(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  AstraVer fork:                                                        *)
(*    Mikhail MANDRYKIN, ISP RAS          (adaptation for Linux sources)  *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Cil
open Visitor

open Common

module Q = Queue
module Queue =
struct
  type 'a t = 'a Q.t
  let create () = Q.create ()
  let add q e = Q.add e q
  let take q = Q.take q
  let is_empty q = Q.is_empty q
end

module Set :
sig
  type 'a t
  val create : (module Datatype.S_with_collections with type t = 'a) -> 'a t
  val add : 'a t -> 'a -> unit
  val mem : 'a t -> 'a -> bool
  val ensure : on_add:('a -> unit) -> 'a t -> 'a -> unit
  val iter : 'a t -> f:('a -> unit) -> unit
end =
struct
  module type H =
  sig
    type t
    type key
    val replace : t -> key -> unit -> unit
    val mem : t -> key -> bool
    val iter : (key -> unit -> unit) -> t -> unit
  end

  module Hide (H : Hashtbl.S) =
  struct
    type t = unit H.t
    type key = H.key
    let create = H.create
    let mem = H.mem
    let replace = H.replace
    let iter = H.iter
  end

  type 'a t = Set : (module H with type key = 'a and type t = 'b) * 'b -> 'a t
  let create (type key) (module S : Datatype.S_with_collections with type t = key) =
    let module H = Hide (S.Hashtbl) in
    Set ((module H), H.create 100)
  let add (type elt) (Set ((module H), t) : elt t) k = H.replace t k ()
  let mem (type elt) (Set ((module H), t) : elt t) k = H.mem t k
  let ensure ~on_add t k =
    if not (mem t k) then begin
      on_add k;
      add t k
    end
  let iter (type elt) (Set ((module H), t) : elt t) ~f = H.iter (fun k () -> f k) t
end

module State =
struct
  type state = {
    types  : typeinfo Set.t;
    comps  : compinfo Set.t; (* Relevant composites for which members matter *)
    fields : fieldinfo Set.t; (* Unused fields are filtered *)
    enums  : enuminfo Set.t;
    vars   : varinfo Set.t;
    fun_queue  : cil_function Queue.t;
    typ_queue  : typeinfo Queue.t;
    comp_queue : compinfo Queue.t
  }
end

module Result =
struct
  type result = {
    types  : typeinfo Set.t;
    comps  : compinfo Set.t;
    fields : fieldinfo Set.t;
    enums  : enuminfo Set.t;
    vars   : varinfo Set.t;
    dcomps : compinfo Set.t (* Dummy composites only used in pointer types of fields *)
  }
end

class relevant_type_visitor
    { State. types; comps; enums; typ_queue; comp_queue } =
  object(self)
    inherit frama_c_inplace

    method! vtype t =
      begin match t with
      | TNamed (ti, _) ->
        Set.ensure types ti ~on_add:(Queue.add typ_queue);
        (* Forcing recursion into the type-info (CIL won't do that). *)
        ignore (self#vtype ti.ttype)
      | TComp (ci, _, _) ->
        Set.ensure comps ci ~on_add:(Queue.add comp_queue)
      | TEnum (ei, _) ->
        Set.add enums ei
      | _ -> ()
      end;
      DoChildren
  end

(* Used for pointer types of fields to add the pointed type to dummies. *)
class dummy_type_visitor { State. enums } dcomps =
  object(self)

    inherit frama_c_inplace

    method! vtype t =
      begin match t with
      | TNamed (ti, _) ->
        (* Forcing recursion into the type-info. *)
        ignore (self#vtype ti.ttype)
      | TComp (ci, _, _) -> Set.add dcomps ci
      | TEnum (ei, _) -> Set.add enums ei
      | _ -> ()
      end;
      DoChildren
  end

let fatal_offset =
  Console.fatal
    "Encountered function type with offset: %a"
    Printer.pp_exp

(* Add the function to the queue for traversal. *)
let do_fun { State. vars; fun_queue } (vi, kf_opt) =
  if not (Set.mem vars vi) then begin
    Set.add vars vi;
    let kf = Option.value ~default:(Globals.Functions.get vi) kf_opt in
    Queue.add fun_queue kf.fundec
  end

let add_var_if_global ~add_from_type ~state vi =
  if vi.vglob && not (isFunctionType vi.vtype) then begin
    add_from_type vi.vtype;
    Set.add state.State.vars vi
  end

let add_field { State. fields } off =
  begin match off with
  | Field (fi, _) ->
    Set.add fields fi
  | Index _ | NoOffset -> ()
  end;
  off

let add_hcast { State.fields } ~typ ~exp =
  let t = typeOf exp in
  if List.for_all isPointerType [typ; t] then begin
    match map_pair typeOf_pointed (typ, t) with
    | TComp (ci1, _, _), TComp (ci2, _, _) ->
      let add_first_field (ci1, ci2) =
        try
          let fi = List.hd ci1.cfields in
          match unrollType fi.ftype with
          | TComp (ci, _, _) when Cil_datatype.Compinfo.equal ci ci2 ->
            Set.add fields fi
          | _ -> ()
        with
        | Failure _ -> ()
      in
      List.iter add_first_field [ci1, ci2; ci2, ci1]
    | _ -> ()
  end

(* Helper function to extract functions occurring as variables
   and mark first structure fields used in hierarchical casts. *)
let do_expr_post ?state ~on_fun ~exclude_fun e =
  if !exclude_fun = Some e.eid then begin
    exclude_fun  := None;
    e
  end else
    match e.enode with
    | Lval (Var vi, NoOffset) | AddrOf (Var vi, NoOffset)
      when isFunctionType vi.vtype ->
      on_fun vi;
      e
    | Lval (Var vi, _) | AddrOf (Var vi, _)
      when isFunctionType vi.vtype ->
      fatal_offset e
    | CastE (typ, _, exp) ->
      Option.iter state ~f:(add_hcast ~typ ~exp);
      e
    | _ -> e

class relevant_function_visitor state ~add_from_type =
  let do_fun = do_fun state in
  (* For marking function expressions in explicit function calls. *)
  let exclude_fun = ref None in
  (* Adds all functions occurring as variables to the queue. *)
  let do_expr_post = do_expr_post ~state ~on_fun:(fun vi -> do_fun (vi, None)) ~exclude_fun in
  let add_var_if_global = add_var_if_global ~add_from_type ~state in
  let do_lval lv = add_from_type (typeOfLval lv); lv in
  let do_offset = add_field state in
  object
    inherit frama_c_inplace

    method! vexpr _ = DoChildrenPost do_expr_post

    method! vterm t = Do.on_term ~post:do_expr_post t

    method! vvrbl vi =
      add_var_if_global vi;
      DoChildren

    method! vinst =
      function
      | Call (_, { eid; enode = Lval (Var vi, NoOffset) }, _, _) ->
        exclude_fun := Some eid;
        do_fun (vi, None);
        DoChildren
      | Call (_, ({ enode = Lval (Var vi, _) } as e), _, _)
        when isFunctionType vi.vtype ->
        fatal_offset e
      | Call (_, f, _, _) ->
        let types =
          match unrollType (typeOf f) with
          | TFun (rt, ao, _, _) | TPtr (TFun (rt, ao, _, _), _) ->
            rt :: (List.map (fun (_, t, _) -> t) (Option.value ~default:[] ao))
          | t ->
            Astraver_options.fatal
              "Non-function (%a) called as function: %a"
              Printer.pp_typ t Printer.pp_exp f
        in
        List.iter do_fun @@
        Globals.Functions.fold
          (fun kf acc ->
             let vi = Kernel_function.get_vi kf in
             if
               vi.vaddrof &&
               let types' =
                 Kernel_function.(
                   get_return_type kf
                   :: List.map (fun vi -> vi.vtype) (get_formals kf))
               in
               List.(length types = length types' &&
                     not @@ exists2 (need_cast ~force:false) types types')
             then (vi, Some kf) :: acc
             else acc)
          [];
        DoChildren
      | _ -> DoChildren

    method! vtype t =
      add_from_type t;
      SkipChildren

    method! vlval _ = DoChildrenPost do_lval

    method! vterm_lval lv = Do.on_term_lval ~post:do_lval lv

    method! voffs _ = DoChildrenPost do_offset

    method! vterm_offset off = Do.on_term_offset ~post:do_offset off
  end

(* Visit all anotation in the file, add necessary types and variables. *)
class annotation_visitor state ~add_from_type =
  let do_fun = do_fun state in
  (* There are no explicit function calls from annotations. *)
  let do_expr_post = do_expr_post ~state ~on_fun:(fun vi -> do_fun (vi, None)) ~exclude_fun:(ref None) in
  let add_var_if_global = add_var_if_global ~add_from_type ~state in
  let rec add_comp_trans ci =
    Set.add state.comps ci;
    List.iter
      (fun fi ->
        Set.add state.fields fi;
        add_ty_trans fi.ftype)
      ci.cfields
  and add_ty_trans ty =
    match unrollType ty with
    | TComp (ci, _, _) -> add_comp_trans ci
    | _                -> ()
  in
  object(self)
    inherit frama_c_inplace

    (* Needed because Frama-C adds logic cunterpart for each local *)
    (* variable declaration. But the types for these varables are added later *)
    (* in the relevant functions visitor. *)
    method! vvdec _ = SkipChildren

    method! vterm t =
    begin match t.term_node with
    | TCastE (ty, _, { term_node = Tunion _; _ })           -> add_ty_trans ty
    | TUpdate (t, _, _)
      when
        Logic_utils.isLogicType (fun _ -> true) t.term_type -> add_ty_trans (Logic_utils.logicCType t.term_type)
    | _                                                     -> ()
    end;
    Do.on_term ~post:do_expr_post t

    method! vmodel_info { mi_base_type } =
      add_from_type mi_base_type;
      DoChildren

    method! vlogic_type t =
      ignore @@ visitFramacLogicType
        (object
          inherit frama_c_inplace

          method! vtype t =
            add_from_type t;
            SkipChildren
        end)
        t;
      DoChildren

    method! vlogic_var_decl =
      function
      | { lv_origin = Some vi } ->
        add_var_if_global vi;
        DoChildren
      | _ -> DoChildren

    method! vlogic_var_use = self#vlogic_var_decl

    method! vterm_lval lv = Do.on_term_lval ~post:(fun lv -> add_from_type (typeOfLval lv); lv) lv

    method! vterm_offset off = Do.on_term_offset ~post:(add_field state) off
  end

class fun_vaddrof_visitor =
  (* To mark function expressions in explicit function calls. *)
  let exclude_fun = ref None in
  let do_expr_post = do_expr_post ~on_fun:(fun vi -> vi.vaddrof <- true) ~exclude_fun in
  object
    inherit frama_c_inplace

    method! vexpr _ = DoChildrenPost (do_expr_post)

    method! vterm t = Do.on_term ~post:do_expr_post t

    method! vstmt_aux s =
      match s.skind with
      | Instr (
        Call (_, ({ eid; enode = Lval (Var { vtype }, NoOffset) }), _, _))
        when isFunctionType vtype ->
        (* Will be handled in the function expression child *)
        exclude_fun := Some eid;
        DoChildren
      | Instr (Call (_, ({ enode = Lval (Var { vtype }, _) } as e), _, _))
        when isFunctionType vtype ->
        fatal_offset e
      | _ -> DoChildren
  end

let get_annotated_funs =
  let emitter = Emitter.end_user in
  let has_user_annots =
    List.exists
      (function
        | { annot_content = AAssert (_, { pred_name = ["missing_return"] }) } -> false
        | _ -> true)
  in
  fun () ->
    Globals.Functions.fold
      (fun kf acc ->
         if Annotations.(
           (try behaviors ~emitter kf <> [] with No_funspec _ -> false) ||
           List.exists Common.(has_user_annots % code_annot ~emitter % fst) @@ code_annot_of_kf kf)
         then kf.fundec :: acc
         else acc)
      []

let collect file =
  let { State.
        types;
        comps;
        fields;
        enums;
        vars;
        fun_queue;
        typ_queue;
        comp_queue
      } as state =
    let open Cil_datatype in
    { State.
      types = Set.create (module Typeinfo);
      comps = Set.create (module Compinfo);
      fields = Set.create (module Fieldinfo);
      enums = Set.create (module Enuminfo);
      vars = Set.create (module Varinfo);
      fun_queue = Queue.create ();
      typ_queue = Queue.create ();
      comp_queue = Queue.create ()
    }
  in
  let dcomps = Set.create (module Cil_datatype.Compinfo) in
  let add_from_type = ignore % visitFramacType (new relevant_type_visitor state) in
  (* For dummy composites *)
  let add_from_type' = ignore % visitFramacType (new dummy_type_visitor state dcomps) in
  let do_type ti = add_from_type ti.ttype in
  let do_comp ci =
    List.iter
      (fun ({ ftype } as fi) ->
        if fi.faddrof || Set.mem fields fi then
          match unrollType ftype with
          | TPtr _ | TArray _ -> add_from_type' ftype
          | _ -> add_from_type ftype)
      ci.cfields
  in
  let do_fun =
    function
    | Definition (f, _) -> ignore @@ visitFramacFunction (new relevant_function_visitor state ~add_from_type) f
    | Declaration (_, vi, vis_opt, _) ->
      List.iter (fun vi -> add_from_type vi.vtype) (vi :: Option.value ~default:[] vis_opt)
  in
  (* Mark all addressed functions in their vaddrof field. *)
  visitFramacFile (new fun_vaddrof_visitor) file;
  (* First add variables and functions occuring in annotations. *)
  visitFramacFile (new annotation_visitor state add_from_type) file;
  (* Now add all annotated functions. *)
  List.iter
    (fun fundec ->
       Set.add vars (Ast_info.Function.get_vi fundec);
       Queue.add fun_queue fundec)
    (get_annotated_funs ());
  while not (Queue.is_empty fun_queue) do
    do_fun (Queue.take fun_queue)
  done;
  (* Also add global ghost variables *)
  Globals.Vars.iter (fun vi _ -> if vi.vghost then add_var_if_global ~add_from_type ~state vi);
  (* This hackish trick was added to avoid an unwanted side-effect of extraction:
     vanishing side-effects. This can happen e.g. with \assigns clauses and assignments when they are used on
     composite types. Since it is possible that no fields of a composite type are used in the relevant code, they can
     all be removed making the containing composite type empty. After expansion of assignments for composite types
     all assignments on such composite types would vanish. To prevent this we
     fill spuriously emptified composites with the first least-nested field of some primitive or array type. *)
  Set.iter comps ~f:(fun { cfields; _ } ->
    let inf = max_int in
    let rec fold_fields_exn ?(nesting=0) fs =
      let rec rank fi =
        let overhead fi = if Set.mem fields fi then 0 else 1 in
        map_fst ((+) @@ 4 * nesting) @@
        match fi.ftype with
        | TEnum _ | TInt _ | TPtr _ | TArray _ | TFun _ -> 0 + overhead fi, [fi]
        | TFloat _ -> 2 + overhead fi, [fi]
        | TNamed (ti, _) -> rank { fi with ftype = ti.ttype }
        | TComp ({ cfields; _ }, _, _) when cfields <> [] ->
          let r, fis = fold_fields_exn ~nesting:(nesting + 1) cfields in
          r + overhead fi, fi :: fis
        | TComp _ | TVoid _ | TBuiltin_va_list _ -> inf, [fi]
      in
      List.(fold_left (fun acc fi -> let r = rank fi in if fst acc > fst r then r else acc) (rank @@ hd fs) @@ tl fs)
    in
    if not (List.exists (fun fi -> fi.faddrof || Set.mem fields fi) cfields) && cfields <> [] then
      let r, fis = fold_fields_exn cfields in
      if r <> inf then
        List.iter (fun fi -> Set.add fields fi; add_from_type fi.ftype) fis);
  (* Now all the relevant fields are added, so we'll use them to omptimize *)
  (* the composites. *)
  begin try while true do
    if not (Queue.is_empty typ_queue) then
      do_type (Queue.take typ_queue)
    else if not (Queue.is_empty comp_queue) then
      do_comp (Queue.take comp_queue)
    else
      raise Exit
    done with Exit -> () end;
  { Result. types; comps; fields; enums; vars; dcomps }

class extractor { Result. types; comps; fields; enums; vars; dcomps } =
  object
    inherit frama_c_inplace

    method! vtype =
      function
      | TArray (t, eo, _, attrs) -> ChangeDoChildrenPost (TArray (t, eo, empty_size_cache (), attrs), Fn.id)
      | TComp (ci, _, attrs) -> ChangeDoChildrenPost (TComp (ci, empty_size_cache (), attrs), Fn.id)
      | _ -> DoChildren

    method! vglob_aux =
      function
      | GType (ti, _) when Set.mem types ti -> SkipChildren
      | GCompTag (ci, _) | GCompTagDecl (ci, _) when Set.mem comps ci ->
        Do.retaining_size_of_composite ci @@ fun ci ->
        Type.Composite.Ci.fill_jessie_fields ci;
        ci.cfields <-
          ListLabels.map ci.cfields
            ~f:(fun fi ->
              if fi.faddrof || Set.mem fields fi then fi
              else
                let fsize_in_bits =
                  Option.value_fatal ~in_:__LOC__ fi.fsize_in_bits +
                  Option.value_fatal ~in_:__LOC__ fi.fpadding_in_bits
                in
                Type.Composite.Ci.padding_field ~fsize_in_bits ci);
        SkipChildren
      | GCompTag (ci, _) | GCompTagDecl (ci, _) when Set.mem dcomps ci ->
        (* The composite is dummy i.e. only used as an abstract type, so *)
        (* its precise contents doesn't matter. *)
        begin match Type.Composite.Ci.size ci with
        | Some fsize_in_bits -> ci.cfields <- [Type.Composite.Ci.padding_field ~fsize_in_bits ci];
        | None -> ()
        end;
        SkipChildren
      | GEnumTag (ei, _) | GEnumTagDecl (ei, _) when Set.mem enums ei ->
        SkipChildren
      | GFun (f, l)
        when
          String.equal (Config.Extract.get ()) "curr_annot" &&
          (Set.mem vars f.svar || f.svar.vghost) &&
          let f = (fst l).pos_path in
          List.for_all
            Filepath.Normalized.(not % equal f % of_string)
            (Kernel.Files.get ()) ->
        f.svar.vdefined <- false;
        ChangeTo [GFunDecl (f.sspec, f.svar, l)]
      | GVarDecl (vi, _) | GVar (vi, _, _) | GFun ( { svar = vi }, _) | GFunDecl (_, vi, _)
        when Set.mem vars vi ->
        SkipChildren
      | GPragma _ -> SkipChildren
      | GText _ -> SkipChildren
      | GAnnot _ -> SkipChildren
      | _ -> ChangeTo []
  end

class local_init_rewriter =
  let cons_set ~loc lv e = List.cons @@ Set (lv, e, loc) in
  let rec fold_init f lv =
    function
    | SingleInit e             -> f lv e
    | CompoundInit (ct, initl) ->(let doinit off init _ = fold_init f (addOffsetLval off lv) init in
                                  fun acc -> foldLeftCompound ~implicit:true ~doinit ~ct ~initl ~acc)
  in
  object
    inherit frama_c_inplace
    method! vinst =
      function
      | Local_init (_,
                    ConsInit (_, _, Constructor),
                    _loc)                           -> Console.fatal "Unsupported C++ constructor call"
      | Local_init (vi,
                    ConsInit (f, args, Plain_func),
                    loc)                            -> ChangeTo [Call (Some (var vi), evar f, args, loc)]
      | Local_init (vi,
                    AssignInit (SingleInit e),
                    loc)                            -> ChangeTo [Set  (var vi, e, loc)]
      | Local_init (vi,
                    AssignInit
                      (CompoundInit _ as init),
                    loc)                            -> ChangeTo (fold_init (cons_set ~loc) (var vi) init [])
      | Call _ | Set _ | Skip _
      | Code_annot _ | Asm _                        -> SkipChildren
  end

let extract file =
  visitFramacFile (new local_init_rewriter) file;
  visitFramacFile (new extractor (collect file)) file;
  (* The following removes some Frama-C builtins from the tables (??) *)
  (*Ast.mark_as_changed ();*)
  Framac.Ast.compute ()
