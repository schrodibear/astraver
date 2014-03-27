(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
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

open Extlib

open Cil_types
open Cil
open Visitor

module Q = Queue
module Queue = struct
  type 'a t = 'a Q.t
  let create () = Q.create ()
  let add q e = Q.add e q
  let take q = Q.take q
  let is_empty q = Q.is_empty q
end

module Set_of_hashtbl (H : Hashtbl.S) = struct
  type t = unit H.t
  let create () = H.create 100
  let add t k = H.replace t k ()
  let mem t k = H.mem t k
end

module T_set = Set_of_hashtbl(Cil_datatype.Typeinfo.Hashtbl)
module C_set = Set_of_hashtbl(Cil_datatype.Compinfo.Hashtbl)
module F_set = Set_of_hashtbl(Cil_datatype.Fieldinfo.Hashtbl)
module E_set = Set_of_hashtbl(Cil_datatype.Enuminfo.Hashtbl)
module V_set = Set_of_hashtbl(Cil_datatype.Varinfo.Hashtbl)

module State = struct
  type state = {
    types  : T_set.t;
    comps  : C_set.t; (* Relevant composites for which members matter *)
    fields : F_set.t; (* Unused fields are filtered *)
    enums  : E_set.t;
    vars   : V_set.t;
    fun_queue  : fundec Queue.t;
    typ_queue  : typeinfo Queue.t;
    comp_queue : compinfo Queue.t
  }
end

module Result = struct
  type result = {
    types  : T_set.t;
    comps  : C_set.t;
    fields : F_set.t;
    enums  : E_set.t;
    vars   : V_set.t;
    dcomps : C_set.t (* Dummy composites only used in pointer types of fields *)
  }
end

class relevant_type_visitor
        { State. types; comps; enums; typ_queue; comp_queue }
= object
  inherit frama_c_inplace

  method! vtype t =
    begin match t with
    | TNamed (ti, _) ->
      if not (T_set.mem types ti) then begin
        T_set.add types ti;
        Queue.add typ_queue ti
      end
    | TComp (ci, _, _) ->
      if not (C_set.mem comps ci) then begin
        C_set.add comps ci;
        Queue.add comp_queue ci
      end
    | TEnum (ei, _) ->
      E_set.add enums ei
    | _ -> ()
    end;
    DoChildren
end

(* Used for pointer types of fields to add the pointed type to dummies. *)
class dummy_type_visitor { State. enums } dcomps = object(self)
  inherit frama_c_inplace

  method! vtype t =
    begin match t with
    | TNamed (ti, _) -> (* Forcing recursion into the type-info. *)
      ignore (visitFramacType (self :> frama_c_visitor) ti.ttype)
    | TComp (ci, _, _) -> C_set.add dcomps ci
    | TEnum (ei, _) -> E_set.add enums ei
    | _ -> ()
    end;
    DoChildren
end

let fatal_offset =
  Jessie_options.fatal
    "Encountered function type with offset: %a"
    Printer.pp_exp

(* Helper function to extract functions occurring as variables. *)
let do_expr_post f do_not_touch e =
  if !do_not_touch = Some e.eid then (do_not_touch := None; e)
  else match e.enode with
  | Lval (Var vi, NoOffset) | AddrOf (Var vi, NoOffset)
    when isFunctionType vi.vtype ->
    f vi;
    e
  | Lval (Var vi, _) | AddrOf (Var vi, _)
    when isFunctionType vi.vtype ->
    fatal_offset e
  | _ -> e

(* Add the function to the queue for traversal. *)
let do_fun { State. vars; fun_queue } add_from_type (vi, kf_opt) =
  if not (V_set.mem vars vi) then begin
    V_set.add vars vi;
    let kf = opt_conv (Globals.Functions.get vi) kf_opt in
    Kernel_function.(
     try Queue.add fun_queue (get_definition kf)
     with No_Definition ->
       List.iter (fun vi -> add_from_type vi.vtype) (get_formals kf))
  end

let add_var_if_global add_from_type state vi =
  if vi.vglob then begin
    add_from_type vi.vtype;
    V_set.add state.State.vars vi
  end

let add_field { State. fields } off =
  begin match off with
  | Field (fi, _) ->
    F_set.add fields fi
  | Index _ | NoOffset -> ()
  end;
  off

class relevant_function_visitor state add_from_type =
  let do_fun = do_fun state add_from_type in
  (* For marking function expressions in explicit function calls. *)
  let do_not_touch = ref None in
  (* Adds all functions occurring as variables to the queue. *)
  let do_expr_post = do_expr_post (fun vi -> do_fun (vi, None)) do_not_touch in
  let add_var_if_global = add_var_if_global add_from_type state in
  let do_lval lv = add_from_type (typeOfLval lv); lv in
  let do_offset = add_field state in
object
  inherit frama_c_inplace

  method! vexpr _ = DoChildrenPost do_expr_post

  method! vterm = Common.do_on_term (None, Some do_expr_post)

  method! vvrbl vi =
    add_var_if_global vi;
    DoChildren

  method! vinst =
    function
    | Call (_, { eid; enode = Lval (Var vi, NoOffset) }, _, _) ->
      do_not_touch := Some eid;
      do_fun (vi, None);
      DoChildren
    | Call (_, ({ enode = Lval (Var vi, _) } as e), _, _)
      when isFunctionType vi.vtype ->
      fatal_offset e
    | Call (_, f, _, _) -> 
      let types =
        match unrollType (typeOf f) with
        | TFun (rt, ao, _, _) | TPtr (TFun (rt, ao, _, _), _) ->
          rt :: (List.map (fun (_, t, _) -> t) (opt_conv [] ao))
        | t ->
          Jessie_options.fatal
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
                    not @@ exists2 need_cast types types')
            then (vi, Some kf) :: acc
            else acc)
          [];
      DoChildren
    | _ -> DoChildren

  method! vtype t =
    add_from_type t;
    SkipChildren

  method! vlval _ = DoChildrenPost do_lval

  method! vterm_lval = Common.do_on_term_lval (None, Some do_lval)

  method! voffs _ = DoChildrenPost do_offset

  method! vterm_offset = Common.do_on_term_offset (None, Some do_offset)
end

(* Visit all anotation in the file, add necessary types and variables. *)
class annotation_visitor state add_from_type =
  let do_fun = do_fun state add_from_type in
  (* There are no explicit function calls from annotations. *)
  let do_expr_post = do_expr_post (fun vi -> do_fun (vi, None)) (ref None) in
  let add_var_if_global = add_var_if_global add_from_type state in
object(self)
  inherit frama_c_inplace

  (* Needed because Frama-C adds logic cunterpart for each local *)
  (* variable declaration. But the types for these varables are added later *)
  (* in the relevant functions visitor. *)
  method! vvdec _ = SkipChildren

  method! vterm = Common.do_on_term (None, Some do_expr_post)

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

  method! vterm_lval =
    Common.do_on_term_lval
      (None, Some (fun lv -> add_from_type (typeOfLval lv); lv))

  method! vterm_offset =
    Common.do_on_term_offset (None, Some (add_field state))
end

class fun_vaddrof_visitor =
  (* To mark function expressions in explicit function calls. *)
  let do_not_touch = ref None in
  let do_expr_post = do_expr_post (fun vi -> vi.vaddrof <- true) do_not_touch in
object
  inherit frama_c_inplace

  method! vexpr _ = DoChildrenPost (do_expr_post)

  method! vterm = Common.do_on_term (None, Some do_expr_post)

  method! vstmt_aux s =
    match s.skind with
    | Instr (
        Call (_, ({ eid; enode = Lval (Var { vtype }, NoOffset) }), _, _))
      when isFunctionType vtype ->
      (* Will be handled in the function expression child *)
      do_not_touch := Some eid;
      DoChildren
    | Instr (Call (_, ({ enode = Lval (Var { vtype }, _) } as e), _, _))
      when isFunctionType vtype ->
      fatal_offset e
    | _ -> DoChildren
end

let get_annotated_funs () =
  Globals.Functions.fold
    (fun kf acc ->
      if Annotations.(
           not (is_empty_funspec (funspec kf)) ||
           code_annot_of_kf kf <> [])
      then
        Kernel_function.(try get_definition kf :: acc
                         with No_Definition -> acc)
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
        comp_queue } as state =
      { State.
        types = T_set.create ();
        comps = C_set.create ();
        fields = F_set.create ();
        enums = E_set.create ();
        vars = V_set.create ();
        fun_queue = Queue.create ();
        typ_queue = Queue.create ();
        comp_queue = Queue.create () }
  in
  let dcomps = C_set.create () in
  let add_from_type t =
    ignore
      (visitFramacType (new relevant_type_visitor state) t)
  in
  (* For dummy composites *)
  let add_from_type' t =
    ignore
      (visitFramacType (new dummy_type_visitor state dcomps) t)
  in
  let do_type ti = add_from_type ti.ttype in
  let do_comp ci =
    List.iter
      (fun ({ ftype } as fi) ->
        if F_set.mem fields fi then
          match unrollType ftype with
          | TPtr _ | TArray _ -> add_from_type' ftype
          | _ -> add_from_type ftype)
      ci.cfields
  in
  let do_fun f =
    ignore @@
      visitFramacFunction (new relevant_function_visitor state add_from_type) f
  in
  (* Mark all addressed functions in their vaddrof field. *)
  visitFramacFile (new fun_vaddrof_visitor) file;
  (* First add variables and functions occuring in annotations. *)
  visitFramacFile (new annotation_visitor state add_from_type) file;
  (* Now add all annotated functions. *)
  List.iter
    (fun fundec ->
       V_set.add vars fundec.svar;
       Queue.add fun_queue fundec)
    (get_annotated_funs ());
  while not (Queue.is_empty fun_queue) do
    do_fun (Queue.take fun_queue)
  done;
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

let dummy_field ci =
  { fcomp = ci;
    forig_name = "";
    fname = "dummy";
    ftype = intType;
    fbitfield = None;
    fattr = [Attr ("const", [])];
    floc = Cil_datatype.Location.unknown;
    faddrof = false;
    fsize_in_bits = None;
    foffset_in_bits = None;
    fpadding_in_bits = None }

class extractor { Result. types; comps; fields; enums; vars; dcomps } = object
  inherit frama_c_inplace

  method! vtype =
    function
    | TArray (t, eo, _, attrs) -> ChangeDoChildrenPost (TArray (t, eo, empty_size_cache (), attrs), id)
    | TComp (ci, _, attrs) -> ChangeDoChildrenPost (TComp (ci, empty_size_cache (), attrs), id)
    | _ -> DoChildren

  method! vglob_aux =
    let dummy_if_empty ci =
      function
      | [] -> [dummy_field ci]
      | l -> l
    in
    function
    | GType (ti, _) when T_set.mem types ti -> SkipChildren
    | GCompTag (ci, _) | GCompTagDecl (ci, _) when C_set.mem comps ci ->
      ci.cfields <- dummy_if_empty ci (List.filter (fun fi -> fi.faddrof || F_set.mem fields fi) ci.cfields);
      ListLabels.iter ci.cfields
        ~f:(fun fi ->
             fi.fsize_in_bits <- None;
             fi.foffset_in_bits <- None;
             fi.fpadding_in_bits <- None);
      SkipChildren
    | GCompTag (ci, _) | GCompTagDecl (ci, _) when C_set.mem dcomps ci ->
      (* The composite is dummy i.e. only used as an abstract type, so *)
      (* its precise contents isn't matter. *)
      ci.cfields <- dummy_if_empty ci [];
      SkipChildren
    | GEnumTag (ei, _) | GEnumTagDecl (ei, _) when E_set.mem enums ei ->
      SkipChildren
    | GVarDecl (_, vi, _) | GVar (vi, _, _) | GFun ( { svar = vi }, _)
      when V_set.mem vars vi ->
      SkipChildren
    | GPragma _ -> SkipChildren
    | GText _ -> SkipChildren
    | GAnnot _ -> SkipChildren
    | _ -> ChangeTo []
end

let extract file =
  visitFramacFile (new extractor (collect file)) file;
  (* The following removes some Frama-C builtins from the tables (??) *)
  (*Ast.mark_as_changed ();*)
  Ast.compute ()

