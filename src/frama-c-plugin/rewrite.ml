(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  Jessie2 fork:                                                         *)
(*    Mikhail MANDRYKIN, ISP RAS                                          *)
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

(* Import from Cil *)
open Cil_types
open Cil
open Cil_datatype
open Ast_info
open Visitor

(* Utility functions *)
open Common

(*****************************************************************************)
(* Adds a default behavior for all functions                                 *)
(*****************************************************************************)

let add_default_behaviors () =
  Globals.Functions.iter @@
    fun kf ->
      if not (List.exists is_default_behavior @@ Annotations.behaviors kf) then begin
        Annotations.add_behaviors Emitters.jessie kf [mk_behavior ()];
        (* ensures that default behavior will be correctly populated *)
        ignore (Annotations.behaviors kf)
      end

(*****************************************************************************)
(* Rename entities to avoid conflicts with Jessie predefined names.          *)
(*****************************************************************************)

class renaming_visitor add_variable add_logic_variable =
  let add_ci =
    let module H = Compinfo.Hashtbl in
    let cis = H.create 17 in
    fun ci ->
    if not (H.mem cis ci)
    then begin
      ci.cname <- Name.unique ~force:true ci.cname;
      List.iter (fun fi -> fi.fname <- Name.unique ~force:true fi.fname) ci.cfields;
      H.add cis ci ()
    end
  in
  let add_li (type key) (module H : Hashtbl.S with type key = key) ~upd =
    let old_lis = H.create 17 in
    let new_lis = H.create 17 in
    fun li ->
      try
        if H.mem old_lis li then
          DoChildren
        else
          ChangeDoChildrenPost (H.find new_lis li, Fn.id)
      with
      | Not_found ->
        let li' = upd li in
        H.add new_lis li li';
        H.add old_lis li' li;
        ChangeDoChildrenPost (li', Fn.id)
  in
  let add_ti =
    add_li
      (module Logic_type_info.Hashtbl)
      ~upd:(fun ti -> { ti with lt_name = Name.unique ~force:true ti.lt_name })
  in
  let add_lci =
    add_li
      (module Logic_ctor_info.Hashtbl)
      ~upd:(fun lci -> { lci with ctor_name = Name.unique ~force:true lci.ctor_name })
  in
  object(self)
    inherit frama_c_inplace

    method! vfunc f =
      List.iter add_variable f.slocals;
      DoChildren

    method! vglob_aux =
      function
      | GCompTag (ci, _loc)
      | GCompTagDecl(ci, _loc) ->
        add_ci ci;
        SkipChildren
      | GVarDecl _ | GVar _ | GFun _ | GAnnot _ | GType _
      | GEnumTagDecl _ | GEnumTag _ | GAsm _ | GPragma _ | GText _ ->
        DoChildren

    method! vlogic_var_decl lv = add_logic_variable lv; DoChildren

    method! vlogic_var_use v =
      let postaction v =
        (* Restore consistency between C variable name and logical name *)
        Option.iter v.lv_origin ~f:(fun cv -> v.lv_name <- cv.vname);
        v
      in
      ChangeDoChildrenPost (v, postaction)

    method! vlogic_type_info_decl = add_ti
    method! vlogic_type_info_use = add_ti

    method! vlogic_type_def =
      function
      | LTsum _ -> DoChildren
      | LTsyn lt ->
        ChangeDoChildrenPost (LTsyn (visitFramacLogicType (self :> frama_c_visitor) lt), Fn.id)

    method! vlogic_ctor_info_decl = add_lci
    method! vlogic_ctor_info_use = add_lci
  end

let logic_names_overloading = Hashtbl.create 257

let rename_entities file =
  let add_variable v =
    let s = Name.unique v.vname in
    v.vname <- s;
    match v.vlogic_var_assoc with
    | None -> ()
    | Some lv -> lv.lv_name <- v.vname
  in
  let add_logic_variable v =
    match v.lv_origin with
    | None -> (* pure logic variable *)
      v.lv_name <- Name.Logic.unique v.lv_name
    | Some _ -> () (* we take care of that in the C world *)
  in
  Globals.Vars.iter (fun v _init -> add_variable v);
  Globals.Functions.iter
    (fun kf ->
       let vi, params = Globals.Functions.(get_vi kf, get_params kf) in
       add_variable vi;
       List.iter add_variable params;
       let rt, params', is_va, attrs = splitFunctionTypeVI vi in
       let params' =
         Option.map
           (List.map2 (fun vi (_, _, attrs) -> vi.vname, vi.vtype, addAttributes attrs vi.vattr) params)
           params'
       in
       vi.vtype <- TFun (rt, params', is_va, attrs));
  (* preprocess of renaming logic functions  *)
  Logic_env.Logic_info.iter
    (fun name _li ->
       try
         let x = Hashtbl.find logic_names_overloading name in
         x := true
       with
       | Not_found ->
         Hashtbl.add logic_names_overloading name (ref false));
  visitFramacFile (new renaming_visitor add_variable add_logic_variable) file


(*****************************************************************************)
(* Replace addrof array with startof.                                        *)
(*****************************************************************************)

class array_addrof_to_startof_visitor =
  object
    inherit frama_c_inplace

    method! vexpr e =
      match e.enode with
      | AddrOf lv when isArrayType (typeOfLval lv) ->
        ChangeDoChildrenPost (new_exp ~loc:e.eloc (StartOf lv), fun x -> x)
      | _ -> DoChildren

    method! vterm t =
      match t.term_node with
      | TAddrOf tlv ->
        begin match Type.Logic_c_type.of_logic_type t.term_type with
        | Some lct ->
          let ty = Type.Logic_c_type.map ~f:pointed_type lct in
          if isArrayType ty then
            ChangeDoChildrenPost (
              {
                t with
                term_node = TStartOf tlv;
                term_type = Ctype (element_type ty);
              },
              Fn.id)
          else
            DoChildren
        | _ -> DoChildren
        end
      | _ -> DoChildren
  end

let replace_addrof_array file =
  visitFramacFile (new array_addrof_to_startof_visitor) file

(*****************************************************************************)
(* Replace string constants by global variables.                             *)
(*****************************************************************************)

(* WARNING: C99 doesn't specify whether string literals with the same contents (values) should be merged *)
(*          (i.e. stored within the same char array).                                                    *)
(*          Therefore such optimizations must NOT be implemented.                                        *)
class string_constants_visitor ~attach =

  let (memo_string, find_strings), (memo_wstring, find_wstrings) =
    let module ScopeMap =
      Map.Make
        (struct
          type t = fundec option
          let compare = Option.compare ~cmp:Fundec.compare
         end)
    in
    let memo_find (type a) (type b) (module Trie : Trie.S with type key = a) (explode : b -> a list) =
      let strings = ref Trie.empty in
      let memo_string s scope loc vi =
        let path = explode s in
        let scope_map = try Trie.find_exn !strings path with Not_found -> ScopeMap.empty in
        strings :=
          Trie.add
            !strings
            path
            ScopeMap.(add scope ((loc, vi)::try find scope scope_map with Not_found -> []) scope_map)
      in
      let find_strings ?scope prefix =
        Trie.find_all !strings (explode prefix) |>
        (match scope with
          | Some scope -> List.map (fun map -> try ScopeMap.find scope map with Not_found -> [])
          | None -> List.(flatten % map (map snd % ScopeMap.bindings)))
        |>
        List.flatten |>
        List.sort (fun (l1, _) (l2, _) -> Location.compare l1 l2) |>
        List.map snd
      in
      memo_string, find_strings
    in
    memo_find (module StringTrie) String.explode, memo_find (module Int64Trie) Fn.id
  in

  (* Functions to build and attach an invariant for each string constant. The actual invariant generation is
   * postponed until finding the corresponding proxy with the __invariant attribute.
   *)
  let content_inv ~loc s lv =
    let content =
      match s with
      | `String s -> List.map (Logic_const.tinteger ~loc % int_of_char) (String.explode s @ ['\000'])
      | `Wstring ws -> List.map (Logic_const.tint ~loc % Integer.of_int64) (ws @ [0x0L])
    in
    Logic_const.(
      pands @@
        ListLabels.mapi content
          ~f:(fun i c ->
            let lval =
              match lv.lv_type with
              | Ctype (TArray _) -> TVar lv, TIndex (tinteger ~loc i, TNoOffset)
              | Ctype (TPtr _) as lt ->
                TMem (term ~loc (TBinOp (PlusPI, tvar ~loc lv, tinteger ~loc i)) lt), TNoOffset
              | _ -> Console.fatal "Wrong type of string literal proxy %a" Printer.pp_logic_var lv
            in
            let el = term ~loc (TLval lval) (Ctype charType) in
            prel ~loc (Req, el, c)))
  in
  let attach_invariant name loc p =
    let globinv = Cil_const.make_logic_info (Name.Logic.unique name) in
    globinv.l_labels <- [LogicLabel (None, "Here")];
    globinv.l_body <- LBpred p;
    attach#globaction (fun () -> Logic_utils.add_logic_function globinv);
    attach#global (GAnnot (Dinvariant (globinv, loc), loc))
  in

  (* Use the Cil translation on initializers. First translate to primitive
   * AST to later apply translation in [blockInitializer].
   *)
  let string_cabs_init expr_loc =
    let open Cabs in
    function
    | `String s -> SINGLE_INIT { expr_node = CONSTANT (CONST_STRING (s, None)); expr_loc }
    | `Wstring ws -> SINGLE_INIT { expr_node = CONSTANT (CONST_WSTRING (ws, None)); expr_loc }
  in

  (* Name of variable should be as close as possible to the string it
   * represents. To that end, we just filter out characters not allowed
   * in C names, before we add a discriminating number if necessary.
   *)
  let string_var s fundec_opt loc =
    let name =
      match s with
      | `String s -> Name.unique ("__string_" ^ String.filter_alphanumeric ~assoc:[] ~default:'_' s)
      | `Wstring _ -> Name.unique "__wstring_"
    in
    let vi =
      makeGlobalVar name (array_type (match s with `String _ -> charType | `Wstring _ -> theMachine.wcharType))
    in
    let attach_invariants ?(content=false) vi' =
      let tv' = Ast.Term.of_var vi' in
      attach_invariant ("proxy_" ^ vi'.vname ^ "_for_" ^ vi.vname) vi'.vdecl @@
        Logic_const.prel ~loc:vi'.vdecl (Req, tv', Ast.Term.of_var vi);
      if content then
        (* Define an invariant on the contents of the string *)
        let content_inv = content_inv ~loc s @@ cvar_to_lvar vi' in
        attach_invariant ("contents_of_" ^ vi.vname) vi.vdecl content_inv
    in
    (match s with `String s -> memo_string s | `Wstring ws -> memo_wstring ws)
      fundec_opt
      loc
      (Some vi, attach_invariants);
    vi
  in

  let make_glob fundec_opt loc s =
    let v = string_var s fundec_opt loc in
    let inite = string_cabs_init loc s in
    let size = match s with `String s -> String.length s | `Wstring ws -> List.length ws - 1 in
    (* Apply translation from initializer in primitive AST to block of code,
     * simple initializer and type.
     *)
    let _b,init,ty =
      Cabs2cil.blockInitializer Cabs2cil.empty_local_env v inite
    in
    (* Precise the array type *)
    v.vtype <- typeAddAttributes [Attr ("const", [])] ty;

    (* Attach global variable and code for global initialization *)

(* DISABLED because does not work and uses deprecated Cil.getGlobInit
   See bts0284.c
    List.iter attach_globinit b.bstmts;
*)
    attach#global (GVar (v, {init=Some init}, CurrentLoc.get ()));

    (* Define a global string invariant *)
    begin try
    let validstring =
      match
        Logic_env.find_all_logic_functions
          (match s with
           | `Wstring _ -> Name.Predicate.valid_wstring
           | `String _ -> Name.Predicate.valid_string)
      with
        | [i] -> i
        | _  -> raise Exit
    in
    let strlen =
      match Logic_env.find_all_logic_functions Name.Logic_function.strlen
      with
        | [i] -> i
        | _  -> raise Exit
    in
    let strlen_type =
      match strlen.l_type with Some t -> t | None -> assert false
    in
    let wcslen =
      match Logic_env.find_all_logic_functions Name.Logic_function.wcslen
      with
        | [i] -> i
        | _  -> raise Exit
    in
    let wcslen_type =
      match wcslen.l_type with Some t -> t | None -> assert false
    in
    let pstring =
      Papp (validstring, [], [variable_term v.vdecl (cvar_to_lvar v)])
    in
    let tv = Ast.Term.of_var v in
    let strsize =
      match s with
      | `Wstring _ -> Ast.Term.mk ~typ:wcslen_type ~loc:v.vdecl @@ Tapp (wcslen, [], [tv])
      | `String _ -> Ast.Term.mk ~typ:strlen_type ~loc:v.vdecl @@ Tapp (strlen, [], [tv])
    in
    let size = constant_term v.vdecl (Integer.of_int size) in
    let psize = Prel (Req, strsize, size) in
    let p = Pand (Ast.Named.mk ~loc:v.vdecl pstring, Ast.Named.mk ~loc:v.vdecl psize) in

    attach_invariant ("validity_of_" ^ v.vname) v.vdecl (Ast.Named.mk ~loc:v.vdecl p);
    with Exit -> ()
    end;
    v
  in
  object(self)

    inherit frama_c_inplace

    method find_strings = find_strings

    method find_wstrings = find_wstrings

    method literal_attr_name = "literal"

    method is_literal_proxy vi =
      vi.vghost && vi.vglob && (vi.vstorage = Static || vi.vstorage = NoStorage) &&
      (isCharPtrType vi.vtype ||
       isPointerType vi.vtype && not (need_cast (pointed_type vi.vtype) theMachine.wcharType)) &&
      hasAttribute "const" (typeAttr vi.vtype) &&
      hasAttribute "const" (typeAttr @@ pointed_type vi.vtype) &&
      hasAttribute self#literal_attr_name vi.vattr

    method! vinit vi _ _ =
      if self#is_literal_proxy vi then
        SkipChildren
      else
        DoChildren

    method! vexpr e = match e.enode with
      | Const(CStr s) ->
        let v = make_glob self#current_func e.eloc (`String s) in
        ChangeTo (new_exp ~loc:e.eloc (StartOf(Var v, NoOffset)))
      | Const(CWStr ws) ->
        let v = make_glob self#current_func e.eloc (`Wstring ws) in
        ChangeTo (new_exp ~loc:e.eloc (StartOf(Var v, NoOffset)))
      | _ -> DoChildren

    method! vglob_aux = function
      | GVar (v, { init = Some (SingleInit {enode = Const _}) }, _) ->
        if isArrayType v.vtype then
          (* Avoid creating an array for holding the initializer for another
           * array. This initializer is later cut into individual
           * initialization statements in [gather_initialization].
          *)
          SkipChildren
        else
          DoChildren
      | GVar (_, { init = Some (CompoundInit (TArray (_, _, _, _), lst)) }, loc) ->
        let content =
          ListLabels.mapi lst
            ~f:(fun i pair ->
              match pair with
              | Index ({ enode = Const (CInt64 (i', _, _)) }, NoOffset),
                SingleInit ({ enode = Const (CChr _ | CInt64 _ as c)
                                    | CastE (_, _, { enode = Const (CChr _ | CInt64 _ as c) }) } as e)
                when i = Integer.to_int i' ->
                let c =
                  match c with
                  | CInt64 (c, _, _) when isCharType (typeOf e) -> CChr (Char.chr @@ Integer.to_int c)
                  | _ -> c
                in
                Some c
              | _ -> None)
        in
        let content = List.take (List.length content - 1) content in
        (try
           let s =
             match List.hd content with
             | Some (CChr _) ->
               `String (String.implode @@ List.map (function Some (CChr c) -> c | _ -> raise @@ Failure "s") content)
             | Some (CInt64 _) ->
               `Wstring
                 (ListLabels.map content
                    ~f:(function Some (CInt64 (i, _, _)) -> Integer.to_int64 i | _ -> raise @@ Failure "s"))
             | _ -> raise @@ Failure "s"
           in
           let attach_invariants ?(content=false) vi' =
             if content then
               attach_invariant
                 ("contents_of_" ^ vi'.vname)
                 vi'.vdecl @@
               content_inv ~loc s @@
               cvar_to_lvar vi'
           in
           (match s with `String s -> memo_string s | `Wstring ws -> memo_wstring ws)
             self#current_func
             loc
             (None, attach_invariants);
           DoChildren
         with
         | Failure "hd" | Failure "s" -> DoChildren)
      | _ -> DoChildren

end

class literal_proxy_visitor (first_pass_visitor : string_constants_visitor) =
  object

    inherit frama_c_inplace

    method! vinit vi off init =
      if first_pass_visitor#is_literal_proxy vi then
        let attrparams = findAttribute first_pass_visitor#literal_attr_name vi.vattr in
        let s, scope, idx =
          match off, init with
          | NoOffset,
            SingleInit { enode = Const const | CastE (_, _, { enode = Const const }) } ->
            let s =
              match const with
              | CStr s ->
                let s =
                  if Str.last_chars s 3 = "..." then
                    Str.first_chars s (String.length s - 3)
                  else s
                in
                `String s
              | CWStr ws ->
                let ws =
                  if List.take 3 (List.rev ws) = [0x2EL; 0x2EL; 0x2EL] then
                    List.(rev @@ drop 3 @@ rev ws)
                  else ws
                in
                `Wstring ws
              | _ -> Console.fatal "Unrecognized literal proxy initializer: %a" Printer.pp_constant const
            in
            let conv_int i = Some (Integer.to_int i) in
            (match attrparams with
             | [AInt i] -> s, Some None, conv_int i
             | ACons (f, []) :: aps ->
               (try
                  s,
                  Some (Some (Kernel_function.get_definition @@ Globals.Functions.find_by_name f)),
                  (match aps with
                   | [AInt i] -> conv_int i
                   | [] -> None
                   | _ -> Console.fatal "Invalid argument in proxy literal attribute: %a" Printer.pp_attributes vi.vattr)
                with
                | Not_found | Kernel_function.No_Definition ->
                  Console.fatal
                    "Invalid function name %s in literal proxy specification: %a" f Printer.pp_attributes vi.vattr)
             | [] -> s, None, None
             | _ -> Console.fatal "Invalid literal proxy attribute specification: %a" Printer.pp_attributes vi.vattr)
          | _ -> Console.fatal "Unrecognized literal proxy specification for variable %a" Printer.pp_varinfo vi
        in
        let vis =
          match s with
          | `String s -> first_pass_visitor#find_strings ?scope s
          | `Wstring ws -> first_pass_visitor#find_wstrings ?scope ws
        in
        let vis =
          Option.fold
            idx
            ~init:vis
            ~f:(fun vis i ->
              try
                [List.nth vis i]
              with
              | Failure "nth"
              | Invalid_argument "List.nth" ->
                Console.fatal "Invalid string literal index: %a" Printer.pp_attributes vi.vattr)
        in
        match vis with
        | [vi'_opt, attach_invs] ->
          attach_invs ~content:(hasAttribute "invariant" vi.vattr) vi;
          (match vi'_opt with
           | Some vi' -> ChangeTo (SingleInit (mkAddrOfVi vi'))
           | None -> (Globals.Vars.find vi).init <- None; SkipChildren)
        | [] -> Console.fatal "No matching literals found for proxy specification (variable %a)" Printer.pp_varinfo vi
        | _ -> Console.fatal "Ambiguous literal proxy specification for variable %a" Printer.pp_varinfo vi
      else
        SkipChildren
  end

let replace_string_constants =
  Do.attaching_globs
    {
      Do.perform =
        fun ~attach file ->
          let first_pass_visitor = new string_constants_visitor attach in
          visitFramacFile (first_pass_visitor :> frama_c_visitor) file;
          visitFramacFile (new literal_proxy_visitor first_pass_visitor) file
    }

(*****************************************************************************)
(* Invariant for global constants                                            *)
(*****************************************************************************)

class global_const_handler ~attach =
  object
    inherit frama_c_inplace

    method! vglob_aux =
      function
      | GVar (v, { init = Some (SingleInit e) }, _) as g
        when typeHasAttribute "const" v.vtype && Option.is_some @@ possible_value_of_integral_expr e ->
        let globinv = Cil_const.make_logic_info (Name.Logic.unique ("__value_of_" ^ v.vname)) in
        globinv.l_labels <- [LogicLabel (None, "Here")];
        globinv.l_body <- LBpred (
          let loc = v.vdecl in
          Logic_const.(prel ~loc (Req, tvar ~loc @@ cvar_to_lvar v, tint ~loc @@ value_of_integral_expr e)));
        attach#globaction (fun () -> Logic_utils.add_logic_function globinv);
        ChangeTo ([g; GAnnot (Dinvariant (globinv, v.vdecl), v.vdecl)])
      | _ -> SkipChildren
  end

let handle_global_consts = Visit.(attaching_globs { mk = new global_const_handler })[@warning "-42"]

(*****************************************************************************)
(* Put all global initializations in the [globinit] file.                    *)
(* Replace global compound initializations by equivalent statements.         *)
(*****************************************************************************)

let gather_initialization _ =
  Globals.Vars.iter
    (fun _v iinfo ->
       (* Too big currently, postpone until useful *)
       iinfo.init <- None)

class copy_spec_specialize_memset =
  object(self)
    inherit frama_c_copy (Project.current())
    method private has_changed lv =
      (get_original_logic_var self#behavior lv) != lv

    method! vlogic_var_use lv =
      if self#has_changed lv then
        DoChildren (* Already visited *)
      else
        begin match lv.lv_origin with
        | Some v when not v.vglob -> (* Don't change global references *)
          let v' = Cil_const.copy_with_new_vid v in
          v'.vformal <- true;
          begin match unrollType v.vtype with
           | TArray _ as t -> v'.vtype <- TPtr (t, [])
           | _ -> ()
          end;
          v'.vlogic_var_assoc <- None; (* reset association. *)
          let lv' = cvar_to_lvar v' in
          set_logic_var self#behavior lv lv';
          set_orig_logic_var self#behavior lv' lv;
          set_varinfo self#behavior v v';
          set_orig_varinfo self#behavior v' v;
          ChangeTo lv'
        | Some _
        | None -> DoChildren
        end

    method! vterm t =
      let post_action t =
        let loc = t.term_loc in
        match t.term_node with
        | TStartOf (TVar lv, TNoOffset) ->
          if self#has_changed lv then begin
            (* Original was an array, and is now a pointer to an array.
               Update term accordingly *)
            let base = Logic_const.tvar ~loc lv in
            let tmem = (TMem base,TNoOffset) in
            Logic_const.term ~loc (TStartOf tmem) (typeOfTermLval tmem)
          end else
            t
        | TLval (TVar lv, (TIndex _ as idx)) ->
          if self#has_changed lv then begin
            (* Change array access into pointer shift. *)
            let base = Logic_const.tvar ~loc lv in
            let tmem = TMem base, idx in
            Logic_const.term ~loc (TLval tmem) t.term_type
          end else
            t
      | _ -> t
      in
      ChangeDoChildrenPost (t, post_action)

    method! vspec s =
      let refresh_deps =
        function
        | FromAny -> FromAny
        | From locs -> From (List.map Logic_const.refresh_identified_term locs)
      in
      let refresh_froms (loc, deps) =
        (Logic_const.refresh_identified_term loc, refresh_deps deps)
      in
      let refresh_assigns =
        function
        | WritesAny -> WritesAny
        | Writes (writes) -> Writes (List.map refresh_froms writes)
      in
      let refresh_allocates =
        function
        | FreeAllocAny -> FreeAllocAny
        | FreeAlloc (free,alloc) ->
          FreeAlloc (List.map Logic_const.refresh_identified_term free,
                     List.map Logic_const.refresh_identified_term alloc)
      in
      let refresh_extended e =
        List.map (fun (s,i,p) -> (s,i,List.map Logic_const.refresh_predicate p)) e
      in
      let refresh_behavior b =
        let requires = List.map Logic_const.refresh_predicate b.b_requires in
        let assumes = List.map Logic_const.refresh_predicate b.b_assumes in
        let post_cond =
          List.map
            (fun (k, p) -> (k, Logic_const.refresh_predicate p)) b.b_post_cond
        in
        let assigns = refresh_assigns b.b_assigns in
        let allocation = Some (refresh_allocates b.b_allocation) in
        let extended = refresh_extended b.b_extended in
        mk_behavior ~assumes ~requires ~post_cond ~assigns ~allocation ~extended ()
      in
      let refresh s =
        let bhvs = List.map refresh_behavior s.spec_behavior in
        s.spec_behavior <- bhvs;
        s
      in
      ChangeDoChildrenPost (s, refresh)
  end

let copy_spec_specialize_memset s =
  let vis = new copy_spec_specialize_memset in
  let s' = visitFramacFunspec vis s in
  let args = fold_visitor_varinfo vis#behavior (fun oldv newv acc -> (oldv,newv)::acc) [] in
  args, s'

class specialize_memset =
  object
    inherit frama_c_inplace
    val mutable my_globals = []
    method! vstmt_aux s =
      match Annotations.code_annot ~filter:Logic_utils.is_contract s with
      | [annot] ->
        (match annot.annot_content with
         | AStmtSpec
             (_, ({ spec_behavior = [{ b_name = "Frama_C_implicit_init" }]} as spec)) ->
           let loc = Stmt.loc s in
           let mk_actual v =
             match unrollType v.vtype with
             | TArray _ ->
               new_exp ~loc (StartOf (var v))
             | _ -> evar ~loc v
           in
           let prms, spec = copy_spec_specialize_memset spec in
           let (actuals, formals) = List.split prms in
           let actuals = List.map mk_actual actuals in
           let arg_type = List.map (fun v -> v.vname, v.vtype, []) formals in
           let f =
             makeGlobalVar
               (Name.unique "implicit_init")
               (TFun (TVoid [], Some arg_type, false, []))
           in
           unsafeSetFormalsDecl f formals;
           my_globals <- GVarDecl(empty_funspec (), f, loc) :: my_globals;
           Globals.Functions.replace_by_declaration spec f loc;
           let kf = Globals.Functions.get f in
           Annotations.register_funspec ~emitter:Emitters.jessie kf;
           let my_instr = Call (None, evar ~loc f, actuals, loc) in
           s.skind <- Instr my_instr;
           SkipChildren
         | _ -> DoChildren)
      | _ -> DoChildren

  method! vglob_aux _ =
    let add_specialized g =
      let s = my_globals in
      my_globals <- [];
      s @ g
    in
    DoChildrenPost add_specialized
end

let specialize_memset file =
  visitFramacFile (new specialize_memset) file;
  (* We may have introduced new globals: clear the last_decl table. *)
  Framac.Ast.clear_last_decl ()

(*****************************************************************************)
(* Specification and specialization for memcpy and other block functions.    *)
(*****************************************************************************)

(*****************************************************************************)
(* Support for kzalloc as kmalloc+memset                                     *)
(*****************************************************************************)

class kzalloc_expanding_visitor =
  object
    inherit frama_c_inplace

    method! vstmt stmt =
      match stmt.skind with
      | Instr (Call (Some lv as lv_opt, { enode = Lval (Var fv, NoOffset); eloc }, ([size; _] as args), loc))
        when isFunctionType fv.vtype && fv.vname = Name.Function.kzalloc ->
        let get_function name =
          try
            Kernel_function.get_vi (Globals.Functions.find_by_name name)
          with
          | Not_found ->
            Console.unsupported
              ("Using kzalloc without declared %s prototype. \
                Please provide a declaration for %s with minimal specification (will be ignored)")
              name name
        in
        let vi_kmalloc = get_function Name.Function.kmalloc in
        let vi_memset = get_function "memset" in
        let lv = new_exp ~loc (Lval lv) in
        let z = zero ~loc in
        stmt.skind <-
          Block
            (mkBlock
               [mkStmt (Instr (Call (lv_opt, evar ~loc:eloc vi_kmalloc, args, loc)));
                mkStmt (
                  If
                    (mkBinOp ~loc Ne lv z,
                     mkBlock
                       [mkStmt (Instr (Call (None, evar ~loc:eloc vi_memset, [lv; z; size], loc)))],
                     mkBlock [mkStmt (Instr (Skip loc))],
                     loc))]);
        SkipChildren
      | _ -> DoChildren
  end

let expand_kzallocs file = visitFramacFile (new kzalloc_expanding_visitor) file

(*****************************************************************************)
(* Support for alloca (and corresponding dynamic stack arrays)               *)
(*****************************************************************************)

class alloca_rewriter =
  object
    inherit frama_c_inplace

    method! vinst =
      function
      | Call (lv, ({ enode = Lval (Var vi, NoOffset) } as e), ([_] as args), loc)
        when isFunctionType vi.vtype && Ast.Vi.Function.(is_alloca @@ of_varinfo_exn vi) ->
        ChangeTo [Call (lv, { e with enode = Lval (Var (Ast.Vi.Function.malloc () :> varinfo), NoOffset) }, args, loc)]
      | _ -> SkipChildren
  end

let rewrite_alloca = visitFramacFile (new alloca_rewriter)

let get_specialized_name (*_type*) (*original_name*) =
  let type_regexp = Str.regexp_string "_type" in
  fun typ ->
    Str.replace_first type_regexp (Name.typ typ)

let is_pattern_type =
  function
  | TNamed ({ torig_name = "_type"; ttype = TInt (_, []) }, _) -> true
  | _ -> false

class spec_refreshing_vsitor =
  object
    method vspec : 'a -> 'a visitAction = fun _ ->
      let refresh_spec s =
        match Logic_const.(refresh_code_annotation @@ new_code_annotation @@ AStmtSpec ([], s)) with
        | { annot_content = AStmtSpec (_, s) } -> s
        | a -> Console.fatal "Unexpectedly refreshed AStmtSpec to something else: %a" Printer.pp_code_annotation a
    in
    DoChildrenPost refresh_spec
  end

class type_substituting_visitor typ =
  object
    method vtype : 'a -> 'a visitAction =
      fun t ->
        if not (is_pattern_type t) then
          DoChildren
        else
          ChangeTo (typeAddAttributes (typeAttrs t) typ)
  end

module Logic_var_ =
struct
  module H = Logic_var.Hashtbl

  module Visitor =
  struct
    class virtual logic_var_visitor typ =
      let get_specialized_name = get_specialized_name typ in
      object(self)
        method virtual behavior : visitor_behavior

        val olds = H.create 10
        val news = H.create 10

        method private set_old = H.replace olds
        method private set_new = H.replace news
        method private is_old = H.mem news
        method private is_new = H.mem olds

        method private virtual vlogic_var_copying : logic_var -> logic_var visitAction

        method private virtual vlogic_var_renaming : logic_var -> logic_var visitAction

        method vlogic_var_decl : 'a -> 'a visitAction =
          fun ({ lv_name; lv_origin } as lv) ->
            if self#is_old lv then      ChangeTo (H.find news lv)
            else if self#is_new lv then DoChildren
            else if lv_name = get_specialized_name lv_name then
              (* logic var name does NOT contain template => just copy it to avoid sharing before renaming *)
              self#vlogic_var_copying lv
            else
              (* logic var name DOES contain template => copy and rename it by substituting _type with type name *)
              match lv_origin with
              | None -> self#vlogic_var_renaming lv
              | Some vi -> Console.fatal "Can't handle logic variable with origin: %a" Printer.pp_varinfo vi

        method vlogic_var_use = self#vlogic_var_decl
      end
  end
end

include Logic_var_.Visitor

class virtual logic_var_specializing_visitor update_logic_info typ =
  let update_logic_info = update_logic_info typ in
  object(self)
    inherit logic_var_visitor typ

    method private vlogic_var_copying ({ lv_name; lv_type; lv_kind } as lv) =
      let lv' = Cil_const.make_logic_var_kind lv_name lv_kind lv_type in
      set_logic_var self#behavior lv lv';
      set_orig_logic_var self#behavior lv' lv;
      self#set_old lv' lv;
      self#set_new lv lv';
      ChangeTo lv'

    method private vlogic_var_renaming ({ lv_name } as lv) =
      match Logic_env.find_all_logic_functions lv_name with
      | [ li ] ->
        let { l_var_info = lv' } as li' = update_logic_info li in
        set_logic_info self#behavior li li';
        set_orig_logic_info self#behavior li' li;
        set_logic_var self#behavior lv lv';
        set_orig_logic_var self#behavior lv' lv;
        ChangeTo lv'
      | [] -> Console.fatal "Can't find logic_info for logic variable: %s" lv_name
      | _ -> Console.fatal "Ambiguous logic_info for logic variable: %s" lv_name
  end

class virtual logic_var_renaming_visitor typ =
  let get_specialized_name = get_specialized_name typ in
  object(self)
    inherit logic_var_visitor typ

    method private vlogic_var_copying _ = DoChildren

    method private vlogic_var_renaming ({ lv_name; lv_type; lv_kind } as lv) =
      let lv_name' = get_specialized_name lv_name in
      let lv' = Cil_const.make_logic_var_kind lv_name' lv_kind lv_type in
      set_logic_var self#behavior lv lv';
      set_orig_logic_var self#behavior lv' lv;
      ChangeTo lv'
  end

class specialize_blockfuns_visitor =
  let specialize_logic_info typ (* logic_info *) =
    let visitor = object
      inherit frama_c_inplace
      inherit! type_substituting_visitor typ
      inherit! logic_var_renaming_visitor typ
    end in
    fun logic_info ->
      let logic_info' = visitFramacLogicInfo (new frama_c_copy @@ Project.current ()) logic_info in
      visitFramacLogicInfo visitor logic_info'
  in
  let specialize_blockfun update_logic_info typ { fundec; spec } =
    let visitor =
      object
        inherit frama_c_copy (Project.current ())
        inherit! spec_refreshing_vsitor
        inherit! type_substituting_visitor typ
        inherit! logic_var_specializing_visitor update_logic_info typ
      end
    in
    match fundec with
    | Declaration (spec, fvinfo, Some argvinfos, loc) ->
      let spec = visitFramacFunspec visitor spec in
      let fvinfo = visitFramacVarDecl visitor fvinfo in
      let argvinfos =
        ListLabels.map
          argvinfos
          ~f:(fun vi ->
            let vi = visitFramacVarDecl visitor vi in
            vi.vlogic_var_assoc <- Option.map vi.vlogic_var_assoc ~f:(get_logic_var visitor#behavior);
            Option.iter vi.vlogic_var_assoc ~f:(fun lv -> lv.lv_origin <- Some vi);
            vi)
      in
      (spec, fvinfo, argvinfos, loc)
    | _ -> Console.fatal "Can't specialize user-defined block function: %a" Printer.pp_funspec spec
  in
  let is_block_function = function
    | { fundec = Declaration (_, _, _, ({ Lexing.pos_fname }, _)) } ->
      Filename.basename pos_fname = Name.File.blockfuns_include
    | _ -> false
  in
  let pointed_type' =
    function
    | TPtr (t, _) -> t
    | TArray _ as arrty -> element_type arrty
    | ty -> ty
  in
  let match_arg_types ftype tl_opt tacts =
    match ftype with
    | TFun (rtype, Some formals, _, _) ->
      let _type_ref = ref None in
      let matches ~tf:tf ta =
        let irrelevant_attrs = ["restrict"; "volatile"] in
        let const_attr = "const" in
        let strip = typeRemoveAttributes irrelevant_attrs in
        let strip_const = typeRemoveAttributes (const_attr :: irrelevant_attrs) in
        if not (is_pattern_type @@ pointed_type' tf) then begin
          not @@ need_cast
            ((if not @@ hasAttribute const_attr @@ typeAttrs tf then strip else strip_const) ta)
            tf
        end else
          let ta = if isPointerType ta then pointed_type ta else ta in
          Option.map_default
            !_type_ref
            ~default:true
            ~f:(fun typ -> isVoidType ta || isCharType ta || not (need_cast ta typ)) &&
          (if not (isVoidType ta || Option.is_some !_type_ref) then _type_ref := Some ta; true)
      in
      if
        List.length formals = List.length tacts &&
        List.for_all Fn.id @@
        (Option.map_default tl_opt ~default:true ~f:(matches ~tf:rtype)) ::
        List.map2 (fun (_, tf, _) ta -> matches ~tf ta) formals tacts
      then Some (!_type_ref |? charType)
      else None
    | TFun _ -> Console.fatal "Can't specialize the function by its return type: %a" Printer.pp_typ ftype
    | _ -> Console.fatal "%a is not a function type, can't check if the signature matches" Printer.pp_typ ftype
  in
  object(self)
    inherit frama_c_inplace

    val mutable new_globals = []
    val mutable introduced_globals = []
    val mutable old_globals = []

    method private update_logic_info typ (*li*) =
      let get_specialized_name = get_specialized_name typ in
      let rec match_global_with_lvar_name name = function
        | GAnnot (Dfun_or_pred ({ l_var_info = { lv_name } }, _), _) -> lv_name = name
        | GAnnot (Daxiomatic (_, lst, loc), _) ->
          List.exists (match_global_with_lvar_name name) (List.map (fun ga -> GAnnot (ga, loc)) lst)
        | _ -> false
      in
      fun ({ l_var_info={ lv_name } } as li) ->
        let lv_name' = get_specialized_name lv_name in
        let match_global' = match_global_with_lvar_name lv_name' in
        let rec find_li' =
          function
          | GAnnot (Dfun_or_pred (li, _), _) -> li
          | GAnnot (Daxiomatic (_, lst, loc), _) ->
            find_li' (List.find match_global' (List.map (fun ga -> GAnnot (ga, loc)) lst))
          | _ -> assert false
        in
        let handle_user_decl li' =
          if List.exists match_global' old_globals then
            let li = find_li' (List.find match_global' old_globals) in
            if Logic_utils.(
              is_same_logic_profile li li' &&
              Option.equal is_same_type li.l_type li'.l_type) &&
               List.(length li.l_labels = length li'.l_labels)
            then
              if li.l_body = LBnone then begin
                li.l_profile <- li'.l_profile;
                li.l_body <- li'.l_body
              end else
                Console.abort "Can't specialize logic function/predicate `%s' to `%s': it already has a definition"
                  lv_name (get_specialized_name lv_name)
        in
        try
          let result = find_li' (List.find match_global' @@ new_globals @ introduced_globals) in
          handle_user_decl result;
          result
        with
        | Not_found ->
          let match_global = match_global_with_lvar_name lv_name in
          let axiomatic_opt =
            Annotations.fold_global
              (fun _ g acc -> if match_global @@ GAnnot (g, Location.unknown) then Some g else acc)
              None
          in
          let specialize_logic_info = specialize_logic_info typ in
          begin match axiomatic_opt with
          | Some Daxiomatic (name, lst, _) ->
            let name = get_specialized_name name in
            let lst =
              ListLabels.map
                lst
                ~f:(function
                  | Dfun_or_pred (li, loc) ->
                    let li = specialize_logic_info li in
                    Dfun_or_pred (li, loc)
                  | _ -> Console.fatal "Can't specialize unknown logic info in axiomatic: %s" name)
            in
            handle_user_decl
              (Option.value_fatal ~in_:"specialize_blockfuns_visitor:update_logic_info" @@
               List.find_map
                 ~f:(function Dfun_or_pred (li, _) when li.l_var_info.lv_name = lv_name' -> Some li | _ -> None)
                 lst);
            let g = Daxiomatic (name, lst, Location.unknown) in
            new_globals <- GAnnot (g, CurrentLoc.get ()) :: new_globals;
            Annotations.add_global Emitters.jessie g;
            self#update_logic_info typ li
          | Some _ ->
            Console.fatal
              "Logic info (predicate, function, ...) specialization outside axiomatics is not supported: %s"
              lv_name
          | None ->
            Console.fatal "Can't find global logic info (predicate, function, ..): %s" lv_name
          end

    method private find_specialized_function fname =
      try
        let fdecl =
          ListLabels.find
            (new_globals @ introduced_globals)
            ~f:(function
              | GVarDecl (_, { vname }, _) -> vname = fname
              | _ -> false)
        in
        match fdecl with
        | GVarDecl (_, f, _) -> Some f
        | _ -> assert false
      with
      | Not_found -> None

    method private specialize_function kf fname typ =
      let spec, fvinfo, argvinfos, loc = specialize_blockfun (self#update_logic_info) typ kf in
      let f = makeGlobalVar fname fvinfo.vtype in
      f.vstorage <- fvinfo.vstorage;
      f.vattr <- fvinfo.vattr;
      unsafeSetFormalsDecl f argvinfos;
      new_globals <- GVarDecl (empty_funspec (), f, loc) :: new_globals;
      Globals.Functions.replace_by_declaration spec f loc;
      let kernel_function = Globals.Functions.get f in
      Annotations.register_funspec ~emitter:Emitters.jessie kernel_function;
      f

    method! vstmt_aux =
      function
      | { skind = Instr (Call (lval_opt, { enode = Lval (Var fvar, NoOffset) }, args , loc)) } as stmt ->
        begin try
          let fpatt = Globals.Functions.find_by_name (fvar.vname ^ "__type") in
          if is_block_function fpatt then
            let args = List.map (Ast.Exp.strip_casts_to voidPtrType) args in
            let lval_type_opt = Option.map lval_opt ~f:typeOfLval in
            let arg_types =  List.map typeOf args in
            let fvtype = match fpatt.fundec with
              | Declaration (_, { vtype }, _ ,_) -> vtype
              | _ -> assert false (* is_block_function == true *)
            in
            match match_arg_types fvtype lval_type_opt arg_types with
            | Some typ ->
              let f =
                let fname = fvar.vname ^ "_" ^ Name.typ typ in
                match self#find_specialized_function fname with
                | Some f -> f
                | None ->
                  if fname <> Name.unique fname then
                    Console.fatal "Can't introduce specialized function due to name conflict: %s" fname;
                  self#specialize_function fpatt fname typ
              in
              let args =
                List.map2
                  (fun t arg ->
                     let typ = if isPointerType t || isArrayType t then TPtr (typ, []) else typ in
                     if is_pattern_type @@ pointed_type' t && need_cast (typeOf arg) typ then
                       mkCast
                         ~force:false
                         ~overflow:Check
                         ~e:arg
                         ~newt:typ
                     else
                       arg)
                  (match fvtype with
                   | TFun (_, Some formals, _, _) -> List.map (fun (_, t, _) -> t) formals
                   | _ -> assert false (* ensured by match_arg_types *))
                  args
              in
              stmt.skind <- Instr (Call (lval_opt, evar ~loc f, args, loc));
              SkipChildren
            | _ ->
              Console.unsupported
                "Can't specialize %s applied (or assigned) to arguments (lvalue) of incorrect type(s):@[%a@]@.\
                 The type of %s is considered to be:@\n@[<hov 2>%a@].@.The types in the call-site context:@\n\
                 @[<hov 2>%a@ (%a)@]."
                fvar.vname Printer.pp_stmt stmt fvar.vname Printer.pp_typ fvar.vtype
                Printer.pp_typ (lval_type_opt |? voidType)
                (Format.pp_print_list ~pp_sep:(fun f () -> Format.fprintf f ",@ ") Printer.pp_typ) arg_types
          else
            DoChildren
        with
        | Not_found -> DoChildren
        end
      | _ -> DoChildren

    method! vglob_aux _ =
      DoChildrenPost (fun globals ->
        introduced_globals <- new_globals @ introduced_globals;
        let saved_globals = new_globals in
        new_globals <-[];
        saved_globals @ globals)

    method! vfile f =
      old_globals <- f.globals;
      DoChildren
  end

let specialize_blockfuns file =
  visitFramacFile (new specialize_blockfuns_visitor) file;
  (* We may have introduced new globals: clear the last_decl table. *)
  Framac.Ast.clear_last_decl ()

(*****************************************************************************)
(* Extending `assigns' clauses and equalities for composite types.           *)
(*****************************************************************************)

class composite_expanding_visitor =
  let ctype ?(force=true) = function
    | Ctype t -> t
    | Ltype ({ lt_name = "set" }, [Ctype t]) -> t
    | _ -> assert (not force); TVoid []
  in
  let rec expand_equality ty t1 t2 =
    let rec add_term_offset ty offset ({ term_node; term_loc=loc } as t) =
      let open! Logic_const in
      match term_node with
      | TLval tlv ->
        let offset = match offset with
          | `Field f -> TField (f, TNoOffset)
          | `Index i -> TIndex (tinteger ~loc i, TNoOffset)
        in
        {
          t with
          term_node = TLval (addTermOffsetLval offset tlv);
          term_type = Ctype ty
        }
      | Tat (t, lab) -> tat ~loc (add_term_offset ty offset t, lab)
      | TCastE (_, oft, ({ term_type } as t))
        when term_type = Linteger || term_type = Lreal ||
             isIntegralType (ctype ~force:false term_type) ||
             isFloatingType (ctype ~force:false term_type) ->
        {
          t with term_node =
                   TCastE (ty,
                           oft,
                           if isIntegralType ty then tinteger ~loc 0
                           else if isFloatingType ty then treal_zero ()
                           else if isPointerType ty then term ~loc Tnull (Ctype ty)
                           else t) }
      | TConst _ -> t
      | _ -> Console.unsupported "Don't know hot to expand term node: %a" Printer.pp_term t
    in
    match unrollType ty with
    | TComp (ci, _, _) ->
      let do_field ({ ftype } as f) =
        let shift = add_term_offset ftype (`Field f) in
        expand_equality ftype (shift t1) (shift t2)
      in
      List.flatten @@ List.map do_field (Type.Composite.Ci.proper_fields ci)
    | TArray (telem, _, _, _) as ty ->
      let do_elem i =
        let shift = add_term_offset telem (`Index i) in
        expand_equality telem (shift t1) (shift t2)
      in
      let rec do_elems acc i =
        if i <= 0 then acc
        else do_elems (do_elem (i - 1) @ acc) (i - 1)
      in
      assert (not @@ Type.Ref.is_ref ty);
      do_elems [] @@ Integer.to_int (direct_array_size ty)
    | _ -> [Prel (Req, t1, t2)]
  in
  let identified_term_list_of_equality_list =
    List.map
      (function
        | Prel (Req, t, { term_node = TConst _}) -> Logic_const.new_identified_term t
        | _ -> assert false)
  in
  let predicate_of_equality_list loc lst =
    Logic_const.(pands @@ List.map (unamed ~loc) lst).content
  in
  let is_term_to_expand { term_type } =
    let t = ctype ~force:false term_type in
    isStructOrUnionType t || isArrayType t
  in
  let expand_identified_term_list lst =
    let dummy_term = Logic_const.tinteger 0 in
    let (to_expand, to_prepend) = ListLabels.partition lst ~f:(fun { it_content } -> is_term_to_expand it_content) in
    to_expand |>
    List.map (fun { it_content = { term_type } as t } -> expand_equality (ctype term_type) t dummy_term) |>
    List.flatten |>
    identified_term_list_of_equality_list |>
    fun expanded -> to_prepend @ expanded
  in
  object
    method vdeps =
      function
      | FromAny -> DoChildren
      | From lst -> ChangeTo (From (expand_identified_term_list lst))

    method vassigns =
      function
      | WritesAny -> DoChildren
      | Writes lst ->
        let lst = List.flatten @@ ListLabels.map lst ~f:(function
          | { it_content = { term_type = ty1 } } as it1,
            From [ { it_content = { term_type = ty2 } } as it2]
            when Logic_utils.is_same_type ty1 ty2 ->
            List.map2
              (fun it1 it2 -> it1, From [it2])
              (expand_identified_term_list [it1])
              (expand_identified_term_list [it2])
          | it1, from -> List.map (fun it -> it, from) @@ expand_identified_term_list [it1])
        in
        ChangeTo (Writes lst)

    method vpredicate_named =
      let open Logic_const in
      function
      | { loc;
          content =
            Prel (Req | Rneq as r,
                  ({ term_node = TBinOp (Eq | Ne as b1, t11, t12) } as t1),
                  ({ term_node = TBinOp (Eq | Ne as b2, t21, t22) } as t2)) } ->
        let rel r = if r = Eq then Req else Rneq in
        let p1 = prel ~loc:t1.term_loc (rel b1, t11, t12) and p2 = prel ~loc:t2.term_loc (rel b2, t21, t22) in
        ChangeDoChildrenPost ((if r = Req then piff else pxor) ~loc (p1, p2), Fn.id)
      | _ -> DoChildren

    method vpredicate = function
      | Prel (Req, ({ term_loc; term_type=ty1 } as t1), ({ term_type=ty2 } as t2)) ->
        let expand1 = is_term_to_expand t1 and expand2 = is_term_to_expand t2 in
        if expand1 && expand2 && Logic_utils.is_same_type ty1 ty2 || not (expand1 = expand2) then
          let result = predicate_of_equality_list term_loc @@ expand_equality (ctype ty1) t1 t2 in
          let open! Logic_const in
          let eq_implies_result t1 t2 =
            (pimplies ~loc:term_loc (prel ~loc:term_loc (Req, t1, t2), unamed result)).content
          in
          let st1 = stripTermCasts t1 and st2 = stripTermCasts t2 in
          match st1 == t1, st2 == t2 with
          | true, true -> ChangeTo result
          | false, true -> ChangeTo (eq_implies_result st1 @@ tinteger ~loc:term_loc 0)
          | true, false -> ChangeTo (eq_implies_result st2 @@ tinteger ~loc:term_loc 0)
          | _ -> Console.unsupported "Don't know how to expand equality: %a = %a" Printer.pp_term t1 Printer.pp_term t2
        else
          DoChildren
      | _ -> DoChildren
  end

let expand_composites =
  visitFramacFile
    (object
      inherit frama_c_inplace
      inherit! composite_expanding_visitor
    end)

(*****************************************************************************)
(* Retype bitwise operations in logic.                                       *)
(*****************************************************************************)

class term_bw_op_retyping_visitor =
  let is_int_type t =
    match unrollType t with
    | TInt _ -> true
    | _ -> false
  in
  let strip ?(force=true) t =
    let open Logic_utils in
    match t.term_node with
    | TConst (Integer (_, Some s)) when t.term_type = Linteger ->
      let ty = typeOf @@ parseIntExp ~loc:Location.unknown s in
      let lty = Ctype (unrollType ty) in
      Logic_const.term ~loc:t.term_loc (TCastE (ty, Check, t)) lty,
      lty
    | TLogic_coerce (Linteger, ({ term_type = lty } as t1))
      when isLogicType is_int_type @@ unroll_type lty ->
      t1, unroll_type lty
    | _ when isLogicType is_int_type @@ unroll_type t.term_type -> t, unroll_type t.term_type
    | _ when force ->
      Console.unsupported
        "Can't automatically recover built-in bounded integral type of term %a"
        Printer.pp_term t
    | _ -> t, t.term_type
  in
  object(self)
    inherit frama_c_inplace

    val retyped_vars = Logic_var.Hashtbl.create 25

    method private vlet : 'a. f:('a -> 'a) -> change_to:(unit -> 'a) -> _ -> 'a visitAction =
      fun ~f ~change_to ->
        function
        | { l_var_info; l_labels = []; l_type = Some Linteger; l_profile = []; l_body = LBterm t; _ } as li ->
          let t, lt = strip ~force:false @@ visitFramacTerm (self :> frama_c_visitor) t in
          li.l_body <- LBterm t;
          if Logic_utils.isLogicType is_int_type lt then begin
            li.l_type <- Some lt;
            l_var_info.lv_type <- lt;
            Logic_var.Hashtbl.add retyped_vars l_var_info ();
            ChangeTo (change_to ())
          end else
            DoChildrenPost f
        | _ -> DoChildrenPost f

    method! vterm t =
      let f t =
        let wrap term_node term_type =
          Logic_const.term
            ~loc:t.term_loc
            (TLogic_coerce (Linteger, { t with term_node; term_type }))
            Linteger
        in
        match t.term_node with
        | TLval (TVar lv, TNoOffset) when Logic_var.Hashtbl.mem retyped_vars lv ->
          wrap t.term_node lv.lv_type
        | TBinOp (
          (PlusA Modulo | MinusA Modulo | Mult Modulo | Div Modulo | Shiftlt _ | Shiftrt | BAnd | BXor | BOr as op),
          t1, t2) ->
          let (t1, ty1), (t2, ty2) = map_pair strip (t1, t2) in
          if Logic_utils.is_same_type ty1 ty2 then
            wrap (TBinOp (op, t1, t2)) ty1
          else
            Console.abort
              ~source:(fst @@ t.term_loc)
              "Bitwise operation %a applied to arguments of different types: %a and %a"
              Printer.pp_binop op
              Printer.pp_logic_type ty1
              Printer.pp_logic_type ty2
        | TUnOp (BNot, t1) ->
          let t1, ty1 = strip t1 in
          wrap (TUnOp (BNot, t1)) ty1
        | TCastE (ty, oft, t') when is_int_type ty ->
          let t', ty' = strip ~force:false t' in
          if Logic_utils.isLogicType is_int_type ty' then
            if Logic_utils.is_same_type (Ctype (unrollType ty)) ty' then t'
            else {t with term_node = TCastE (ty, oft, t') }
          else t
        | TBinOp ((Lt | Gt | Le | Ge | Eq | Ne as rel), t1, t2) ->
          let (t1, ty1), (t2, ty2) = map_pair (strip ~force:false) (t1, t2) in
          if Logic_utils.is_same_type ty1 ty2 then
            { t with term_node = TBinOp (rel, t1, t2) }
          else
            t
        | _ -> t
      in
      match t.term_node with
      | Tlet (li, t) ->
        self#vlet
          ~f
          li
          ~change_to:(fun () ->
            let t', term_type = strip ~force:false @@ visitFramacTerm (self :> frama_c_visitor) t in
            { t with term_node = Tlet (li, t'); term_type })
      | _ -> DoChildrenPost f

    method! vpredicate =
      let f =
        function
        | Prel (rel, t1, t2) as p ->
          let (t1, ty1), (t2, ty2) = map_pair (strip ~force:false) (t1, t2) in
          if Logic_utils.is_same_type ty1 ty2 then
            Prel (rel, t1, t2)
          else
            p
        | p -> p
      in
      function
      | Plet (li, p) ->
        self#vlet
          ~f
          li
          ~change_to:
            (fun () ->
               Plet (li, { p with content = visitFramacPredicate (self :> frama_c_visitor) p.content }))
      | _ -> DoChildrenPost f
  end

let retype_bw_ops_in_terms = visitFramacFile @@ new term_bw_op_retyping_visitor

(*****************************************************************************)
(* Replace inine assembly with undefined function calls.                     *)
(*****************************************************************************)

class asms_to_functions_visitor =
  let mkAddrOf ~loc lv =
    let rec set_flag =
      function
      | Var vi, NoOffset -> vi.vaddrof <- true
      | _, Field (fi, NoOffset) -> fi.faddrof <- true
      | vi, Field (_, offset) -> set_flag (vi, offset)
      | vi, Index (_, offset) -> set_flag (vi, offset)
      | Mem _, _ -> ()
    in
    set_flag lv;
    mkAddrOf ~loc lv
  in
  let exp_of_lval ?(addr=false) ~loc lv = if addr then mkAddrOf ~loc lv else new_exp ~loc @@ Lval lv in
  let to_args ~loc ins outs =
    let thrd (_, _, e) = e in
    List.map thrd ins @ List.map (fun trpl -> exp_of_lval ~loc ~addr:true @@ thrd trpl) outs
  in
  object(self)
    inherit frama_c_inplace

    val mutable new_globals = []

    method! vglob_aux =
      let f g = let r = new_globals in new_globals <- []; r @ g in
      function
      | GAsm _ ->
        Console.warning "Ignoring global inline assembly, which can potentially have side effects!";
        ChangeToPost ([], f)
      | _ -> DoChildrenPost f

    method private introduce_function ?(int=false) attrs outs ins clobs loc =
      let to_param pkind i (name_opt, _, e) =
        let typ = typeOf e in
        let ret name =
          match pkind with
          | `Input ->  Name.unique name, typ, []
          | `Output -> Name.unique name, TPtr (typ, [Attr ("const", [])]), []
        in
        match name_opt with
        | Some name -> ret name
        | None -> match e.enode with
          | Lval (Var { vname }, _) -> ret vname
          | _ -> ret @@ (match pkind with `Input -> "in" | `Output -> "out") ^ string_of_int i
      in
      let to_oparam i (name_opt, constr, lval) = to_param `Output i (name_opt, constr, exp_of_lval ~loc lval) in
      let ins = List.mapi (to_param `Input) ins and outs = List.mapi to_oparam outs in
      let params = ins @ outs in
      let ret_typ = if int then intType else voidType in
      let attrs = attrs @ List.map (fun a -> Attr (a, [])) ["static"; "inline"] in
      let fname = Name.unique ("inline_asm" ^ (if int then "_goto" else "")) in
      let f = makeGlobalVar ~source:false fname @@ TFun (ret_typ, Some params, false, attrs) in
      new_globals <- GVarDecl (empty_funspec (), f, loc) :: new_globals;
      Globals.Functions.replace_by_declaration (empty_funspec ()) f loc;
      (* We've created a new undefined unspecified function. Now let's specify it: *)
      let { fundec } as kf = Globals.Functions.get f in
      match fundec with
      | Declaration (funspec, _, Some args, loc) ->
        let get_vars = List.map @@ fun (name, typ, _) ->
          let vi = List.find (fun { vname } -> vname = name) @@ args in
          let result = Cil_const.make_logic_var_formal name (Ctype typ) in
          vi.vlogic_var_assoc <- Some result;
          result.lv_origin <- Some vi;
          result
        in
        let reads_any = ListLabels.exists ins ~f:(fun (_, typ, _)  ->
          isPointerType typ || isStructOrUnionType typ || isArrayType typ)
        in
        let out_types = List.map (fun (_, typ, _) -> typ) outs in
        let ins = get_vars ins and outs = get_vars outs in
        let has_mem_clob = List.exists ((=) "memory") clobs in
        funspec.spec_behavior <-
          (let open! Logic_const in
           [mk_behavior
              ~requires:[new_predicate @@ pands @@ List.map (fun lv -> pvalid ~loc (here_label, tvar ~loc lv)) outs]
              ~assigns:(if has_mem_clob then
                          Console.warning "The inline assembly includes memory clobber, but no side effect is assumed!";
                        let to_terms = List.map @@ tvar ~loc in
                        let outs from =
                          let outs =
                            (if int then [tresult ~loc intType] else []) @
                            ListLabels.map2 (to_terms outs) out_types ~f:(fun t typ ->
                              term ~loc (TLval (TMem t, TNoOffset)) @@ Ctype (pointed_type typ))
                          in
                          Writes (List.map (fun t -> new_identified_term t, from) outs)
                        in
                        if reads_any then begin
                          Console.warning ("The inline assembly takes pointer, array or composite argument, so \
                                            over-approximating data dependencies in assigns clause with FromAny");
                          outs FromAny
                        end else
                          outs (From (List.map new_identified_term @@ to_terms ins)))
              ()]);
        Annotations.register_funspec ~emitter:Emitters.jessie kf;
        f
      | Declaration (_, _, None, _) -> Console.fatal "Generated dummy function has somehow lost its arguments"
      | Definition _ -> Console.fatal "Generated dummy function was somehow unexpectedly defined"

    method! vinst =
      function
      | Asm (attrs, _, outs, ins, clobs, [], loc) ->
        let f = self#introduce_function attrs outs ins clobs loc in
        ChangeTo [Call (None, evar ~loc f, to_args ~loc ins outs, loc)]
      | Asm _ ->
        Console.fatal "Unsupported representation for asm goto (use AsmGoto statement instead of Asm instruction)"
      | _ -> DoChildren

    method! vstmt_aux =
      function
      | { skind = AsmGoto (attrs, _, outs, ins, clobs, stmts, loc) } as s ->
        let f = self#introduce_function ~int:true attrs outs ins clobs loc in
        begin match self#current_func with
        | Some fundec ->
          let aux = makeLocalVar fundec ~temp:true (Name.unique "inline_asm_goto_aux") intType in
          self#queueInstr [Call (Some (var aux), evar ~loc f, to_args ~loc ins outs, loc)];
          let labeled lab ({ labels } as stmt) = stmt.labels <- lab :: labels; stmt in
          let cases =
            let rec loop acc n =
              function
              | [] -> List.rev @@ (labeled (Default loc) @@ mkStmtOneInstr ~valid_sid:true (Skip loc)) :: acc
              | sref :: srefs ->
                loop
                  ((labeled (Case (integer ~loc @@ n, loc)) @@ mkStmt (Goto (sref, loc))) :: acc)
                  (n + 1)
                  srefs
            in
            loop [] 0 stmts
          in
          s.skind <- Switch (evar aux, mkBlock cases, cases, loc);
          SkipChildren
        | None -> Console.fatal "Can't introduce local auxiliary variable outside function body"
        end
      | _ -> DoChildren
  end

let asms_to_functions file =
  visitFramacFile (new asms_to_functions_visitor) file;
  (* We may have introduced new globals: clear the last_decl table. *)
  Framac.Ast.clear_last_decl ()

(*****************************************************************************)
(* Rewrite function pointers into void* and fp calls into if statements.     *)
(*****************************************************************************)

class fptr_to_pvoid_visitor =
  object
    inherit frama_c_inplace

    method! vtype t =
      match unrollTypeDeep t with
      | TPtr (TFun _, _) | TArray (TFun _, _, _, _) -> ChangeTo voidConstPtrType
      | _ -> DoChildren

    method! vlogic_type =
      function
      | Ctype t ->
        begin match unrollTypeDeep t with
        | TFun _ | TPtr (TFun _, _) | TArray (TFun _, _, _, _) -> ChangeTo (Ctype voidConstPtrType)
        | _ -> DoChildren
        end
      | _ -> DoChildren
  end

class fp_eliminating_visitor ~attach =
  let fatal_offset = Console.fatal "Encountered function type with offset: %a" Printer.pp_exp in
  let fatal_transform = Console.fatal "Unexpectedly transformed function call to something else: %a" Printer.pp_stmt in
  let do_not_touch = ref None in
  let do_expr_pre e =
    match e.enode with
    | Lval (Mem e, NoOffset) when isFunctionType @@ typeOf e -> e
    | Lval (Mem e', _) when isFunctionType @@ typeOf e' -> fatal_offset e
    | _ -> e
  in
  let intro_var =
    let module Hashtbl = Varinfo.Hashtbl in
    let new_vis = Hashtbl.create 10 in
    fun ~loc vi ->
      let cast_addr0 vi =
        mkCast
          ~overflow:Check
          ~force:false
          ~e:(mkAddrOf ~loc (Var vi, Index (integer ~loc 0, NoOffset)))
          ~newt:voidConstPtrType
      in
      try
        cast_addr0 @@ Hashtbl.find new_vis vi
      with
      | Not_found ->
        let name = Name.unique ("dummy_place_of_" ^ vi.vname) in
        let typ = array_type ~length:(integer ~loc:vi.vdecl 16) charType in
        let vi' = makeGlobalVar ~source:false name typ in
        attach#global @@ GVar (vi', { init = None }, vi.vdecl);
        vi'.vdecl <- vi.vdecl;
        vi.vaddrof <- true;
        vi'.vaddrof <- true;
        Hashtbl.add new_vis vi vi';
        cast_addr0 vi'
  in
  let do_expr_post e =
    if !do_not_touch = Some e.eid then begin
      do_not_touch := None;
      e
    end else
      match e.enode with
      | Lval (Var vi, NoOffset) | AddrOf (Var vi, NoOffset) when isFunctionType vi.vtype -> intro_var ~loc:e.eloc vi
      | Lval (Var vi, _) | AddrOf (Var vi, _) when isFunctionType vi.vtype -> fatal_offset e
      | _ -> e
  in
  object(self)
    inherit frama_c_inplace

    method! vexpr e = ChangeDoChildrenPost (do_expr_pre e, do_expr_post)

    method! vterm = Do.on_term ~pre:do_expr_pre ~post:do_expr_post

    method! vstmt_aux s =
      match s.skind with
      | Instr (Call (_, ({ enode = Lval (Var { vtype }, NoOffset) } as f), _, _)) when isFunctionType vtype ->
        do_not_touch := Some f.eid;
        DoChildren
      | Instr (Call (_, ({ enode = Lval (Var { vtype }, _) } as e), _, _)) when isFunctionType vtype ->
        fatal_offset e
      | Instr (Call (_, f, _, _)) ->
        let types t =
          match unrollType t with
          | TFun (rt, ao, _, _) -> rt :: (List.map (fun (_, t, _) -> t) @@ Option.value ~default:[] ao)
          | t -> Console.fatal "Non-function (%a) called as function: %a" Printer.pp_typ t Printer.pp_exp f
        in
        let norm, ts =
          let t = typeOf f in
          if isPointerType t then
            Fn.id, types @@ pointed_type t
          else
            (function
              | { enode = Lval (Mem e, _) } -> e
              | _ -> Console.fatal ("Expression of function type which is not a function \
                                     nor a function pointer dereference: %a") Printer.pp_exp f),
            types t
        in
        let candidates ~loc =
          Globals.Functions.fold
          (fun kf acc -> match kf.fundec with
            | Definition ( { svar = { vtype; vaddrof=true } as vi }, _)
            | Declaration (_, ({ vtype; vaddrof=true } as vi), _, _) when isFunctionType vtype ->
              (vi, types vtype) :: acc
            | _ -> acc)
          []
        |>
        List.filter_map
          ~f:(fun (vi, ts') ->
            if List.(length ts = length ts' && not @@ exists2 (need_cast ~force:false) ts ts') then
              Some (vi, intro_var ~loc vi)
            else
              None)
      in
      let kf = Option.value_fatal ~in_:__LOC__ self#current_kf in
      let fundec = Option.value_fatal ~in_:__LOC__ self#current_func in
      let f =
        function
        | { skind = Instr (Call (lv_opt, f, args, loc)) } as s ->
          attach#globaction (fun () ->
            let vis, addrs = List.split @@ candidates ~loc in
            let z = zero ~loc in
            let eqs =
              let f = norm f in
              List.map (fun e -> new_exp ~loc @@ BinOp (Eq, f, e, intType)) addrs
                  in
                  Annotations.add_assert Emitters.jessie ~kf s @@
                    Ast.Predicate.Named.of_exp_exn @@
                      List.fold_left (mkBinOp ~loc LOr) z eqs;
                  let s' =
                    ListLabels.fold_left2
                      eqs vis
                      ~init:(let vi = makeTempVar fundec ~name:"unreachable" intType in
                             let s =
                               mkStmtOneInstr
                                 ~valid_sid:true
                                 (Set ((Var vi, NoOffset), mkBinOp ~loc (Div Check) z z, loc))
                             in
                             Annotations.add_assert Emitters.jessie ~kf s @@ Logic_const.pfalse;
                             s)
                      ~f:(fun acc eq vi ->
                          mkStmt (
                          If (eq,
                              mkBlock [mkStmtOneInstr ~valid_sid:true (Call (lv_opt, evar ~loc vi, args, loc))],
                              mkBlock [acc],
                              loc)))
                  in
                  s.skind <- s'.skind);
          s
        | s -> fatal_transform s
      in
      DoChildrenPost f
      | _ -> DoChildren
  end

let eliminate_fps file =
  (Visit.attaching_globs { Visit.mk = new fp_eliminating_visitor } file)[@warning "-42"];
  visitFramacFile (new fptr_to_pvoid_visitor) file;
  Framac.Ast.clear_last_decl ()

(*****************************************************************************)
(*  Add dummy definitions for structures only used in pointer types.         *)
(*****************************************************************************)

class dummy_struct_definer ~attach =
  object(self)
    inherit frama_c_inplace

    method! vcompinfo ci =
      if ci.cdefined = false && ci.cfields = [] then begin
        Console.warning
          "Defining dummy composite tag for %s in extract mode (enabled by -jessie-extract)"
          (compFullName ci);
        attach#global @@ GCompTag (ci, Location.unknown);
        ci.cdefined <- true
      end;
      DoChildren

    method! vglob_aux =
      function
      | GCompTagDecl (ci, _) ->
        ignore (self#vcompinfo ci);
        DoChildren
      | _ -> DoChildren
  end

let define_dummy_structs file =
  (Visit.attaching_globs { Visit.mk = new dummy_struct_definer } file)[@warning "-42"];
  Framac.Ast.clear_last_decl ()

(*****************************************************************************)
(* Rewrite va_list into void *                                               *)
(*****************************************************************************)

class va_list_rewriter () =
  let va_list_name = "va_list" in
  let const = Attr ("const", []) in
  let const_type = typeAddAttributes [const] in
  let flat = Config.Flat_vararg.get () in
  let va_list_type =
    if not flat then
      TPtr (const_type voidPtrType, [])
    else
      voidConstPtrType
  in
  let va_list_var_type ~loc n =
    if not flat then
      TArray (voidPtrType, Some (integer ~loc n), { scache = Not_Computed }, [])
    else
      voidPtrType
  in
  let va_start_name = "__builtin_va_start" in
  let va_arg_name = "__builtin_va_arg" in
  let va_end_name = "__builtin_va_end" in
  let va_copy_name = "__builtin_va_copy" in
  let const_ptr t = TPtr (t, [const]) in
  let va_list_in formals =
    match List.rev formals with
    | ("va_list", t, _) :: _ when unrollType t == va_list_type -> true
    | _ -> false
  in
  object(self)
    inherit frama_c_inplace

    method! vtype t =
      match unrollType t with
      | TBuiltin_va_list _ -> ChangeTo va_list_type
      | TFun (rt, args_opt, true, attrs) ->
        let va_arg = va_list_name, va_list_type, [] in
        ChangeDoChildrenPost (TFun (rt, Some (Option.value ~default:[] args_opt @ [va_arg]), false, attrs), Fn.id)
      | _ -> DoChildren

    method! vvdec { vtype; vdefined } =
      match unrollType vtype, vdefined with
      | TFun (_, _, true, _), false ->
        DoChildrenPost
          (fun vi ->
             let va_list = makeVarinfo ~source:false false true va_list_name va_list_type in
             let formals = getFormalsDecl vi @ [va_list] in
             unsafeSetFormalsDecl vi formals;
             let kf = Globals.Functions.get vi in
             Globals.Functions.replace_by_declaration (Annotations.funspec kf) vi (Kernel_function.get_location kf);
             (* Important invariant, because Jessie doesn't care about function signature matching *)
             assert (List.length formals = List.length Globals.Functions.(get_params (get vi)));
             vi)
      | _ -> DoChildren

    method! vfunc ({ svar } as fundec) =
      match unrollType svar.vtype with
      | TFun (_, _, true, _) ->
        let ftype = svar.vtype in
        ignore (makeFormalVar fundec va_list_name va_list_type);
        svar.vtype <- ftype; (* Will be rewritten again by vtype in the child *)
        DoChildren
      | _ -> DoChildren

    method! vinst _ =
      DoChildrenPost
        (function
          | [Call (None,
                   { enode = Lval (Var { vname = "__builtin_va_start" }, NoOffset) },
                   [{ enode = Lval ((Var va_list, NoOffset) as lva_list) }],
                   loc)]
            when unrollType va_list.vtype == va_list_type ->
            let current_func =
              Option.value_fatal ~in_:__LOC__ self#current_func
            in
            begin
              match List.rev current_func.sformals with
              | va_list' :: _
                when va_list'.vname = va_list_name &&
                     unrollType va_list'.vtype == va_list_type ->
                [Set (lva_list, evar ~loc va_list', loc)]
              | _ -> Console.fatal "Illegal call to %s: can't find necessary formals" va_start_name
            end
          | [Call (_, { enode = Lval (Var { vname = "__builtin_va_start" }, _) }, _, _)] ->
            Console.fatal "Illegal call to %s: wrong arguments or lvalue is present" va_start_name

          | [Call (None,
               { enode = Lval (Var { vname = "__builtin_va_arg" }, NoOffset) },
                   [({ enode = Lval ((Var va_list, NoOffset) as lva_list) } as eva_list); { enode = SizeOf t }; elval],
                   loc)]
            when unrollType va_list.vtype == va_list_type ->
            let lval =
              match (stripCasts elval).enode with
              | AddrOf lval -> lval
              | _ -> Console.fatal "Illegal call to %s: unrecognized internal representation of lval" va_arg_name
            in
            if not flat then
              let eva_arg_addr =
                mkCastT
                  ~force:false
                  ~overflow:Check
                  ~e:(new_exp ~loc @@ Lval (mkMem ~addr:(mkAddrOrStartOf ~loc lva_list) ~off:NoOffset))
                  ~oldt:va_list_type
                  ~newt:(const_ptr t)
              in
              [Set (lval, new_exp ~loc @@ Lval (mkMem ~addr:eva_arg_addr ~off:NoOffset), loc);
               Set (lva_list, increm eva_list 1, loc)]
            else
              let eva_list = mkCastT ~force:false ~overflow:Check ~e:eva_list ~oldt:va_list_type ~newt:(const_ptr t) in
              [Set (lval, new_exp ~loc (Lval (Mem eva_list, NoOffset)), loc);
               Set (lva_list, mkBinOp ~loc PlusPI eva_list (one ~loc), loc)]
          | [Call ( _, { enode = Lval (Var { vname = "__builtin_va_arg" }, _) }, _, _)] ->
            Console.fatal "Illegal call to %s: wrong arguments or lvalue is absent" va_arg_name

          | [Call (None,
                   { enode = Lval (Var { vname = "__builtin_va_end" } , NoOffset) },
                   [{ enode = Lval (Var va_list, NoOffset) }],
                   _)]
            when unrollType va_list.vtype == va_list_type ->
            []
          | [Call (_, { enode = Lval (Var { vname = "__builtin_va_end" }, _) }, _, _)] ->
            Console.fatal "Illegal call to %s: wrong arguments or lvalue is present" va_end_name

          | [Call (None,
                   { enode = Lval (Var { vname = "va_copy" | "__va_vopy" | "__builtin_va_copy" }, NoOffset) },
                   [{ enode = Lval ((Var vi_dst, NoOffset) as lva_dst) };
                    { enode = Lval (Var vi_src, NoOffset)} as va_src],
                   loc)]
            when unrollType vi_dst.vtype == va_list_type &&
                 unrollType vi_src.vtype == va_list_type ->
            [Set (lva_dst, va_src, loc)]
          | [Call (_,
                   { enode = Lval (Var { vname = "va_copy" | "__va_vopy" | "__builtin_va_copy" }, NoOffset) }, _, _)] ->
            Console.fatal "Illegal call to %s: wrong arguments or lvalue is present" va_copy_name

          | [Call (lv_opt,
                   ({ enode = Lval (Var { vtype = TFun (_, Some formals, false, _) }, NoOffset) } as f), args, loc)]
            when va_list_in formals ->
            let nformals = List.length formals - 1 in
            let actuals = List.drop nformals args in
            let current_func = Option.value_fatal ~in_:__LOC__ self#current_func in
            let vtmp = makeTempVar current_func ~name:"va_list" (va_list_var_type ~loc (List.length actuals)) in
            if not flat then
              let assignments =
                List.flatten @@
                  ListLabels.mapi
                    actuals
                    ~f:(fun i a ->
                      let va_arg_lval = Var vtmp, Index (integer ~loc i, NoOffset) in
                      let va_arg_type = Type.promote_argument_type (typeOf a) in
                      let va_arg_addr =
                        mkCast
                          ~force:false
                          ~overflow:Check
                          ~e:(new_exp ~loc (Lval va_arg_lval))
                          ~newt:(TPtr (va_arg_type, []))
                      in
                      let atmp = makeTempVar current_func ~name:"va_arg" (TPtr (va_arg_type, [])) in
                      [Call (Some (var atmp),
                             evar ~loc (Ast.Vi.Function.malloc () :> varinfo),
                             [sizeOf ~loc va_arg_type],
                             loc);
                       Set (va_arg_lval, evar atmp, loc);
                       Set (mkMem ~addr:va_arg_addr ~off:NoOffset, a, loc)])
          in
          assignments @ [Call (lv_opt, f, List.take nformals args @ [mkAddrOrStartOf ~loc (var vtmp)], loc)]
        else
          let init =
            Call (Some (var vtmp), evar ~loc (Ast.Vi.Function.malloc () :> varinfo),
                  [integer ~loc (List.length actuals)], loc)
          in
          let assignments =
            List.rev_map2
              (fun e a -> Set ((Mem (constFold false e), NoOffset), a, loc))
              (ListLabels.fold_left
                 List.(map (fun e -> Type.promote_argument_type (typeOf e)) actuals)
                 ~init:[]
                 ~f:(fun acc t ->
                      match acc with
                      | a :: _ ->
                        mkCastT
                          ~force:false
                          ~overflow:Check
                          ~e:(mkBinOp ~loc PlusPI a (one ~loc))
                          ~oldt:(typeOf a)
                          ~newt:(const_ptr t)
                          :: acc
                      | [] ->
                        [mkCastT
                           ~force:false
                           ~overflow:Check
                           ~e:(evar ~loc vtmp)
                           ~oldt:va_list_type
                           ~newt:(const_ptr t)]))
              (List.rev actuals)
          in
          [init] @ assignments @ [Call (lv_opt, f, List.take nformals args @ [evar ~loc vtmp], loc)]
      | [Call (_, { enode = Lval (Var { vtype = TFun (_, Some formals, _, _) }, off) }, _, _)]
        when va_list_in formals ->
        Console.fatal "Variadic function called with some offset in function lvalue: %a" Printer.pp_offset off

      | i -> i)

  method! vglob_aux =
    function
    | GVarDecl(_, { vname = "__builtin_va_start" }, _)
    | GVarDecl(_, { vname = "__builtin_va_arg" }, _)
    | GVarDecl(_, { vname = "__builtin_va_end" }, _)
    | GVarDecl(_, { vname = "__builtin_va_copy" }, _) ->
      ChangeTo []
    | _ -> DoChildren
  end

let rewrite_va_lists file =
  visitFramacFile (new va_list_rewriter ()) file;
  Framac.Ast.clear_last_decl ()

(* Jessie has trouble with Pre labels inside function contracts. *)
class pre_old_rewriter =
  object (self)

    inherit frama_c_inplace

    method! vbehavior =
      let label_rewriter ?(in_zone=false) ~pre_to =
        object
          inherit frama_c_inplace
          method! vlogic_label l =
            if Logic_label.equal l Logic_const.pre_label &&
               self#current_kinstr = Kglobal (* Do not rewrite Pre in stmt annot. *)
            then
              ChangeTo pre_to
            else if not in_zone && Logic_label.equal l Logic_const.post_label then
              ChangeTo Logic_const.here_label
            else
              DoChildren
        end
      in
      let pre_to_here_rewriter ?in_zone () = label_rewriter ~pre_to:Logic_const.here_label ?in_zone in
      let pre_to_old_rewriter ?in_zone () = label_rewriter ~pre_to:Logic_const.old_label ?in_zone in
      fun b ->
        let requires = visitFramacPredicates (pre_to_here_rewriter ()) b.b_requires in
        let assumes = visitFramacPredicates (pre_to_here_rewriter ()) b.b_assumes in
        let allocation =
          match b.b_allocation with
          | FreeAllocAny -> FreeAllocAny
          | FreeAlloc (free, alloc) ->
            let free =
              List.map
                (visitFramacIdTerm
                   (object
                     inherit frama_c_inplace
                     method! vlogic_label l =
                       if Logic_label.equal l Logic_const.here_label
                       then ChangeTo Logic_const.old_label
                       else DoChildren
                   end) %>
                 visitFramacIdTerm (pre_to_old_rewriter ()))
                free
            in
            let alloc =
              List.map
                (visitFramacIdTerm (pre_to_old_rewriter ()))
                alloc
            in
            FreeAlloc (free, alloc)
        in
        (* VP: 2012-09-20: signature of Cil.mk_behavior is utterly broken.
           We'll have to live with that for Oxygen, but this will change as
           soon as possible. *)
        let allocation = Some allocation in
        let assigns = visitFramacAssigns (pre_to_old_rewriter ~in_zone:true ()) b.b_assigns in
        let post_cond =
          mapNoCopy
            (fun (k, p as e) ->
               let p' = visitFramacIdPredicate (pre_to_old_rewriter ()) p in
               if p != p' then (k,p') else e)
            b.b_post_cond
        in
        let name = b.b_name in
        let b = mk_behavior ~name ~requires ~assumes ~assigns ~allocation ~post_cond () in
        ChangeTo b
end

let rewrite_pre_old = visitFramacFile (new pre_old_rewriter)

class unsupported_remover: frama_c_visitor =
object
  inherit frama_c_inplace
  method! vpredicate =
    function
    | Pseparated _ ->
      Console.warn_once
        "\\separated is not supported by Jessie. This predicate will be \
         ignored";
      ChangeTo Ptrue
    | _ -> DoChildren
end

let remove_unsupported = visitFramacFile (new unsupported_remover)

(****************************************************************************)
(* Add jessie_nondet_int () function for kmalloc.                           *)
(****************************************************************************)

let declare_jessie_nondet_int file =
  begin[@warning "-42"]
      Visit.attaching_globs
      {
        Visit.mk = fun ~attach ->
          object(self)
            inherit frama_c_inplace

            method private fix_vartype ~loc:(source, _) =
              function
              | Var vi, NoOffset ->
                if not (isPointerType vi.vtype) then
                  begin try
                    match (List.hd (Option.value_exn ~exn:Exit self#current_stmt).succs).skind with
                    | Instr (Set (_, { enode = CastE (t, _, _) }, _)) when isPointerType t ->
                      vi.vtype <- t
                    | _ -> raise Exit
                  with
                  | Failure "hd"
                  | Exit ->
                    (* Cannot use Common.unsupported with ~source due to argument erasure *)
                    Console.unsupported
                      ~current:true
                      ~source
                      "unable to recognize type of the allocation";
                  end
              | _ -> ()

            val mutable f_opt = None

            method! vinst =
              function
              | Call (Some lv, { enode = Lval (Var vi, NoOffset) }, _, loc) ->
                begin match Ast.Vi.Function.of_varinfo vi with
                | Some vi
                  when Ast.Vi.Function.(is_kmalloc vi || is_kzalloc vi) && f_opt = None ->
                  let f =
                    makeGlobalVar ~source:false Name.Logic_function.nondet_int @@
                      TFun (intType, Some [], false, [Attr ("extern", []); Attr ("const", [])])
                  in
                  f_opt <- Some f;
                  let fspec = empty_funspec () in
                  fspec.spec_behavior <-
                    [mk_behavior ~assigns:(Writes [Logic_const.(new_identified_term (tresult intType), FromAny)]) ()];
                  attach#global @@ GVarDecl (fspec, f, Location.unknown);
                  Globals.Functions.replace_by_declaration fspec f Location.unknown;
                  Annotations.register_funspec ~emitter:Emitters.jessie (Globals.Functions.get f);
                  self#fix_vartype ~loc lv;
                  SkipChildren
                | Some vi
                  when
                    Ast.Vi.Function.(is_malloc vi || is_kmalloc vi || is_kzalloc vi || is_realloc vi || is_calloc vi) ->
                  self#fix_vartype ~loc lv;
                  SkipChildren
                | Some _
                | None -> SkipChildren
                end
              | _ -> DoChildren
          end
      }
      file
  end

(*****************************************************************************)
(* Remove \from clauses from assigns (not used by Jessie)                    *)
(*****************************************************************************)

class assigns_from_remover =
  object
    inherit frama_c_inplace
    method! vdeps =
      function
      | From _ ->
        ChangeTo FromAny
      | FromAny -> SkipChildren
  end

let remove_assigns_from = visitFramacFile (new assigns_from_remover)

(*****************************************************************************)
(* Rewrite the C file for Jessie translation.                                *)
(*****************************************************************************)

let apply ~file f msg =
  Console.debug "Applying transformation: %s" msg;
  f file;
  Debug.check_exp_types file

let rewrite file =
  let apply = apply ~file in
  let open Config in
  (* Remove assigns \from clauses not used by Jessie but causing failures by void * dereferences *)
  apply remove_assigns_from "removing assigns \\from clauses";
  (* Insert declarations for kmalloc and jessie_nondet_int if necessary *)
  apply declare_jessie_nondet_int "inserting declaration for jessie_nondet_int (if necessary)";
  (* Add definitions for undefined composite tags. *)
  apply define_dummy_structs "defining dummy structs";
  (* Eliminate function pointers through dummy variables, assertions and if-then-else statements *)
  apply eliminate_fps "eliminating function pointers";
  (* Eliminate va_lists by replacing it with void * *)
  apply rewrite_va_lists "eliminating va_lists";
  (* Replace inline assembly with undefined function calls (and switches) *)
  apply asms_to_functions "replacing inline assembly with undefined function calls";
  (* Specialize block functions e.g. memcpy. *)
  if Specialize.get () then begin
    apply expand_kzallocs "expanding kzallocs to kmalloc+memset";
    apply specialize_blockfuns "using specialized versions for block functions (e.g. memcpy)";
  end;
  (* Rewrite alloca to malloc (currently unconditionally successful) *)
  apply rewrite_alloca "rewriting alloca";
  (* Retype bitwise operations in terms. *)
  apply retype_bw_ops_in_terms "retyping bitwise binary operations in terms";
  (* Expand assigns clauses and equalities for composite types. *)
  apply expand_composites "expanding assigns clauses and equality for composite types";
  (* adds a behavior named [name_of_default_behavior] to all functions if
     it does not already exist.
   *)
  apply (fun _ -> add_default_behaviors ()) "adding default behavior to all functions";
  (* Rename entities to avoid conflicts with Jessie predefined names.
     Should be performed before any call to [Cil.cvar_to_lvar] destroys
     sharing among logic variables.
  *)
  apply rename_entities "renaming entities";
  (* Replace addrof array with startof. *)
  apply replace_addrof_array "replacing addrof array with startof";
  (* Replace string constants by global variables. *)
  apply replace_string_constants "replacing string constants by global variables";
  (* Add invariant for global constants *)
  apply handle_global_consts "adding invariants for global constants";
  (* Put all global initializations in the [globinit] file. *)
  apply gather_initialization "putting all global initializations in the [globinit] file";
  (* Replace global compound initializations by equivalent statements. *)
  apply specialize_memset "using specialized versions of Frama_C_memset";
  (* Rewrite comparison of pointers into difference of pointers. *)
  apply rewrite_pre_old "rewriting Pre as Old in funspecs";
  (* Remove unsupported predicates *)
  apply remove_unsupported "checking if there are unsupported predicates"

(*
Local Variables:
compile-command: "make -C ."
End:
*)
