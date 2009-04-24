(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* $Id: jc_typing.ml,v 1.283 2009-04-24 09:32:25 melquion Exp $ *)

open Jc_stdlib
open Jc_env
open Jc_envset
open Jc_region
open Jc_ast
open Jc_fenv

open Jc_constructors
open Jc_pervasives
(*
open Jc_iterators
*)
open Jc_struct_tools

open Format

exception Typing_error of Loc.position * string

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter

let logic_type_table = Hashtbl.create 97

let exceptions_table = Hashtbl.create 97

let enum_types_table = Hashtbl.create 97

let structs_table = Hashtbl.create 97
let roots_table = Hashtbl.create 97

let mutable_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)
let committed_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)

let logic_functions_table = Hashtbl.create 97
let logic_functions_env = Hashtbl.create 97
let logic_constants_table = Hashtbl.create 97
let logic_constants_env = Hashtbl.create 97
let functions_table = Hashtbl.create 97
let functions_env = Hashtbl.create 97
let variables_table = Hashtbl.create 97
let variables_env = Hashtbl.create 97


type axiomatic_decl =
  | ABaxiom of Loc.position * string * Jc_env.label list * Jc_constructors.assertion

type axiomatic_data =
    {
      mutable axiomatics_defined_ids : logic_info list;
      mutable axiomatics_decls : axiomatic_decl list;
    }

let axiomatics_table = (Hashtbl.create 17 : (string, axiomatic_data) Hashtbl.t)

let field_tag_counter = ref 0

let create_mutable_field st =
  incr field_tag_counter;
  let name = "committed_"^st.jc_struct_info_name in
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = name;
    jc_field_info_final_name = Jc_envset.get_unique_name name;
    jc_field_info_type = boolean_type;
    jc_field_info_hroot = st.jc_struct_info_hroot;
    jc_field_info_struct = st;
    jc_field_info_rep = false;
    jc_field_info_bitsize = None;
  } in
  Hashtbl.add committed_fields_table st.jc_struct_info_name fi

let find_struct_info loc id =
  try
    let st,_ = Hashtbl.find structs_table id in st
  with Not_found ->
    typing_error loc "undeclared structure %s" id

let find_struct_root st =
  match st.jc_struct_info_hroot.jc_struct_info_root with
    | None -> raise Not_found
    | Some vi -> vi

let is_real t =
  match t with
    | JCTnative Treal -> true
    | _ -> false

let is_double t =
  match t with
    | JCTnative Tdouble -> true
    | _ -> false

let is_float t =
  match t with
    | JCTnative Tfloat -> true
    | _ -> false

let is_gen_float t =
  match t with
    | JCTnative (Tdouble | Tfloat) -> true
    | _ -> false


let is_boolean t =
  match t with
    | JCTnative Tboolean -> true
    | _ -> false

let is_numeric t =
  match t with
    | JCTnative (Tinteger | Treal) -> true
    | JCTenum _ -> true
    | _ -> false

let is_integer t =
  match t with
    | JCTnative Tinteger -> true
    | JCTenum _ -> true
    | _ -> false

let is_root_struct st = 
  match st.jc_struct_info_parent with None -> true | Some _ -> false

let lub_numeric_types t1 t2 =
  match t1,t2 with
    | JCTnative Tfloat, JCTnative Tfloat -> Tfloat
    | JCTnative (Tdouble | Tfloat), JCTnative (Tdouble | Tfloat) -> Tdouble
    | JCTnative Treal,_ | _,JCTnative Treal -> Treal
    | _ -> Tinteger

let rec substruct st = function
  | (JCtag(st', _)) as pc ->
      if st == st' then true else
        let vi = struct_root st and vi' = struct_root st' in
        (vi == vi' && (root_is_union vi))
        || 
        begin match st.jc_struct_info_parent with
          | None -> false
          | Some(p, []) -> substruct p pc
          | Some(p, _) -> assert false (* TODO *)
        end
  | JCroot vi ->
      struct_root st == vi

let rec superstruct st = function
  | JCtag(st', _) ->
      let vi' = struct_root st' in
      not (root_is_union vi') && substruct st' (JCtag(st,[]))
  | JCroot _vi ->
      false

let same_hierarchy st1 st2 =
  let vi1 = pointer_class_root st1 in
  let vi2 = pointer_class_root st2 in
  vi1 == vi2

let subtype ?(allow_implicit_cast=true) t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 ->
        t1=t2 ||
         (* integer is subtype of real *)
        (match t1,t2 with 
           | Tinteger, Treal -> true
	   | _ -> false)
    | JCTenum ri1, JCTenum ri2 -> 
        allow_implicit_cast ||
          (Num.ge_num ri1.jc_enum_info_min ri2.jc_enum_info_min &&
             Num.le_num ri1.jc_enum_info_max ri2.jc_enum_info_max)
    | JCTenum _, JCTnative Tinteger ->
        true
    | JCTnative Tinteger, JCTenum _ -> 
        allow_implicit_cast 
    | JCTlogic s1, JCTlogic s2 ->
        s1=s2
    | JCTpointer(JCtag(s1, []), _, _), JCTpointer(pc, _, _) -> 
        substruct s1 pc
    | JCTpointer(JCroot v1, _, _), JCTpointer(JCroot v2, _, _) ->
        v1 == v2
    | JCTnull, (JCTnull | JCTpointer _) ->
        true
    | _ ->
        false

let subtype_strict = subtype ~allow_implicit_cast:false

let mintype loc t1 t2 =
  try match t1,t2 with
    | JCTnative Tinteger, JCTnative Treal
    | JCTnative Treal, JCTnative Tinteger ->
        JCTnative Treal
    | JCTnative n1, JCTnative n2 ->
        if n1=n2 then t1 else raise Not_found
          (* TODO: integer is subtype of real *)
    | (JCTenum _ | JCTnative Tinteger), (JCTenum _| JCTnative Tinteger) ->
        Jc_pervasives.integer_type
    | JCTlogic s1, JCTlogic s2 ->
        if s1=s2 then t1 else raise Not_found
    | JCTpointer(JCtag(s1, []), _, _), JCTpointer(pc, _, _)
        when substruct s1 pc ->
        t2
    | JCTpointer(pc, _, _), JCTpointer(JCtag(s1, []), _, _)
        when substruct s1 pc ->
        t1
    | JCTpointer(JCroot v1, _, _), JCTpointer(JCroot v2, _, _) ->
        if v1 == v2 then t1 else raise Not_found
    | JCTnull, JCTnull -> JCTnull
    | JCTnull, JCTpointer _ -> t2
    | JCTpointer _, JCTnull -> t1       
    | JCTany, t | t, JCTany -> t
    | JCTpointer(JCtag(_, _::_), _, _), JCTpointer _
    | JCTpointer _, JCTpointer(JCtag(_, _::_), _, _) -> assert false
        (* TODO: parameterized type *)
    | _ -> raise Not_found
  with Not_found ->
    typing_error loc "incompatible types: %a and %a"
      print_type t1 print_type t2

let unit_expr e =
  if e#typ = unit_type then e else 
    new expr_with ~typ:unit_type ~region:dummy_region ~original_type:e#typ e

let same_type_no_coercion t1 t2 = 
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTenum ei1, JCTenum ei2 -> ei1.jc_enum_info_name = ei2.jc_enum_info_name
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | JCTpointer(pc1,_,_), JCTpointer(pc2,_,_) -> 
        pointer_class_root pc1 == pointer_class_root pc2
    | JCTnull, JCTnull -> true
    | JCTnull, JCTpointer _
    | JCTpointer _, JCTnull -> true
    | _ -> false

let comparable_types t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTenum _, JCTenum _ -> true
    | JCTenum _, JCTnative Tinteger -> true
    | JCTnative Tinteger, JCTenum _ -> true
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | JCTpointer(pc1,_,_), JCTpointer(pc2,_,_) -> 
        pointer_class_root pc1 == pointer_class_root pc2
    | JCTnull, JCTnull -> true
    | JCTnull, JCTpointer _
    | JCTpointer _, JCTnull -> true
    | _ -> false


let rec list_assoc_name f id l =
  match l with
    | [] -> raise Not_found
    | fi::r -> 
        if (f fi) = id then fi
        else list_assoc_name f id r


let rec find_field_struct loc st allow_mutable = function
  | ("mutable" | "committed") as x ->
      if allow_mutable && !Jc_common_options.inv_sem = InvOwnership then
        let table =
          if x = "mutable" then mutable_fields_table
          else committed_fields_table
        in
        Hashtbl.find table (root_name st)
      else typing_error loc "field %s cannot be used here" x
  | f ->
      try
        list_assoc_name
          (fun f -> f.jc_field_info_name) f st.jc_struct_info_fields
      with Not_found ->
        match st.jc_struct_info_parent with
          | None -> 
              raise Not_found
(*              typing_error loc "no field %s in structure %s" 
                f st.jc_struct_info_name*)
          | Some(st, _) -> find_field_struct loc st allow_mutable f
let find_field_struct loc st allow_mutable f =
  try find_field_struct loc st allow_mutable f
  with Not_found ->
    typing_error loc "no field %s in structure %s" f st.jc_struct_info_name

let find_field loc ty f allow_mutable =
  match ty with
    | JCTpointer(JCtag(st, _), _, _) -> find_field_struct loc st allow_mutable f
    | JCTpointer(JCroot _, _, _)
    | JCTnative _ 
    | JCTenum _
    | JCTlogic _
    | JCTnull
    | JCTany | JCTtype_var _ ->
        typing_error loc "not a structure type"

let find_fun_info id = Hashtbl.find functions_env id

let find_logic_info id = Hashtbl.find logic_functions_env id

(* types *)

let type_type t =
  match t#node with
    | JCPTnative n -> JCTnative n
    | JCPTpointer (id, _, a, b) -> 
        (* first we try the most precise type (the tag) *)
        begin try
          let st, _ = Hashtbl.find structs_table id in
          JCTpointer(JCtag(st, []), a, b)
        with Not_found ->
          try
            let vi = Hashtbl.find roots_table id in
            JCTpointer(JCroot vi, a, b)
          with Not_found ->
            typing_error t#pos "unknown type or tag: %s" id
        end
    | JCPTidentifier id -> 
        try
          let _ = Hashtbl.find logic_type_table id in
          JCTlogic id
        with Not_found ->
          try
            let (ri (* ,_,_,_ *)) = Hashtbl.find enum_types_table id in
            JCTenum ri
          with Not_found ->
            typing_error t#pos "unknown type %s" id

let unary_op (t: [< operator_type]) (op: [< unary_op]) = op, t

let bin_op (t: [< operator_type]) (op: [< bin_op]) = op, t

(******************************************************************************)
(*                                  Patterns                                  *)
(******************************************************************************)

(* constants *)

let const c =
  match c with
    | JCCvoid -> unit_type,dummy_region,c
    | JCCinteger _ -> integer_type,dummy_region,c
    | JCCreal _ -> real_type,dummy_region,c
    | JCCboolean _ -> boolean_type, dummy_region, c
    | JCCnull -> null_type,Region.make_var JCTnull "null",c
    | JCCstring _ -> string_type,dummy_region,c


let valid_pointer_type st =
  JCTpointer(st, Some (Num.num_of_int 0), Some (Num.num_of_int 0))

(* ety = expected type *)
(* env: the variables already bound *)
(* vars: the var_info to use if encountering a given variable *)
(* Return: (vars, pat) where:
     vars is the environment of the binders of the pattern
     pat is the typed pattern. *)
let rec pattern env vars pat ety =
  let get_var ety id =
    let id = id#name in
    if List.mem_assoc id env then
      typing_error pat#pos
        "the variable %s appears twice in the pattern" id;
    try
      StringMap.find id vars
    with Not_found ->
      let vi = var ety id in
      vi.jc_var_info_assigned <- true;
      vi
  in
  let tpn, ty, newenv = match pat#node with
    | JCPPstruct(id, lpl) ->
        let pc = match ety with
          | JCTpointer(pc, _, _) -> pc
          | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull | JCTany
          | JCTtype_var _ ->
              typing_error pat#pos
                "this pattern doesn't match a structure nor a variant"
        in
        (* tag *)
        let st = find_struct_info id#pos id#name in
        if not (substruct st pc) then
          typing_error id#pos
            "tag %s is not a subtag of %s"
            st.jc_struct_info_name (Jc_output_misc.pointer_class pc);
        (* fields *)
        let env, tlpl = List.fold_left
          (fun (env, acc) (l, p) ->
             let fi = find_field_struct l#pos st false l#name in
             let env, tp = pattern env vars p fi.jc_field_info_type in
             env, (fi, tp)::acc)
          (env, []) lpl
        in
        JCPstruct(st, List.rev tlpl), valid_pointer_type (JCtag(st, [])), env
    | JCPPvar id ->
        let vi = get_var ety id in
        JCPvar vi, ety, (id#name, vi)::env
    | JCPPor(p1, p2) ->
        let _, tp1 = pattern env vars p1 ety in
        let vars = pattern_vars vars tp1 in
        let env, tp2 = pattern env vars p2 ety in
        JCPor(tp1, tp2), ety, env
    | JCPPas(p, id) ->
        let env, tp = pattern env vars p ety in
        let vi = get_var (tp#typ) id in
        JCPas(tp, vi), ety, (id#name, vi)::env
    | JCPPany ->
        JCPany, ety, env
    | JCPPconst c ->
        let ty, _, c = const c in
        if not (subtype_strict ty ety) then
          typing_error pat#pos
            "type %a is not a subtype of %a" print_type ty print_type ety;
        JCPconst c, ety, env
  in newenv, new pattern ~typ:ty ~pos:pat#pos tpn
let pattern = pattern [] StringMap.empty

(******************************************************************************)
(*                                   Terms                                    *)
(******************************************************************************)

let num_op (op: [< `Badd | `Bsub | `Bmul | `Bdiv | `Bmod]) = op, Tinteger

let num_un_op t (op: [< `Uminus | `Ubw_not | `Unot]) e =
  match op with
    | `Unot
    | `Uminus
    | `Ubw_not -> JCTunary((unary_op t op :> unary_op * 'a),e)

let make_logic_unary_op loc (op : Jc_ast.unary_op) e2 =
  let t2 = e2#typ in
  match op with
    | `Unot -> 
	if is_boolean t2 then
	  t2, dummy_region, num_un_op (operator_of_native Tboolean) op  e2
	else
          typing_error loc "boolean expected"
    | ((`Uminus | `Ubw_not) as x) -> 
        if is_numeric t2 then
          let t = lub_numeric_types t2 t2 in
          JCTnative t,dummy_region,num_un_op (operator_of_native t) x e2
        else
          typing_error loc "numeric type expected"
(*    | `Upostfix_dec | `Upostfix_inc | `Uprefix_dec | `Uprefix_inc ->
        typing_error loc "pre/post incr/decr not allowed as logical term"*)

(* [term_coerce t1 t2 e] applies coercion to expr e of type t1 to t2 *)
let term_coerce t1 t2 e =
  let tn1 =
    match t1 with
      | JCTenum ri -> Tinteger
      | JCTnative t -> t
      | _ -> assert false
  in
  match tn1,t2 with
    | Tinteger, Treal -> 
	begin
	  match e#node with
	    | JCTconst (JCCinteger n) ->  
		new term
		  ~typ:real_type
		  ~region:e#region
		  ~mark:e#mark
		  ~pos:e#pos
		  (JCTconst(JCCreal (n^".0")))
	    | _ ->
		let app = {
		  jc_app_fun = real_of_integer;
		  jc_app_args = [e];
		  jc_app_region_assoc = [];
		  jc_app_label_assoc = [];
		} in
		new term
		  ~typ:real_type
		  ~region:e#region
		  ~mark:e#mark
		  ~pos:e#pos
		  (JCTapp app)
	end
    | _ -> e

let logic_bin_op (t : [< operator_type ]) (op : [< bin_op]) : term_bin_op =
  bin_op t op
(*
  match t,op with
    | _, BPgt -> gt_int
    | _, BPlt -> lt_int
    | _, BPge -> ge_int
    | _, BPle -> le_int
    | _, BPeq -> eq
    | _, BPneq -> neq
    | Tinteger, BPadd -> add_int
    | Treal, BPadd -> add_real
    | _, BPsub -> sub_int
    | _, BPmul -> mul_int
    | _, BPdiv -> div_int
    | _, BPmod -> mod_int
    | Tboolean, BPland -> band 
    | Tboolean, BPlor -> bor
        (* not allowed as expression op *)
    | _,BPimplies -> assert false
    | Tunit,_ -> assert false
    | _ -> assert false
*)

let make_logic_bin_op loc (op: bin_op) e1 e2 =
  let t1 = e1#typ and t2 = e2#typ in
  match op with
    | `Bgt | `Blt | `Bge | `Ble ->
        if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          boolean_type,dummy_region,
          JCTbinary(term_coerce t1 t e1, logic_bin_op (operator_of_native t) op, 
                     term_coerce t2 t e2)
        else
          typing_error loc "numeric types expected for >, <, >= and <="
    | `Beq | `Bneq ->
        if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          boolean_type,dummy_region,
          JCTbinary(term_coerce t1 t e1, logic_bin_op (operator_of_native t) op,
                     term_coerce t2 t e2)
        else if is_pointer_type t1 && is_pointer_type t2
	  && (comparable_types t1 t2) 
	then
          boolean_type,dummy_region,
          JCTbinary(e1,logic_bin_op `Pointer op,e2)
        else
          typing_error loc "numeric or pointer types expected for == and !="
    | `Badd ->
        if is_pointer_type t1 && is_integer t2 then
          t1, e1#region, JCTshift(e1, term_coerce t2 Tinteger e2)
        else if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t,dummy_region,
           JCTbinary(term_coerce t1 t e1,
                     logic_bin_op (operator_of_native t) op,
                     term_coerce t2 t e2))
        else
          typing_error loc "unexpected types for +"
    | `Bsub ->
        if is_pointer_type t1 && is_integer t2 then
          let _, _, te = make_logic_unary_op loc `Uminus e2 in
          let e2 = new term_with ~node:te e2 in
          t1,e1#region,JCTshift(e1, term_coerce t2 Tinteger e2)
        else if 
          is_pointer_type t1 && is_pointer_type t2 
          && comparable_types t1 t2 
        then
          (integer_type,dummy_region, 
           JCTbinary(e1, bin_op `Pointer `Bsub, e2))
        else if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t,
           dummy_region,
           JCTbinary(term_coerce t1 t e1,
                     logic_bin_op (operator_of_native t) op, 
                     term_coerce t2 t e2))
        else
          typing_error loc "unexpected types for -"
    | `Bmul | `Bdiv | `Bmod | `Bbw_and | `Bbw_or | `Bbw_xor 
    | `Blogical_shift_right | `Barith_shift_right | `Bshift_left ->
        if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t,dummy_region,
           JCTbinary(term_coerce t1 t e1,
                     logic_bin_op (operator_of_native t) op,
                     term_coerce t2 t e2))
        else typing_error loc "numeric types expected for *, / and %%"
    | `Bland | `Blor -> 
        let t=
          match (t1,t2) with
            | JCTnative t1, JCTnative t2 ->
                begin
                  match (t1,t2) with
                    | Tboolean,Tboolean -> Tboolean
                    | _ -> assert false (* TODO *)
                end
            | _ ->
                typing_error loc "booleans expected"
        in
        JCTnative t,
        dummy_region,
        JCTbinary(e1, logic_bin_op (operator_of_native t) op, e2)

        (* not allowed as term op *)
    | `Bimplies | `Biff -> assert false
    | `Bconcat -> assert false (* TODO *)


(** Check that used logic labels appear in the environment,
and add the current [label] to the node in [jc_nexpr_label].
[env] is the list of valid labels.
[result_label] is the expected label for [\result].
However, [label] might be changed by the "\at" construction. *)
let rec type_labels env ~result_label label e =
  let check e x =
    if not (List.mem x env) then
      typing_error e#pos "label `%a' not found" Jc_output_misc.label x
  in
  let iter_subs ?(env=env) label =
    List.iter
      (fun e -> ignore (type_labels env ~result_label label e))
      (Jc_iterators.INExpr.subs e)
  in
  e#set_label label;
  match e#node with
    | JCNEconst _ | JCNEderef _ | JCNEbinary _
    | JCNEunary _ | JCNEassign _ | JCNEinstanceof _ | JCNEcast _
    | JCNEif _ | JCNEoffset _ | JCNEaddress _ | JCNEbase_block _
    | JCNEalloc _ | JCNEfree _ | JCNElet _
    | JCNEassert _ | JCNEloop _ | JCNEreturn _ | JCNEtry _
    | JCNEthrow _ | JCNEpack _ | JCNEunpack _ | JCNEmatch _ | JCNEquantifier _
    | JCNEmutable _ | JCNEeqtype _ | JCNEsubtype _ | JCNErange _ -> 
        iter_subs label;
        env
    | JCNEvar id ->
	if id = "\\result" then
	  begin match label,result_label with
	    | Some lab1, Some lab2 ->
		if lab1 <> lab2 then
		  typing_error e#pos "\\result not allowed here"
	    | None, _ 
	    | _, None -> typing_error e#pos "\\result not allowed here"
	  end;
	env
    | JCNEcontract(req,dec,behs,e) ->
	let _ = type_labels_opt env ~result_label:None (Some LabelHere) req in
	let _ = type_labels_opt env ~result_label:None (Some LabelHere) dec in
	List.iter (behavior_labels env) behs;
	type_labels env ~result_label None e
    | JCNEapp(_, l, _) ->
        List.iter (check e) l;
        iter_subs label;
        env
    | JCNEold _ ->
        check e LabelOld;
        iter_subs (Some LabelOld);
        env
    | JCNEat(_, l) ->
        check e l;
        iter_subs (Some l);
        env
    | JCNEblock el ->
        List.fold_left
          (fun env e -> type_labels env ~result_label label e)
          env el
    | JCNElabel(lab, _) ->
        let lab = {
          label_info_name = lab;
          label_info_final_name = lab;
          times_used = 0;
        } in
        let env = (LabelName lab)::env in
        iter_subs ~env label;
        env

and type_labels_opt env ~result_label label e =
  match e with
    | None -> env
    | Some e -> type_labels env ~result_label label e
	
and behavior_labels env 
    (loc,id,throws,assumes,requires,assigns,ensures) =
  let here = Some LabelHere in
  let _ = type_labels_opt env ~result_label:None here assumes in
  let _ = type_labels_opt env ~result_label:None here requires in
  let env = LabelOld :: LabelPost :: env in
  Option_misc.iter
    (fun (_,a) ->
       List.iter 
	 (fun e -> 
	    ignore(type_labels env 
		     ~result_label:(Some LabelPost) (Some LabelOld) e)) a)
    assigns;
  let _ = type_labels env ~result_label:here here ensures in
  ()

let type_labels env ~result_label label e =
  ignore (type_labels env ~result_label label e)

let get_label e =
  match e#label with
    | None -> typing_error e#pos "a memory state is needed here (\\at missing?)"
    | Some l -> l

let label_assoc loc id cur_label fun_labels effective_labels =
  match cur_label, fun_labels, effective_labels with
    | Some l, [lf], [] -> [lf,l]
    | _ ->
	try
	  List.map2
	    (fun l1 l2 -> (l1,l2))
	    fun_labels effective_labels
	with Invalid_argument _ ->
	  typing_error loc 
	    "wrong number of labels for %s (expected %d, got %d)" id (List.length fun_labels) (List.length effective_labels)
	  
let rec term env e =
  let ft = term env in
  let lab = ref "" in
  let label () = get_label e in
  let t, tr, te = match e#node with
    | JCNEconst c ->
        let t, tr, c = const c in t, tr, JCTconst c
    | JCNElabel(l, e1) ->
        let te1 = ft e1 in
        lab := l;
        te1#typ, te1#region, te1#node
    | JCNEvar id ->
	begin try 
          let vi =
            try List.assoc id env 
	    with Not_found -> Hashtbl.find variables_env id
          in
          vi.jc_var_info_type, vi.jc_var_info_region, JCTvar vi
	with Not_found ->
	  let pi = 
            try Hashtbl.find logic_functions_env id with Not_found ->
              typing_error e#pos "unbound term identifier %s" id
	  in
          let app = {
            jc_app_fun = pi;
            jc_app_args = [];
            jc_app_region_assoc = [];
            jc_app_label_assoc = [];
          } in
	  let ty = 
	    match pi.jc_logic_info_result_type with
	      | Some t -> t
	      | None -> assert false (* check it is a function *)
	  in
	  ty, Region.make_var ty pi.jc_logic_info_name, JCTapp app
	end
    | JCNEderef(e1, f) ->
        let te1 = ft e1 in
        let fi = find_field e#pos te1#typ f true in
        fi.jc_field_info_type,
        Region.make_field te1#region fi,
        JCTderef(te1, label (), fi)
    | JCNEbinary(e1, op, e2) ->
        make_logic_bin_op e#pos op (ft e1) (ft e2)
    | JCNEunary(op, e1) ->
        make_logic_unary_op e#pos op (ft e1)
    | JCNEapp(id, labs, args) ->
        begin try
(* Yannick: no need for different rule for const logic *)
(*           if List.length args = 0 then *)
(*             let vi = Hashtbl.find logic_constants_env id in *)
(*             vi.jc_var_info_type, vi.jc_var_info_region, JCTvar vi *)
(*           else *)
	    begin
            let pi = find_logic_info id in
            let tl =
              try
                List.map2
                  (fun vi e ->
                     let ty = vi.jc_var_info_type in
                     let te = ft e in
                     if subtype_strict te#typ ty then te
                     else
                       typing_error e#pos 
                         "type %a expected instead of %a" 
                         print_type ty print_type te#typ) 
                  pi.jc_logic_info_parameters args
              with  Invalid_argument _ ->
                typing_error e#pos 
                  "wrong number of arguments for %s" id
            in
            let ty = match pi.jc_logic_info_result_type with
              | None ->
                  typing_error e#pos
                    "the logic info %s is a predicate; it should be \
used as an assertion, not as a term" pi.jc_logic_info_name
              | Some ty -> ty
	    in
            let label_assoc = 
	      label_assoc e#pos id e#label pi.jc_logic_info_labels labs 
	    in
            let app = {
              jc_app_fun = pi;
              jc_app_args = tl;
              jc_app_region_assoc = [];
              jc_app_label_assoc = label_assoc;
            } in
            ty, Region.make_var ty pi.jc_logic_info_name, JCTapp app
          end
        with Not_found ->
          typing_error e#pos "unbound logic function identifier %s" id
        end
    | JCNEinstanceof(e1, t) ->
        boolean_type,
        dummy_region,
        JCTinstanceof(ft e1, label (), find_struct_info e#pos t)
    | JCNEcast(e1, t) ->
        let te1 = ft e1 in
	let ty = type_type t in
	begin match ty with
	  | JCTnative Tinteger ->
	      if is_real te1#typ then
		integer_type, te1#region, JCTreal_cast(te1,Real_to_integer)
	      else if is_integer te1#typ then
		integer_type, te1#region, te1#node
	      else
		typing_error e#pos "bad cast to integer"
	  | JCTnative Treal ->
	      if is_integer te1#typ then
		real_type, te1#region, JCTreal_cast(te1,Integer_to_real)
	      else if is_real te1#typ then 
		real_type, te1#region, te1#node
	      else if is_double te1#typ then 
		real_type, te1#region, JCTreal_cast(te1,Double_to_real)
	      else if is_float te1#typ then 
		real_type, te1#region, JCTreal_cast(te1,Float_to_real)
	      else
		typing_error e#pos "bad cast to real"
	  | JCTnative Tdouble -> 
              if is_real te1#typ || is_integer te1#typ then 
                double_type, te1#region, JCTreal_cast(te1, Round_double Round_nearest_even)
	      else if is_double te1#typ then
		double_type, te1#region, te1#node
	      else if is_float te1#typ then 
		double_type, te1#region, te1#node
	      else
		typing_error e#pos "bad cast to double"	  
	  | JCTnative Tfloat -> 
              if is_real te1#typ || is_double te1#typ || is_integer te1#typ then 
                float_type, te1#region, JCTreal_cast(te1, Round_float Round_nearest_even)
	      else if is_float te1#typ then
		float_type, te1#region, te1#node
	      else
		typing_error e#pos "bad cast to float"

	  | JCTnative _ -> assert false (* TODO *)
	  | JCTenum ri ->
	      if is_integer te1#typ then
		JCTenum ri, dummy_region, JCTrange_cast(te1, ri)
	      else 
		(* CM je ne comprends pas ce cast de real vers enum 
		   if is_real te1#typ then
		let cast = NExpr.mkcast ~expr:e1 ~typ:integer_type () in
		let t = ft cast in
		  JCTenum ri, te1#region, JCTrange_cast(t, ri)
	      else
		*)
		typing_error e#pos "integer type expected"
	  | JCTpointer(JCtag(st,_),_,_) -> 
	      begin match te1#typ with
		| JCTpointer(st1, a, b) ->
		    if superstruct st st1 then
		      (te1#typ,
		       te1#region,
		       te1#node)
		    else if substruct st st1 then
		      (JCTpointer(JCtag(st, []), a, b),
		       te1#region,
		       JCTcast(te1, label (), st))
		    else if same_hierarchy (JCtag(st, [])) st1 then
		      typing_error e#pos "invalid cast"
		    else
		      (* bitwise cast *)
		      (Region.make_bitwise te1#region;
		       JCTpointer(JCtag(st, []), a, b),
		       te1#region,
		       JCTbitwise_cast(te1, label(), st))
		| JCTnull ->
		    (* bitwise cast *)
		    (Region.make_bitwise te1#region;
		     JCTpointer(JCtag(st,[]),None,None),
		     te1#region,
		     JCTbitwise_cast(te1, label(), st))
		| JCTnative _ | JCTlogic _ | JCTenum _ | JCTany
		| JCTtype_var _ ->
		    typing_error e#pos "only structures can be cast"
	      end
	  | JCTpointer (JCroot _, _, _)  -> assert false (* TODO *)
	  | JCTtype_var _|JCTlogic _|JCTany|JCTnull -> assert false (* TODO *)
	end
    | JCNEif(e1, e2, e3) ->
        let te1 = ft e1 and te2 = ft e2 and te3 = ft e3 in
        begin match te1#typ with
          | JCTnative Tboolean ->
              let t =
                let t2 = te2#typ and t3 = te3#typ in
                if subtype_strict t2 t3 then t3 else
                  if subtype_strict t3 t2 then t2 else
                    typing_error e#pos "incompatible result types"
              in
              t, te1#region, JCTif(te1, te2, te3)
          | _ -> typing_error e#pos "boolean expression expected"
        end
    | JCNEoffset(k, e1) ->
        let te1 = ft e1 in
        begin match te1#typ with
          | JCTpointer(JCtag(st, _), _, _) ->
              integer_type, dummy_region, JCToffset(k, te1, st)
          | JCTpointer(JCroot _, _, _) ->
              assert false (* TODO *)
          | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull | JCTany
          | JCTtype_var _ ->
              typing_error e#pos "pointer expected"
        end        
    | JCNEaddress(Addr_absolute,e1) ->
        let te1 = ft e1 in
        if is_integer te1#typ then
	  JCTnull, dummy_region, JCTaddress(Addr_absolute,te1)
	else
          typing_error e#pos "integer expected"
    | JCNEaddress(Addr_pointer,e1) ->
        let te1 = ft e1 in
        begin match te1#typ with
          | JCTpointer(JCtag(st, _), _, _) ->
              integer_type, dummy_region, JCTaddress(Addr_pointer,te1)
          | JCTpointer(JCroot _, _, _) ->
              assert false (* TODO *)
          | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull | JCTany
          | JCTtype_var _ ->
              typing_error e#pos "pointer expected"
        end        
    | JCNEbase_block(e1) ->
        let te1 = ft e1 in
        if is_pointer_type te1#typ then
	  JCTnull, dummy_region, JCTbase_block(te1)
	else
          typing_error e#pos "pointer expected"
    | JCNElet(pty, id, Some e1, e2) ->
        let te1 = ft e1 in
        let ty = match pty with
          | None -> te1#typ
          | Some pty ->
              let ty = type_type pty in
              if not (subtype te1#typ ty) then
                typing_error pty#pos
                  "inferred type is not a subtype of declared type"
              else
                ty
        in
        let vi = var ty id in
        let te2 = term ((id, vi)::env) e2 in
        te2#typ, te2#region, te2#node
    | JCNElet(Some pty, id, None, e2) ->
        let vi = var (type_type pty) id in
        let te2 = term ((id, vi)::env) e2 in
        te2#typ, te2#region, te2#node
    | JCNElet(None, _, None, _) ->
        typing_error e#pos "let with no initial value must have a type"
    | JCNEmatch(arg, pel) ->
        let targ = ft arg in
        let rty, tpel = match pel with
          | [] -> assert false (* should not be allowed by the parser *)
          | (p1, e1)::rem ->
              (* type the first item *)
              let penv, tp1 = pattern p1 targ#typ in
              let te1 = term (penv @ env) e1 in
              (* type the remaining items *)
              List.fold_left
                (fun (accrty, acctpel) (p, e2) ->
                   let penv, tp = pattern p targ#typ in
                   let te2 = term (penv @ env) e2 in
                   mintype e#pos accrty te2#typ,
                   (tp, te2)::acctpel)
                (te1#typ, [tp1, te1])
                (List.rev rem)
        in
        rty, targ#region, JCTmatch(targ, List.rev tpel)
    | JCNEold e1 ->
        let te1 = ft e1 in
        te1#typ, te1#region, JCTold te1
    | JCNEat(e1, lab) ->
        let te1 = ft e1 in
        te1#typ, te1#region, JCTat(te1, lab)
    | JCNEmutable(e, t) -> assert false (* TODO *)
    | JCNErange(Some e1, Some e2) ->
        let e1 = ft e1 and e2 = ft e2 in
        let t1 = e1#typ and t2 = e2#typ in
        assert (is_numeric t1 && is_numeric t2);
        let t = lub_numeric_types t1 t2 in
        JCTnative t, dummy_region, 
        JCTrange(Some (term_coerce t1 t e1),Some (term_coerce t2 t e2))
    | JCNErange(Some e, None) ->
        let e = ft e in
        let t = e#typ in
        assert (is_numeric t);
        t, dummy_region,JCTrange(Some e,None)
    | JCNErange(None, Some e) ->
        let e = ft e in
        let t = e#typ in
        assert (is_numeric t);
        t,dummy_region, JCTrange(None,Some e)
    | JCNErange(None, None) ->
        integer_type, dummy_region,JCTrange(None,None)
    (* Not terms: *)
    | JCNEassign _ | JCNEalloc _ | JCNEfree _ | JCNEblock _ | JCNEassert _
    | JCNEloop _ | JCNEreturn _ | JCNEtry _ | JCNEthrow _ | JCNEpack _
    | JCNEunpack _ | JCNEquantifier _ | JCNEcontract _ 
    | JCNEeqtype _ | JCNEsubtype _ ->
	typing_error e#pos "construction %a not allowed in logic terms"
	  Jc_noutput.expr e
  in
  new term
    ~typ: t
    ~region: tr
    ~mark: !lab
    ?label: e#label
    ~pos: e#pos
    te

(******************************************************************************)
(*                                 Assertions                                 *)
(******************************************************************************)

(*
let term label_env label env e =
  type_labels label_env label e;
  term env e
*)

(*  
let rel_unary_op loc op t =
  match op with
    | `Unot | `Ubw_not -> assert false
    | `Uminus | `Uplus -> 
        typing_error loc "not a proposition"
    | `Upostfix_dec | `Upostfix_inc | `Uprefix_dec | `Uprefix_inc ->
        typing_error loc "pre/post incr/decr not allowed as logical term"
*)

let rel_bin_op t (op: [< comparison_op]) =
  (bin_op t op :> pred_rel_op)
(*
  match t,op with
    | Tinteger,BPgt -> gt_int
    | Tinteger,BPlt -> lt_int
    | Tinteger,BPge -> ge_int
    | Tinteger,BPle -> le_int
    | _,BPeq -> eq
    | _,BPneq -> neq
    | _,(BPadd | BPsub | BPmul | BPdiv | BPmod) -> assert false
    | _,(BPland | BPlor | BPimplies | BPiff) -> assert false
    | _ -> assert false  (* TODO *)
*)

let make_and a1 a2 =
  match (a1#node, a2#node) with
    | (JCAtrue,_) -> a2
    | (_,JCAtrue) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCAand l1 , JCAand l2) -> new assertion(JCAand(l1@l2))
    | (JCAand l1 , _ ) -> new assertion(JCAand(l1@[a2]))
    | (_ , JCAand l2) -> new assertion(JCAand(a1::l2))
    | _ -> new assertion(JCAand [a1;a2])

let make_or a1 a2 =
  match (a1#node, a2#node) with
    | (JCAfalse,_) -> a2
    | (_,JCAfalse) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCAor l1 , JCAor l2) -> new assertion(JCAor(l1@l2))
    | (JCAor l1 , _ ) -> new assertion(JCAor(l1@[a2]))
    | (_ , JCAor l2) -> new assertion(JCAor(a1::l2))
    | _ -> new assertion(JCAor [a1;a2])

let make_rel_bin_op loc (op: [< comparison_op]) e1 e2 =
  let t1 = e1#typ and t2 = e2#typ in
  match op with
    | `Bgt | `Blt | `Bge | `Ble ->
        if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          JCArelation(term_coerce t1 t e1,
                      rel_bin_op (operator_of_native t) op,
                      term_coerce t2 t e2)
        else
          typing_error loc "numeric types expected for >, <, >= and <="
    | `Beq | `Bneq ->
        if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          JCArelation(term_coerce t1 t e1,
                      rel_bin_op (operator_of_native t) op,
                      term_coerce t2 t e2)
        else
          let t = operator_of_type (mintype loc t1 t2) in
          if comparable_types t1 t2 then 
            JCArelation(e1, rel_bin_op t op, e2)
          else
            typing_error loc "terms should have the same type for == and !="
(*        (* non propositional operators *)
    | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod | `Bbw_and | `Bbw_or | `Bbw_xor
    | `Blogical_shift_right | `Barith_shift_right | `Bshift_left 
        -> assert false
        (* already recognized as connectives *)
    | `Bland | `Blor -> assert false 
    | `Bimplies -> assert false
    | `Biff -> assert false*)

let tag env hierarchy t =
  let check_hierarchy loc st =
    if hierarchy <> "" &&
      root_name st != hierarchy then
        typing_error loc
          "this is in the hierarchy of %s, while it should be in the hierarchy \
of %s"
          (root_name st) hierarchy
  in
  let tt = match t#node with
    | JCPTtag id ->
        let st = find_struct_info id#pos id#name in
        check_hierarchy id#pos st;
        JCTtag st
    | JCPTbottom -> JCTbottom
    | JCPTtypeof tof ->
        let ttof = term env tof in
        match ttof#typ with
          | JCTpointer(JCtag(st, _), _, _) ->
              check_hierarchy tof#pos st;
              JCTtypeof (ttof, st)
          | _ -> typing_error tof#pos "tag pointer expression expected"
  in
  new tag ~pos:t#pos tt 

let rec assertion env e =
  let fa = assertion env in
  let ft = term env in
  let lab = ref "" in
  let label () = get_label e in
  let struct_for_tags ttag1 ttag2 = 
    match ttag1#node, ttag2#node with
      | JCTbottom, JCTbottom -> None
      | JCTbottom, JCTtag st
      | JCTtag st, JCTbottom
      | JCTbottom, JCTtypeof(_, st)
      | JCTtypeof(_, st), JCTbottom -> Some st
      | JCTtag st1, JCTtag st2
      | JCTtypeof(_, st1), JCTtag st2
      | JCTtag st1, JCTtypeof(_, st2)
      | JCTtypeof(_, st1), JCTtypeof(_, st2) ->
          if st1.jc_struct_info_hroot != st2.jc_struct_info_hroot then
            typing_error e#pos "the hierarchy %s and %s are different"
              (root_name st1)
              (root_name st2)
          else
            Some st1.jc_struct_info_hroot
  in
  let ta = match e#node with
    | JCNElabel(l, e) ->
        let te = fa e in
        lab := l;
        te#node
    | JCNEbinary(e1, (`Bland | `Blor | `Bimplies | `Biff as op), e2) ->
        let a1 = fa e1 and a2 = fa e2 in
        begin match op with
          | `Bland -> (make_and a1 a2)#node
          | `Blor -> (make_or a1 a2)#node
          | `Bimplies -> JCAimplies(a1, a2)
          | `Biff -> JCAiff(a1, a2)
        end
    | JCNEbinary(e1, (#comparison_op as op), e2) ->
        make_rel_bin_op e#pos op (ft e1) (ft e2)
    | JCNEunary(`Unot, e1) ->
        JCAnot(fa e1)
    | JCNEapp (id, labs, args) ->
        begin try
          let pi = find_logic_info id in
          let tl = try
            List.map2
              (fun vi e ->
                 let ty = vi.jc_var_info_type in
                 let te = ft e in
                 if subtype_strict te#typ ty then te
                 else
                   typing_error e#pos 
                     "type %a expected instead of %a" 
                     print_type ty print_type te#typ) 
              pi.jc_logic_info_parameters args
          with Invalid_argument _ ->
            typing_error e#pos "wrong number of arguments for %s" id
          in
	  let label_assoc =
		label_assoc e#pos id e#label pi.jc_logic_info_labels labs
	      in
          let app = {
            jc_app_fun = pi;
            jc_app_args = tl;
            jc_app_region_assoc = [];
            jc_app_label_assoc = label_assoc;
          } in
          JCAapp app
        with Not_found ->
          typing_error e#pos "unbound predicate identifier %s" id
        end
    | JCNEinstanceof(e1, t) -> 
        JCAinstanceof(ft e1, label (), find_struct_info e#pos t)
    | JCNEcast _ -> assert false (* TODO *)
    | JCNEif(e1,e2,e3) ->
        let te1 = ft e1 and te2 = fa e2 and te3 = fa e3 in
        begin
          match te1#typ with
            | JCTnative Tboolean ->
                JCAif(te1,te2,te3)
            | _ ->
                typing_error e1#pos 
                  "boolean expression expected"
        end
    | JCNElet _ -> assert false (* TODO *)
    | JCNEmatch(arg, pel) ->
        let targ = ft arg in
        let tpal = List.map
          (fun (pat, body) ->
             let vars, tpat = pattern pat targ#typ in
             let tbody = assertion (vars @ env) body in
             tpat, tbody)
          pel
        in
        JCAmatch(targ, tpal)
    | JCNEquantifier(q, ty, idl, e1) ->
        let ty = type_type ty in
        (make_quantifier q e#pos ty idl env e1)#node
    | JCNEold e1 ->
        JCAold(fa e1)
    | JCNEat(e1, lab) ->
        JCAat(fa e1, lab)
    | JCNEmutable(e, t) ->
        let te = ft e in
        let te_st = match te#typ with
          | JCTpointer(JCtag(st, _), _, _) -> st
          | _ -> typing_error e#pos "tag pointer expression expected"
        in
        let tt = tag env (root_name te_st) t in
        JCAmutable(te, te_st, tt)
    | JCNEeqtype(tag1, tag2) ->
        let ttag1 = tag env "" tag1 in
        let ttag2 = tag env "" tag2 in
	let st = struct_for_tags ttag1 ttag2 in
        JCAeqtype(ttag1, ttag2, st)
    | JCNEsubtype(tag1, tag2) ->
        let ttag1 = tag env "" tag1 in
        let ttag2 = tag env "" tag2 in
	let st = struct_for_tags ttag1 ttag2 in
        JCAsubtype(ttag1, ttag2, st)
    (* Boolean terms: *)
    | JCNEconst _ | JCNEvar _ | JCNEderef _ ->
        let t = ft e in
        begin match t#typ with
          | JCTnative Tboolean -> JCAbool_term t
          | _ -> typing_error e#pos "non boolean expression"
        end
    (* Not assertions: *)
    | JCNEoffset _ | JCNEaddress _ | JCNEbase_block _
    | JCNErange _ | JCNEassign _ | JCNEalloc _ | JCNEfree _
    | JCNEassert _ | JCNEblock _ | JCNEloop _ | JCNEreturn _ | JCNEtry _
    | JCNEthrow _ | JCNEpack _ | JCNEunpack _ | JCNEbinary _ | JCNEunary _ 
    | JCNEcontract _ ->
        typing_error e#pos "construction not allowed in logic assertions"
  in
  new assertion
    ~mark: !lab
    ?label: e#label
    ~pos: e#pos
    ta

and make_quantifier q loc ty idl env e : assertion =
  match idl with
    | [] -> assertion env e
    | id :: r ->
        let vi = var ty id#name in
        let env = (id#name, vi) :: env in
        let f = 
          JCAquantifier (q, vi, make_quantifier q loc ty r env e) 
        in
        new assertion ~pos:loc f

(******************************************************************************)
(*                                Expressions                                 *)
(******************************************************************************)

let loop_annot =
  let cnt = ref 0 in 
  fun ~behaviors ~free_invariant ~variant ->
    incr cnt;
    {
      jc_loop_tag = !cnt;
      jc_loop_behaviors = behaviors;
      jc_free_loop_invariant = free_invariant;
      jc_loop_variant = variant;
    }

let rec location_set env e =
  let ty,r,locs_node = match e#node with
    | JCNElabel(l,e) -> 
        assert false (* TODO *)
    | JCNEvar id ->
        let vi =
          try List.assoc id env with Not_found ->
            try Hashtbl.find variables_env id with Not_found ->
              typing_error e#pos "unbound identifier %s" id
        in
        begin match vi.jc_var_info_type with
          | JCTpointer _ ->
              vi.jc_var_info_type, vi.jc_var_info_region, JCLSvar vi
          | _ -> assert false
        end
    | JCNEbinary(e, `Badd, i) ->
	begin try
          let ty,tr,te = location_set env e in
	  let ti = term env i in
          begin match ty, ti#typ with 
            | JCTpointer(st,_,_), t2 when is_integer t2 ->
                begin match ti#node with
                  | JCTrange(t1,t2) -> ty,tr,JCLSrange(te,t1,t2)
                  | _ -> ty,tr,JCLSrange(te,Some ti,Some ti)
		      (* TODO ?
			 | _ -> ty,tr,JCLSshift(te,ti)
		      *)
                end
            | JCTpointer _, _ -> 
                typing_error i#pos "integer expected, %a found"
                  print_type ti#typ
            | _ -> 
                typing_error e#pos "pointer expected"
          end
	with Typing_error _ ->
          let t1 = term env e in
          let ty, tr, te = t1#typ, t1#region, t1 in
	  let ti = term env i in
          begin match ty, ti#typ with 
            | JCTpointer(st,_,_), t2 when is_integer t2 ->
                begin match ti#node with
                  | JCTrange(t1,t2) -> ty,tr,JCLSrange_term(te,t1,t2)
                  | _ -> ty,tr,JCLSrange_term(te,Some ti,Some ti)
		      (* TODO ?
			 | _ -> ty,tr,JCLSshift(te,ti)
		      *)
                end
            | JCTpointer _, _ -> 
                typing_error i#pos "integer expected, %a found"
                  print_type ti#typ
            | _ -> 
                typing_error e#pos "pointer expected"
          end
	end
    | JCNEbinary _ ->
        assert false
    | JCNEderef(ls, f) -> 
        let t,tr,tls = location_set env ls in
        let fi = find_field e#pos t f false in
        let fr = Region.make_field tr fi in
        fi.jc_field_info_type, fr, JCLSderef(tls, get_label e, fi, fr)   
    | JCNErange _ | JCNEeqtype _ | JCNEmutable _ | JCNEat _ | JCNEold _
    | JCNEquantifier _ | JCNEmatch _ | JCNEunpack _ | JCNEpack _ | JCNEthrow _
    | JCNEtry _ |JCNEreturn _ | JCNEloop _ |JCNEblock _ | JCNEassert _
    | JCNElet _ |JCNEfree _ | JCNEalloc _ | JCNEoffset _ | JCNEaddress _ 
    | JCNEif _ | JCNEcast _ | JCNEbase_block _
    | JCNEinstanceof _ | JCNEassign _ | JCNEapp _ | JCNEunary _
    | JCNEconst _ | JCNEcontract _ | JCNEsubtype _ ->
        typing_error e#pos "invalid memory location"
  in
  let locs = 
    new location_set
      ~pos: e#pos
      ~region:r
      ?label: e#label
      locs_node
  in ty,r,locs

let rec location env e =
  let ty,r,loc_node = match e#node with
    | JCNElabel(l, e) ->
        assert false (* TODO *)
    | JCNEvar id ->
        let vi =
          try List.assoc id env with Not_found ->
            try Hashtbl.find variables_env id with Not_found ->
              typing_error e#pos "unbound identifier %s" id
        in
        vi.jc_var_info_type, vi.jc_var_info_region, JCLvar vi
    | JCNEderef(ls, f) ->
	begin try
          let t, tr, tls = location_set env ls in
          let fi = find_field e#pos t f false in
          let fr = Region.make_field tr fi in
          fi.jc_field_info_type, fr, JCLderef(tls, get_label e, fi, fr)
	with Typing_error _ ->
          let t1 = term env ls in
          let fi = find_field e#pos t1#typ f false in
          let fr = Region.make_field t1#region fi in
          fi.jc_field_info_type, fr, JCLderef_term(t1, fi)
	end
    | JCNEat(e, lab) ->
        let t, tr, tl = location env e in
        t, tr, JCLat(tl, lab)
    | JCNErange _ | JCNEeqtype _ | JCNEmutable _ | JCNEold _
    | JCNEquantifier _ | JCNEmatch _ | JCNEunpack _ | JCNEpack _ | JCNEthrow _
    | JCNEtry _ | JCNEreturn _ | JCNEloop _ | JCNEblock _ | JCNEassert _
    | JCNElet _ | JCNEfree _ | JCNEalloc _ | JCNEoffset _ | JCNEaddress _ 
    | JCNEif _ | JCNEcast _ | JCNEbase_block _
    | JCNEinstanceof _ | JCNEassign _ | JCNEapp _ | JCNEunary _ | JCNEbinary _
    | JCNEconst _ | JCNEcontract _ | JCNEsubtype _ ->
        typing_error e#pos "invalid memory location"
  in
  let loc = 
    new location
      ~pos: e#pos
      ~region:r
      ?label: e#label
      loc_node
  in ty,r,loc
  
let behavior env vi_result (loc, id, throws, assumes, requires, assigns, ensures) =
  let throws,env_result = 
    match throws with
      | None -> None, (vi_result.jc_var_info_name,vi_result)::env 
      | Some id -> 
          try 
            let ei = 
              Hashtbl.find exceptions_table id#name 
            in
            let tei = match ei.jc_exception_info_type with
              | Some tei -> tei
              | None -> typing_error id#pos
                  "exception without value"
            in
            let vi = var tei "\\result" in
            vi.jc_var_info_final_name <- "result";
            Some ei, (vi.jc_var_info_name,vi)::env 
          with Not_found ->
            typing_error id#pos 
              "undeclared exception %s" id#name
  in
  let assumes = Option_misc.map (assertion env) assumes in
  (*
    let requires = Option_misc.map (assertion (Some "Here") env) requires in
  *)
  let assigns = 
    Option_misc.map 
      (fun (loc, l) -> 
         (loc, List.map 
            (fun a -> let _,_,tl = location env_result a in 
             (match tl#node with
                | JCLvar vi -> vi.jc_var_info_assigned <- true
                | _ -> ());
             tl) 
            l)) 
      assigns 
  in
  let b = {
    jc_behavior_throws = throws;
    jc_behavior_assumes = assumes;
    (*
      jc_behavior_requires = requires;
    *)
    jc_behavior_assigns = assigns;
    jc_behavior_ensures = assertion env_result ensures;
    jc_behavior_free_ensures = Assertion.mktrue () }
  in
  (*
    eprintf "lab,loc for ensures: \"%s\", %a@."
    b.jc_behavior_ensures.jc_assertion_label
    Loc.gen_report_position b.jc_behavior_ensures.jc_assertion_loc;
  *)
  (loc,id,b)
    

let loopbehavior env (names,inv,ass) = 
  (names,Option_misc.map (assertion env) inv,
     Option_misc.map 
       (fun (p,locs) -> 
	  List.map 
	    (fun l -> 
	       let _,_,tl = location env l in tl) locs) ass)

let make_unary_op loc (op : Jc_ast.unary_op) e2 =
  let t2 = e2#typ in
  match op with
(*    | `Uprefix_inc | `Upostfix_inc | `Uprefix_dec | `Upostfix_dec (*as op*) ->
        begin
          let t = if is_pointer_type t2 then t2 else
            JCTnative (lub_numeric_types t2 t2) in
          match e2#node with
            | JCEvar v ->
                v.jc_var_info_assigned <- true;
                t, v.jc_var_info_region,
                assert false (* JCEincr_local(incr_op op, v) *)
            | JCEderef(e,f) ->
                t, e2#region,
                assert false (* JCEincr_heap(incr_op op, e, f) *)
            | _ -> typing_error e2#pos "not an lvalue"
        end*)
    | `Unot as op -> 
        let t=
          match t2 with
            | JCTnative t2 ->
                begin
                  match t2 with
                    | Tboolean -> Tboolean
                    | _ -> assert false (* TODO *)
                end
            | _ ->
                typing_error loc "boolean expected"
        in (JCTnative t,dummy_region,
            JCEunary(unary_op (operator_of_native t) op, e2))
    | `Uminus -> 
        if is_numeric t2 || is_gen_float t2 then
          let t = lub_numeric_types t2 t2 in
          (JCTnative t,dummy_region,
           JCEunary(unary_op (operator_of_native t) op, e2))
        else
          typing_error loc "numeric type expected"
    | `Ubw_not -> 
        if is_numeric t2 then
          let t = lub_numeric_types t2 t2 in
          (JCTnative t,dummy_region,
           JCEunary(unary_op (operator_of_native t) op, e2))
        else
          typing_error loc "numeric type expected"

let coerce t1 t2 e =
  let tn1 =
    match t1 with
      | JCTenum ri -> Tinteger
      | JCTnative t -> t
      | _ -> assert false
  in
  match tn1, t2 with
    | Tinteger,Treal ->
	begin
	  match e#node with
	    | JCEconst (JCCinteger n) ->  
		new expr
		  ~typ:real_type
		  ~region:e#region
		  ~pos:e#pos
		  (JCEconst(JCCreal (n^".0")))
	    | _ ->
		new expr
		  ~typ: real_type
		  ~pos: e#pos
		  (JCEapp{
		     jc_call_fun = JCfun real_of_integer_;
		     jc_call_args = [e];
		     jc_call_region_assoc = [];
		     jc_call_label_assoc = [];
		   })
	end
    | _ -> e

let make_bin_op loc (op: operational_op) e1 e2 =
  let t1 = e1#typ and t2 = e2#typ in
  match op with
    | `Bgt | `Blt | `Bge | `Ble ->
        if is_numeric t1 && is_numeric t2 
	  || is_gen_float t1 && is_gen_float t2
	then
          let t = lub_numeric_types t1 t2 in
          (boolean_type, dummy_region,
           JCEbinary(coerce t1 t e1,
                     bin_op (operator_of_native t) op,
                     coerce t2 t e2))
        else
          typing_error loc "numeric types expected for <, >, <= and >="
    | `Beq | `Bneq as op ->
        if is_numeric t1 && is_numeric t2 
	  || is_gen_float t1 && is_gen_float t2
	then
          let t = lub_numeric_types t1 t2 in
          (boolean_type, dummy_region,
           JCEbinary(coerce t1 t e1,
                     bin_op (operator_of_native t) op,
                     coerce t2 t e2))
        else
          if t1 = boolean_type && t2 = boolean_type then
            (boolean_type, dummy_region, JCEbinary (e1, bin_op `Boolean op, e2))
          else
            if is_pointer_type t1 && is_pointer_type t2 &&
              comparable_types t1 t2 then
                (boolean_type, dummy_region,
                 JCEbinary(e1, bin_op `Pointer op, e2))
            else
              typing_error loc
                "numeric, boolean or pointer types expected for == and !="
    | `Badd as op  ->
        if is_pointer_type t1 && is_integer t2 then
          t1, e1#region, JCEshift(e1, coerce t2 Tinteger e2)
        else if is_numeric t1 && is_numeric t2 	  
	  || is_gen_float t1 && is_gen_float t2
	then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t,
           dummy_region,
           JCEbinary(coerce t1 t e1,
                     bin_op (operator_of_native t) op,
                     coerce t2 t e2))
        else
          typing_error loc "unexpected types for +"
    | `Bsub as op  ->
        if is_pointer_type t1 && is_integer t2 then
          let _,_,te = make_unary_op loc `Uminus e2 in
          let e2 = new expr_with ~node:te e2 in
          t1, e1#region, JCEshift(e1, coerce t2 Tinteger e2)
        else if 
          is_pointer_type t1 && is_pointer_type t2 
          && comparable_types t1 t2 
        then
          (integer_type, dummy_region,
           JCEbinary(e1, bin_op `Pointer `Bsub, e2))
        else if is_numeric t1 && is_numeric t2 
	  || is_gen_float t1 && is_gen_float t2
	then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t, dummy_region,
           JCEbinary(coerce t1 t e1,
                     bin_op (operator_of_native t) op,
                     coerce t2 t e2))
	else
          typing_error loc "unexpected types for -"
    | `Bmul | `Bdiv | `Bmod ->
        if is_numeric t1 && is_numeric t2 
	  || is_gen_float t1 && is_gen_float t2
	then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t,dummy_region,
           JCEbinary(coerce t1 t e1,
                     bin_op (operator_of_native t) op,
                     coerce t2 t e2))
        else
	  typing_error loc "numeric types expected for multiplicative operators"
    | `Bbw_and | `Bbw_or | `Bbw_xor ->
        if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t,dummy_region,
           JCEbinary(coerce t1 t e1,
                     bin_op (operator_of_native t) op,
                     coerce t2 t e2))
        else if is_boolean t1 && is_boolean t2 then
          (boolean_type, dummy_region,
           JCEbinary(e1,
                     bin_op (operator_of_native Tboolean) op,
                     e2))	  
        else 
	  typing_error loc "numeric types expected for bitwise operators"
    | `Blogical_shift_right | `Barith_shift_right | `Bshift_left as op  ->
        if is_numeric t1 && is_numeric t2 then
          let t = lub_numeric_types t1 t2 in
          (JCTnative t,dummy_region,
           JCEbinary(coerce t1 t e1,
                     bin_op (operator_of_native t) op,
                     coerce t2 t e2))
        else 
	  typing_error loc "numeric types expected for shift operators"
    | `Bland | `Blor as op -> 
        let t = match (t1, t2) with
          | JCTnative t1, JCTnative t2 ->
              begin match (t1, t2) with
                | Tboolean, Tboolean -> Tboolean
                | _ -> assert false (* TODO *)
              end
          | _ -> typing_error loc "booleans expected"
        in
        (JCTnative t,
         dummy_region,
         JCEbinary(e1, bin_op (operator_of_native t) op, e2))
    | `Bconcat -> assert false (* TODO *)


let reset_return_label, set_return_label, get_return_label =
  let has_label = ref false in
  (fun () -> has_label := false), 
  (fun () -> has_label := true), 
  (fun () -> !has_label)

let rec expr env e =
  let fe = expr env in
  let ft = term env in
  let lab = ref "" in
  let ty, region, typed_e = match e#node with
    (* old expressions *)
    | JCNEconst c ->
        let t, tr, tc = const c in t, tr, JCEconst tc
    | JCNElabel(l, e1) ->
        let te1 = fe e1 in
        lab := l;
        te1#typ, te1#region, te1#node
    | JCNEvar id ->
	begin try 
          let vi =
            try List.assoc id env 
	    with Not_found -> Hashtbl.find variables_env id
          in vi.jc_var_info_type, vi.jc_var_info_region, JCEvar vi
	with Not_found -> 
          let pi = 
	    try Hashtbl.find logic_functions_env id with Not_found -> 
              typing_error e#pos "unbound identifier %s" id
	  in
          let app = {
            jc_call_fun = JClogic_fun pi;
            jc_call_args = [];
            jc_call_region_assoc = [];
            jc_call_label_assoc = [];
          } in
	  let ty = 
	    match pi.jc_logic_info_result_type with
	      | Some r -> r
	      | None -> assert false (* check it is a function *)
	  in
	  ty, Region.make_var ty pi.jc_logic_info_name, JCEapp app
	end
	  
    | JCNEderef(e1, f) -> 
        let te1 = fe e1 in
        let fi = find_field e#pos te1#typ f false in
        fi.jc_field_info_type,
        Region.make_field te1#region fi,
        JCEderef(te1, fi)
    | JCNEbinary(e1, (#logical_op as op), e2) ->
        let te1 = fe e1 and te2 = fe e2 in
	(* boolean_type, dummy_region,  *)
	  begin match op with
	  | `Bland ->
	      (*
              JCEif(
                te1,
                te2,
                new expr ~typ:boolean_type (JCEconst(JCCboolean false))
              )
	      *)
	      make_bin_op e#pos `Bland te1 te2
          | `Blor ->
              (*
		JCEif(
                te1,
                new expr ~typ:boolean_type (JCEconst(JCCboolean true)),
                te2
              )
	      *)
	      make_bin_op e#pos `Blor te1 te2
	  | `Bimplies | `Biff ->
	      typing_error e#pos "unexpected operator in expression"
	end
    | JCNEbinary(e1, (#operational_op as op), e2) ->
        make_bin_op e#pos op (fe e1) (fe e2)
    | JCNEunary(op, e1) ->
        make_unary_op e#pos op (fe e1)
    | JCNEapp(id, labs, args) -> 
        begin try
          let fi = find_fun_info id in
          assert (labs = []);
          let tl = try
            List.map2
              (fun (valid,vi) e ->
                 let ty = vi.jc_var_info_type in
                 let te = fe e in
                 if subtype te#typ ty then te
                 else
                   typing_error e#pos "type %a expected instead of %a" 
                     print_type ty print_type te#typ) 
              fi.jc_fun_info_parameters args
          with Invalid_argument _ ->
            typing_error e#pos "wrong number of arguments for %s" id
          in
          let ty = fi.jc_fun_info_result.jc_var_info_type in
          ty,
          Region.make_var ty fi.jc_fun_info_name,
          JCEapp {
            jc_call_fun = JCfun fi;
            jc_call_args = tl;
            jc_call_region_assoc = [];
            jc_call_label_assoc = [];
          }
        with Not_found -> try
(* Yannick: no need for different rule for const logic *)
(*           if List.length args = 0 then *)
(*             let vi = Hashtbl.find logic_constants_env id in *)
(*             vi.jc_var_info_type, vi.jc_var_info_region, JCEvar vi *)
(*           else *)
	  begin
            let pi = find_logic_info id in
            let tl =
              try
                List.map2
                  (fun vi e ->
                     let ty = vi.jc_var_info_type in
                     let te = fe e in
                     if subtype_strict te#typ ty then te
                     else
                       typing_error e#pos 
                         "type %a expected instead of %a" 
                         print_type ty print_type te#typ) 
                  pi.jc_logic_info_parameters args
              with  Invalid_argument _ ->
                typing_error e#pos 
                  "wrong number of arguments for %s" id
            in
            let ty = match pi.jc_logic_info_result_type with
              | None ->
                  typing_error e#pos
                    "the logic info %s is a predicate; it should be \
used as an assertion, not as a term" pi.jc_logic_info_name
              | Some ty -> ty
            in
            let label_assoc = 
              match e#label, pi.jc_logic_info_labels, labs with
                | Some l, [lf], [] -> [lf,l]
                | _ ->
                    try
                      List.map2
                        (fun l1 l2 -> (l1,l2))
                        pi.jc_logic_info_labels labs
                    with Invalid_argument _ ->
                      typing_error e#pos 
                        "wrong number of labels for %s" id
            in
            let app = {
              jc_call_fun = JClogic_fun pi;
              jc_call_args = tl;
              jc_call_region_assoc = [];
              jc_call_label_assoc = label_assoc;
            } in
            ty, Region.make_var ty pi.jc_logic_info_name, JCEapp app
          end
        with Not_found ->
          typing_error e#pos "unbound function or logic function identifier %s" id
        end
    | JCNEassign(e1, e2) -> 
        let te1 = fe e1 and te2 = fe e2 in
        let t1 = te1#typ and t2 = te2#typ in
        if subtype t2 t1 then 
	  begin
	    let te2 =
	      match t2 with
		| JCTnull -> new expr_with ~typ:t1 te2
		| _ -> te2
	    in
            match te1#node with
              | JCEvar v ->
                  v.jc_var_info_assigned <- true;
                  t1, te2#region, JCEassign_var(v, te2)
              | JCEderef(e, f) ->
                  t1, te2#region, JCEassign_heap(e, f, te2)
              | _ -> typing_error e1#pos "not an lvalue"
	  end
        else
          typing_error e2#pos 
            "type '%a' expected in assignment instead of '%a'"
            print_type t1 print_type t2
    | JCNEinstanceof(e1, t) -> 
        let te1 = fe e1 in
        let st = find_struct_info e#pos t in
        boolean_type, dummy_region, JCEinstanceof(te1, st)
    | JCNEcast(e1, t) -> 
       let te1 = fe e1 in
	let ty = type_type t in
	begin match ty with
	  | JCTnative Tinteger ->
	      if is_real te1#typ then
		integer_type, te1#region, JCEreal_cast(te1,Real_to_integer)
	      else if is_integer te1#typ then
		integer_type, te1#region, te1#node
	      else
		typing_error e#pos "bad cast to integer"
	  | JCTnative Treal ->
	      if is_integer te1#typ then
		real_type, te1#region, JCEreal_cast(te1,Integer_to_real)
	      else if is_real te1#typ then 
		real_type, te1#region, te1#node
	      else if is_double te1#typ then 
		real_type, te1#region, JCEreal_cast(te1,Double_to_real)
	      else if is_float te1#typ then 
		real_type, te1#region, JCEreal_cast(te1,Float_to_real)
	      else
		typing_error e#pos "bad cast to real"
	  | JCTnative Tdouble -> 
              if is_real te1#typ || is_integer te1#typ then
                double_type, te1#region, JCEreal_cast(te1,Round_double Round_nearest_even)
              else if is_float te1#typ then
                double_type, te1#region, te1#node
	      else
		typing_error e#pos "bad cast to double"
	  | JCTnative Tfloat -> 
              if is_real te1#typ || is_double te1#typ || is_integer te1#typ then
                float_type, te1#region, JCEreal_cast(te1,Round_float Round_nearest_even)
	      else
		typing_error e#pos "bad cast to float"
	  | JCTnative _ -> assert false (* TODO *)
	  | JCTenum ri ->
	      if is_integer te1#typ then
		JCTenum ri, dummy_region, JCErange_cast(te1, ri)
	      else 
		(* CM je ne comprends pas ce cast de real vers enum 
		   if is_real te1#typ then
		let cast = NExpr.mkcast ~expr:e1 ~typ:integer_type () in
		let t = ft cast in
		  JCTenum ri, te1#region, JCErange_cast(t, ri)
	      else
		*)
		typing_error e#pos "integer type expected"
	  | JCTpointer(JCtag(st,_),_,_) -> 
	      begin match te1#typ with
		| JCTpointer(st1, a, b) ->
		    if superstruct st st1 then
		      (te1#typ,
		       te1#region,
		       te1#node)
		    else if substruct st st1 then
		      (JCTpointer(JCtag(st, []), a, b),
		       te1#region,
		       JCEcast(te1, st))
		    else if same_hierarchy (JCtag(st, [])) st1 then
		      typing_error e#pos "invalid cast"
		    else
		      (* bitwise cast *)
		      (Region.make_bitwise te1#region;
		       JCTpointer(JCtag(st, []), a, b),
		       te1#region,
		       JCEbitwise_cast(te1, st))
		| JCTnull ->
		    (* bitwise cast *)
		    (Region.make_bitwise te1#region;
		     JCTpointer(JCtag(st,[]),None,None),
		     te1#region,
		     JCEbitwise_cast(te1, st))
		| JCTnative _ | JCTlogic _ | JCTenum _ | JCTany
		| JCTtype_var _ ->
		    typing_error e#pos "only structures can be cast"
	      end
	  | JCTpointer (JCroot _, _, _)  -> assert false (* TODO *)
	  | JCTtype_var _|JCTlogic _|JCTany|JCTnull -> assert false (* TODO *)
	end
 (*
        let te1 = fe e1 in
	if t = "integer" then
	  if is_real te1#typ then
	    integer_type, te1#region, JCEreal_cast(te1,Real_to_integer)
	  else if is_integer te1#typ then
	    integer_type, te1#region, te1#node
	  else
	    typing_error e#pos "bad cast to integer"
	else if t = "real" then
	  if is_integer te1#typ then
	    real_type, te1#region, JCEreal_cast(te1,Integer_to_real)
	  else if is_real te1#typ then 
	    real_type, te1#region, te1#node
	  else
	    typing_error e#pos "bad cast to real"
        else begin try
          let ri = Hashtbl.find enum_types_table t in
          if is_integer te1#typ then
            JCTenum ri, te1#region, JCErange_cast(te1, ri)
          else if is_real te1#typ then
	    let cast = NExpr.mkcast ~expr:e1 ~typ:"integer" () in
	    let e = fe cast in
	    JCTenum ri, te1#region, JCErange_cast(e, ri)
          else
            typing_error e#pos "numeric type expected"
        with Not_found ->
          let st = find_struct_info e#pos t in
          match te1#typ with
            | JCTpointer(st1, a, b) ->
                if superstruct st st1 then
		  (te1#typ,
                   te1#region,
                   te1#node)
                else if substruct st st1 then
                  (JCTpointer(JCtag(st, []), a, b),
                   te1#region,
                   JCEcast(te1, st))
                else if same_hierarchy (JCtag(st, [])) st1 then
                  typing_error e#pos "invalid cast"
		else
		  (* bitwise cast *)
                  (Region.make_bitwise te1#region;
		   JCTpointer(JCtag(st, []), a, b),
                   te1#region,
                   JCEbitwise_cast(te1, st))
            | _ ->
                typing_error e#pos
                  "only structures or numeric types can be cast"
        end
 *)
    | JCNEif(e1,e2,e3) ->
        let te1 = fe e1 and te2 = fe e2 and te3 = fe e3 in
        begin match te1#typ with
          | JCTnative Tboolean ->
	      let te2,te3 =
		if same_type_no_coercion te2#typ te3#typ then
		  te2,te3
		else
		  unit_expr te2, unit_expr te3 
	      in
              let t = mintype e#pos
                te2#typ
                te3#typ
              in
              t, te2#region, JCEif(te1, te2, te3)
          | _ -> typing_error e1#pos "boolean expression expected"
        end
    | JCNEoffset(k, e1) ->
        let te1 = fe e1 in
        begin match te1#typ with 
          | JCTpointer(JCtag(st, _), _, _) ->
              integer_type, dummy_region, JCEoffset(k, te1, st)
          | JCTpointer(JCroot _, _, _) ->
              assert false (* TODO *)
          | _ -> typing_error e#pos "pointer expected"
        end
    | JCNEaddress(Addr_absolute,e1) ->
        let te1 = fe e1 in
	if is_integer  te1#typ then
          JCTnull, dummy_region, JCEaddress(Addr_absolute,te1)
	else 
	  typing_error e#pos "integer expected"
    | JCNEaddress(Addr_pointer,e1) ->
        let te1 = fe e1 in
        begin match te1#typ with 
          | JCTpointer(JCtag(st, _), _, _) ->
              integer_type, dummy_region, JCEaddress(Addr_pointer,te1)
          | JCTpointer(JCroot _, _, _) ->
              assert false (* TODO *)
          | _ -> typing_error e#pos "pointer expected"
        end
    | JCNEbase_block(e1) ->
        let te1 = fe e1 in
	if is_pointer_type te1#typ then
          JCTnull, dummy_region, JCEbase_block(te1)
	else 
	  typing_error e#pos "pointer expected"
    | JCNEalloc(e1, t) ->
        let st = find_struct_info e#pos t in
        let ty = JCTpointer(JCtag(st, []), Some zero, None) in
        ty, Region.make_var ty "alloc", JCEalloc (fe e1, st)
    | JCNEfree e1 ->
        unit_type, dummy_region, JCEfree (fe e1)
    | JCNElet(tyo, id, e1o, e2) ->
        let ty, te1o = match tyo, e1o with
          | None, None ->
              typing_error e#pos "let with no initial value must have a type"
          | Some ty, None ->
              type_type ty, None
          | None, Some e1 ->
              let te1 = fe e1 in
              te1#typ, Some te1
          | Some ty, Some e1 ->
              let te1 = fe e1 in
              let tty = type_type ty in
              if subtype te1#typ tty then
                tty, Some te1
              else
                typing_error e#pos
                  "inferred type is not a subtype of declared type"
        in
        let vi = var ty id in
        let te2 = expr ((id, vi)::env) e2 in
        te2#typ,
        te2#region,
        JCElet(vi, te1o, te2)
    (* old statements *)
    | JCNEassert(behav,asrt,e1) ->
        unit_type, dummy_region, JCEassert(behav,asrt,assertion env e1)
    | JCNEcontract(req,dec,behs,e) ->
	let requires = Option_misc.map (assertion env) req in
	let decreases = Option_misc.map (term env) req in
	let e = expr env e in
	let vi_result = var (e#typ) "\\result" in
	let behs = List.map (behavior env vi_result) behs in
	e#typ,e#region,JCEcontract(requires,decreases,vi_result,behs,e)	
    | JCNEblock el ->
        (* No warning when a value is ignored. *)
        let tel = List.map fe el in
        begin match List.rev tel with
          | [] ->
              unit_type, dummy_region, JCEconst JCCvoid
          | last::but_last ->
	      let but_last = List.map unit_expr but_last in
              last#typ, last#region, JCEblock(List.rev(last::but_last))
        end
    | JCNEloop(behs, vo, body) ->
        unit_type,
        dummy_region,
        JCEloop(
          loop_annot
            ~behaviors:(List.map (loopbehavior env) behs)
            ~free_invariant:(Assertion.mktrue ())
            ~variant:(apply_option ft vo),
          fe body)
    | JCNEreturn None ->
        unit_type, dummy_region, JCEreturn_void
    | JCNEreturn(Some e1) ->
        let te1 = fe e1 in
        let vi = List.assoc "\\result" env in
        if subtype te1#typ vi.jc_var_info_type then
          (unit_type,
           te1#region,
           JCEreturn(vi.jc_var_info_type, te1))
        else
          typing_error e#pos "type `%a' expected in return instead of `%a'"
            print_type vi.jc_var_info_type print_type te1#typ
    | JCNEtry(body, catches, finally) ->
        let tbody = unit_expr (fe body) in
        let tfinally = unit_expr (fe finally) in
        let tcatches = List.map begin function (id, v, cbody) ->
	  if id#name = Jc_norm.return_label#name then set_return_label ();
          let ei = try
            Hashtbl.find exceptions_table id#name
          with Not_found ->
            typing_error id#pos "undeclared exception: %s" id#name
          in
          match ei.jc_exception_info_type with
            | Some tei -> 
		let vi = var tei v in
		ei, Some vi, unit_expr (expr ((v, vi) :: env) cbody)
            | None -> ei, None, unit_expr (fe cbody)
        end catches in
          tbody#typ,
        tbody#region,
        JCEtry(tbody, tcatches, tfinally)
    | JCNEthrow(id, e1o) ->
        let ei = try
          Hashtbl.find exceptions_table id#name
        with Not_found ->
          typing_error id#pos "undeclared exception %s" id#name
        in
        let region, te1o = match e1o with
          | None -> dummy_region, None
          | Some e1 ->
              let te1 = fe e1 in
              let tei = match ei.jc_exception_info_type with
                | Some tei -> tei
                | None -> typing_error e#pos "this exception has no argument"
              in
              if subtype te1#typ tei then
                te1#region, Some te1
              else
                typing_error e#pos "type `%a' expected instead of `%a'"
                  print_type tei print_type te1#typ
        in
        Jc_pervasives.any_type, region, JCEthrow(ei, te1o)
    | JCNEpack(e1, t) ->
        let te1 = fe e1 in
        begin match te1#typ with
          | JCTpointer(JCtag(st, _), _, _) ->
              let as_t = match t with
                | Some t -> find_struct_info t#pos t#name
                | None -> st
              in
              unit_type, te1#region, JCEpack(st, te1, as_t)
          | _ -> typing_error e#pos "only structures can be packed"
        end
    | JCNEunpack(e1, t) ->
        let te1 = fe e1 in 
        begin match te1#typ with
          | JCTpointer(JCtag(st, []), _, _) ->
              let from_t = match t with
                | Some t -> find_struct_info t#pos t#name
                | None ->
                    let rec res = {
                      jc_struct_info_params = [];
                      jc_struct_info_name = "bottom";
                      jc_struct_info_parent = None;
                      jc_struct_info_hroot = res;
                      jc_struct_info_fields = [];
                      jc_struct_info_root = None;
                    }
                    in res
              in
              unit_type, te1#region, JCEunpack(st, te1, from_t)
          | _ -> typing_error e#pos "only structures can be unpacked"
        end
    | JCNEmatch(arg, pel) ->
        let targ = fe arg in
        let rty, tpel = match pel with
          | [] -> assert false (* should not be allowed by the parser *)
          | (p1, e1)::rem ->
              (* type the first item *)
              let penv, tp1 = pattern p1 targ#typ in
              let te1 = expr (penv @ env) e1 in
              (* type the remaining items *)
              List.fold_left
                (fun (accrty, acctpel) (p, e2) ->
                   let penv, tp = pattern p targ#typ in
                   let te2 = expr (penv @ env) e2 in
                   mintype e#pos accrty te2#typ,
                   (tp, te2)::acctpel)
                (te1#typ, [tp1, te1])
                rem
        in
        rty, targ#region, JCEmatch(targ, List.rev tpel)
    (* logic only *)
    | JCNEquantifier _ | JCNEold _ | JCNEat _ | JCNEmutable _
    | JCNEeqtype _ | JCNErange _ | JCNEsubtype _ ->
        typing_error e#pos "construction not allowed in expressions"
  in
  new expr
    ~pos: e#pos
    ~typ: ty
    ~region: region
    ~mark: !lab
    typed_e

(*******************************************************************************)
(*                                  Declarations                               *)
(*******************************************************************************)



let default_label l =
  match l with
    | [l] -> Some l
    | _ -> None

(** Apply [type_labels] in all expressions of a normalized clause,
with the correct label environment. *)
let type_labels_in_clause = function
  | JCCrequires e | JCCdecreases e ->
      type_labels [LabelHere] ~result_label:None (Some LabelHere) e
  | JCCbehavior(_, _, _, assumes, requires, assigns, ensures) ->
      Option_misc.iter
	(type_labels [LabelHere] ~result_label:None (Some LabelHere)) assumes;
      Option_misc.iter
	(type_labels [LabelHere] ~result_label:None (Some LabelHere)) requires;
      Option_misc.iter
        (fun (_, x) ->
           List.iter
             (type_labels [LabelOld; LabelHere] 
		~result_label:(Some LabelPost) (Some LabelOld)) x)
        assigns;
      type_labels [LabelOld; LabelHere] 
	~result_label:(Some LabelHere) (Some LabelHere) ensures

(** Apply [type_labels] in all expressions of a normalized declaration,
with the correct label environment. *)
let rec type_labels_in_decl d = match d#node with
  | JCDvar(_, _, init) ->
      Option_misc.iter (type_labels [] ~result_label:None None) init
  | JCDfun(_, _, _, clauses, body) ->
      Option_misc.iter
        (type_labels [LabelHere; LabelPre] ~result_label:None (Some LabelHere))
        body;
      List.iter type_labels_in_clause clauses
  | JCDtag(_, _, _, _, invs) ->
      List.iter
        (fun (_, _, e) -> 
	   type_labels [LabelHere] ~result_label:None (Some LabelHere) e) invs
  | JCDlemma(_, _, labels, body) ->
(*
      let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
      type_labels labels ~result_label:None (default_label labels) body
  | JCDlogic(_, _, labels, _, JCreads el) ->
(*
      let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
      List.iter 
	(type_labels labels 
	   ~result_label:(Some LabelPost) (default_label labels)) el
  | JCDlogic(_, _, labels, _, JCexpr e) ->
(*
      let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
      type_labels labels  ~result_label:None (default_label labels) e
  | JCDlogic(_, _, labels, _, JCinductive l) ->
(*
      let _labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
      List.iter (fun (_,labels,e) -> 
		   type_labels labels 
		     ~result_label:None (default_label labels) e) l
  | JCDglobal_inv(_, body) ->
      type_labels [LabelHere] ~result_label:None (Some LabelHere) body
  | JCDvariant_type _ | JCDunion_type _ | JCDenum_type _ | JCDlogic_type _
  | JCDexception _ | JCDinvariant_policy _ | JCDseparation_policy _
  | JCDannotation_policy _ | JCDabstract_domain _ | JCDint_model _ 
  | JCDlogic_var _ ->
      ()
  | JCDaxiomatic(id,l) -> List.iter type_labels_in_decl l



(* <====== A partir d'ici, c'est pas encore fait *)



let clause env vi_result c acc =
  match c with
    | JCCrequires e ->
        { acc with 
          jc_fun_requires = 
            make_and (assertion env e) acc.jc_fun_requires; }
    | JCCdecreases e ->
	assert (acc.jc_fun_decreases = None);
        { acc with jc_fun_decreases = Some (term env e) }
	
    | JCCbehavior b ->
	let (loc,id,b) = behavior env vi_result b in
	if id = "default" then
	  { acc with jc_fun_default_behavior = loc,id,b }
	else
          { acc with jc_fun_behavior = (loc,id,b)::acc.jc_fun_behavior }
  
let param (t,id) =
  let ty = type_type t in
  let vi = var ~formal:true ty id in 
  (id,vi)

let fun_param (v,t,id) =
  let ty = type_type t in
  let vi = var ~formal:true ty id in 
  (v,id,vi)

let assertion_true = new assertion JCAtrue

let field st root (rep, t, id, bitsize) =
  let ty = type_type t in
  incr field_tag_counter;
  let name = st.jc_struct_info_name ^ "_" ^ id in
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = id ;
    jc_field_info_final_name = Jc_envset.get_unique_name name;
    jc_field_info_type = ty;
    jc_field_info_hroot = root;
    jc_field_info_struct = st;
    jc_field_info_rep = rep or (not (is_pointer_type ty));
    jc_field_info_bitsize = bitsize;
  } in
  fi

let lemmas_table = Hashtbl.create 17
let global_invariants_table = Hashtbl.create 17

(*let add_typedecl d (id, parent) =
  let root,par = 
    match parent with
      | None -> 
          (None, None)
      | Some p ->
          let st = find_struct_info d.jc_pdecl_loc p in
          (Some st.jc_struct_info_hroot, Some st)
  in
  let struct_info, root =
    try
      let struct_info,_ = Hashtbl.find structs_table id in
      let root = match root with
        | Some x -> x
        | None -> struct_info
      in
      struct_info.jc_struct_info_hroot <- root;
      struct_info.jc_struct_info_parent <- par;
      struct_info, root
    with Not_found ->
      assert false (* cannot happen, thanks to the function decl_declare *)
(*      let rec struct_info =
        { jc_struct_info_name = id;
          jc_struct_info_fields = [];
          jc_struct_info_parent = par;
          jc_struct_info_hroot = struct_info;
          jc_struct_info_root = None;
        }
      in
      (* adding structure name in global environment before typing 
         the fields, because of possible recursive definition *)
      Hashtbl.replace structs_table id (struct_info,[]);
      struct_info, struct_info*)
  in
  root, struct_info*)

let add_vardecl (ty,id) =
  let ty = type_type ty in
  let vi = var ~static:true ty id in
  Hashtbl.add variables_env id vi

let get_vardecl id =
  Hashtbl.find variables_env id

let get_fundecl id =
  let fi = Hashtbl.find functions_env id in
  let param_env =
    List.map 
      (fun (valid,v) -> (v.jc_var_info_name, v)) 
      fi.jc_fun_info_parameters
  in
  param_env, fi

let add_fundecl (ty,loc,id,pl) =
  try
    let param_env,fi = get_fundecl id in
    Format.eprintf 
      "FIXME: Warning: ignoring second declaration of function %s@." id;
    param_env, fi
  with Not_found ->
    let params = List.map fun_param pl in
    let param_env = List.map (fun (_,t,x) -> (t,x)) params in
    let ty = type_type ty in
    let fi = make_fun_info id ty in
    fi.jc_fun_info_parameters <- List.map (fun (v,_,x) -> (v,x)) params;
    Hashtbl.replace functions_env id fi;
    param_env, fi

let add_logic_fundecl (ty,id,labels,pl) =
  try
    let pi = Hashtbl.find logic_functions_env id in
    let ty = pi.jc_logic_info_result_type in
    let param_env =
      List.map (fun v -> v.jc_var_info_name, v) pi.jc_logic_info_parameters
    in
    param_env, ty, pi
  with Not_found ->
    let param_env = List.map param pl in
    let ty = Option_misc.map type_type ty in
    let pi = match ty with 
      | None -> make_pred id
      | Some ty -> make_logic_fun id ty
    in
    pi.jc_logic_info_parameters <- List.map snd param_env;
    pi.jc_logic_info_labels <- labels;
    Hashtbl.replace logic_functions_env id pi;
    param_env, ty, pi

let () =
  List.iter 
    (fun (ty,x,whyid,pl) -> 
       let pi = match ty with 
	 | None -> make_pred x
	 | Some ty -> make_logic_fun x ty
       in
       let pl = List.map 
	 (fun ty -> var ~formal:true ty "_") pl
       in
       pi.jc_logic_info_parameters <- pl;
       pi.jc_logic_info_final_name <- whyid;
       Hashtbl.add logic_functions_env x pi)
    Jc_pervasives.builtin_logic_symbols;
  List.iter 
    (fun (ty,x,whyid,pl,treat) -> 
       let pi = make_fun_info x ty in
       let pl = List.map 
	 (fun ty -> (true,var ~formal:true ty "_")) pl
       in
       pi.jc_fun_info_parameters <- pl;
       pi.jc_fun_info_final_name <- whyid;
       pi.jc_fun_info_builtin_treatment <- Some treat;
       Hashtbl.add functions_env x pi)
    Jc_pervasives.builtin_function_symbols

(* let add_logic_constdecl (ty, id) = *)
(*   try *)
(*     let vi = Hashtbl.find logic_constants_env id in *)
(*       vi.jc_var_info_type, vi  *)
(*   with Not_found -> *)
(*     let ty = type_type ty in *)
(*     let vi = var ~static:true ty id in *)
(*       Hashtbl.add logic_constants_env id vi; *)
(*       ty, vi *)
        
let type_range_of_term ty t =
  match ty with
    | JCTenum ri ->
        let mint = 
          new term ~pos:t#pos ~typ:integer_type
            (JCTconst(JCCinteger (Num.string_of_num ri.jc_enum_info_min)))
        in
        let mina = new assertion (JCArelation(mint,(`Ble,`Integer),t)) in
        let maxt = 
          new term ~pos:t#pos ~typ:integer_type
            (JCTconst(JCCinteger (Num.string_of_num ri.jc_enum_info_max)))
        in
        let maxa = new assertion (JCArelation(t,(`Ble,`Integer),maxt)) in
	new assertion (JCAand [ mina; maxa ])
    | JCTpointer (JCtag(st, _), n1opt, n2opt) ->
(*      let instanceofcstr = new assertion (JCAinstanceof (t, st)) in *)
(*      let mincstr = match n1opt with
          | None -> true_assertion
          | Some n1 ->
              let mint = 
                term_no_loc (JCToffset (Offset_min, t, st)) integer_type in
              let n1t =
                term_no_loc (JCTconst (JCCinteger (Num.string_of_num n1))) 
                  integer_type
              in
              new assertion (JCArelation (mint, Beq_int, n1t))
        in *)
        let maxcstr = match n2opt with
          | None -> Assertion.mktrue ()
          | Some n2 ->
              let maxt = 
                new term
                  ~pos: t#pos
                  ~typ: integer_type
                  (JCToffset (Offset_max, t, st))
              in
              let n2t =
                new term
                  ~pos: t#pos
                  ~typ: integer_type
                  (JCTconst (JCCinteger (Num.string_of_num n2)))
              in
              new assertion (JCArelation (maxt, (`Beq, `Integer), n2t))
        in
          maxcstr
(*        if is_root_struct st then *)
(*        Jc_pervasives.make_and [mincstr; maxcstr] *)
(*        else
          Jc_pervasives.make_and [instanceofcstr; mincstr; maxcstr] *)
    | JCTpointer (JCroot vi, _, _) ->
        assert false (* TODO, but need to change JCToffset before *)
    | _ -> Assertion.mktrue ()

(* First pass: declare everything with no typing
 * (use dummy values that will be replaced by "decl")
 * (declare identifiers so that previous definitions can (possibly recursively)
 * use them) *)
(*let rec decl_declare d =
  match d.jc_pdecl_node with
    | JCPDtag(id, parent, fields, inv) ->
        (* declare structure name *)
        let rec struct_info = {
          jc_struct_info_name = id;
          jc_struct_info_fields = [];
          jc_struct_info_parent = None;
          jc_struct_info_hroot = struct_info;
          jc_struct_info_root = None;
        } in
        Hashtbl.add structs_table id (struct_info, []);
        (* declare mutable field (if needed) *)
        if parent = None && !Jc_common_options.inv_sem = InvOwnership then
          create_mutable_field struct_info;
        (* TODO: declare fields *)
        (* TODO: declare invariants *)
        Hashtbl.replace structs_table id (struct_info, [])
    | JCPDvarianttype(id, _) ->
        Hashtbl.replace variants_table id {
          jc_root_info_name = id;
          jc_root_info_roots = [];
        }
    | JCPDvar _
    | JCPDfun _
    | JCPDrecfuns _
    | JCPDenumtype _
    | JCPDlogictype _
    | JCPDaxiom _
    | JCPDexception _
    | JCPDlogic _
    | JCPDglobinv _ ->
        () (* TODO *)
*)

(** [check_positivity pi a] checks whether the assertion [a] as exactly one positive occurrence of pi in a *)

let rec signed_occurrences pi a =
match a#node with
  | JCArelation _ | JCAtrue | JCAfalse -> (0,0)
  | JCAapp app -> ((if app.jc_app_fun == pi then 1 else 0),0)
  | JCAquantifier (Forall, vi, p) -> signed_occurrences pi p
  | JCAquantifier (Exists, vi, p) -> assert false (* TODO *)
  | JCAimplies (p1, p2) -> 
      let (pos1,neg1) = signed_occurrences pi p1 in
      let (pos2,neg2) = signed_occurrences pi p2 in
      (neg1+pos2,pos1+neg2)
  | JCAand l -> 
      List.fold_left
	(fun (p,n) a -> 
	   let (pos1,neg1) = signed_occurrences pi a in
	   (p+pos1,n+neg1)) (0,0) l
  | JCAor _ -> assert false (* TODO *)
  | JCAnot p -> 
      let (pos,neg) = signed_occurrences pi p in
      (neg,pos)
  | JCAiff (_, _) -> assert false (* TODO *)
  | JCAsubtype (_, _, _) -> assert false (* TODO *)
  | JCAeqtype (_, _, _) -> assert false (* TODO *)
  | JCAmutable (_, _, _) -> assert false (* TODO *)
  | JCAif (_, _, _) -> assert false (* TODO *)
  | JCAbool_term _ -> assert false (* TODO *)
  | JCAinstanceof (_, _, _) -> assert false (* TODO *)
  | JCAat (_, _) -> assert false (* TODO *)
  | JCAold _ -> assert false (* TODO *)
  | JCAmatch (_, _) -> assert false (* TODO *)

let check_positivity loc pi a =
  let (pos,neg) = signed_occurrences pi a in
  if pos = 0 then 
    typing_error loc "predicate has no positive occurrence in this case";
  if pos > 1 then 
    typing_error loc "predicate has too many positive occurrences in this case"



(** [check_consistency id data] attempt to detect trivial inconsistency cases in axiomatics
  
    pis = data.axiomatics_defined_ids is the set of logic ids defined in this axiomatic

    check 1: 
      for each lemma: check that at least one pi of pis occurs

    check 2:
      for each lemma with labels l1,..,lk: for each li, there should be at least one occurrence 
      of some pi of pis applied to label li.

*)

let rec term_occurrences table t =
  match t#node with
    | JCTconst _ 
    | JCTvar _ -> ()
    | JCTrange_cast (t, _)
    | JCTat (t, _) 
    | JCTunary (_, t) 
    | JCToffset (_, t, _)
    | JCTderef (t, _, _) -> term_occurrences table t
    | JCTbinary (t1, _, t2)
    | JCTshift (t1, t2) -> 
	term_occurrences table t1; term_occurrences table t2
    | JCTapp app ->
      begin
        List.iter (term_occurrences table) app.jc_app_args;
	try
	  let l = Hashtbl.find table app.jc_app_fun.jc_logic_info_tag in
	  Hashtbl.replace table app.jc_app_fun.jc_logic_info_tag (app.jc_app_label_assoc::l)
	with Not_found -> ()
      end
    | JCTmatch (_, _) -> assert false (* TODO *)
    | JCTrange (_, _) -> assert false (* TODO *)
    | JCTif (_, _, _) -> assert false (* TODO *)
    | JCTreal_cast (_, _) -> assert false (* TODO *)
    | JCTbitwise_cast (_, _, _) -> assert false (* TODO *)
    | JCTcast (_, _, _) -> assert false (* TODO *)
    | JCTinstanceof (_, _, _) -> assert false (* TODO *)
    | JCTbase_block _ -> assert false (* TODO *)
    | JCTaddress (_, _) -> assert false (* TODO *)
    | JCTold _ -> assert false (* TODO *)

let rec occurrences table a =
  match a#node with
  | JCAtrue | JCAfalse -> ()
  | JCAapp app -> 
      begin
        List.iter (term_occurrences table) app.jc_app_args;
	try
	  let l = Hashtbl.find table app.jc_app_fun.jc_logic_info_tag in
	  Hashtbl.replace table app.jc_app_fun.jc_logic_info_tag (app.jc_app_label_assoc::l)
	with Not_found -> ()
      end
  | JCAnot p
  | JCAquantifier (_, _, p) -> occurrences table p
  | JCAiff (p1, p2)
  | JCAimplies (p1, p2) -> 
      occurrences table p1; occurrences table p2 
  | JCAand l | JCAor l -> 
      List.iter (occurrences table) l
  | JCArelation(t1,op,t2) -> 
      term_occurrences table t1; term_occurrences table t2
  | JCAsubtype (_, _, _) -> assert false (* TODO *)
  | JCAeqtype (_, _, _) -> assert false (* TODO *)
  | JCAmutable (_, _, _) -> assert false (* TODO *)
  | JCAif (_, _, _) -> assert false (* TODO *)
  | JCAbool_term _ -> assert false (* TODO *)
  | JCAinstanceof (_, _, _) -> assert false (* TODO *)
  | JCAat (_, _) -> assert false (* TODO *)
  | JCAold _ -> assert false (* TODO *)
  | JCAmatch (_, _) -> assert false (* TODO *)

let rec list_assoc_data lab l =
  match l with
    | [] -> false
    | (_,d):: r -> 	
	d=lab || list_assoc_data lab r

let check_consistency id data =
  let pis = data.axiomatics_defined_ids in
  List.iter
    (fun (ABaxiom(loc,axid,labels,a)) -> 
       let h = Hashtbl.create 17 in
       List.iter
	 (fun pi -> Hashtbl.add h pi.jc_logic_info_tag [])
	 pis;
       occurrences h a;
       Jc_options.lprintf "@[<v 2>occurrences table for axiom %s in axiomatic %s:@\n" axid id;
       Hashtbl.iter
	 (fun pi l ->
	    Jc_options.lprintf "%d: @[" pi;
	    List.iter
	      (fun label_assoc -> 
		 Jc_options.lprintf "%a ;" 
		   (Pp.print_list Pp.comma (fun fmt (l1,l2) -> Jc_output_misc.label fmt l2)) label_assoc)
	      l;
	    Jc_options.lprintf "@]@\n")
	 h;		 
       Jc_options.lprintf "@]@.";
       if Hashtbl.fold (fun pi l acc -> acc && l=[]) h true then
	 typing_error loc 
	   "axiom %s should contain at least one occurrence of a symbol declared in axiomatic %s" axid id;
       List.iter
	 (fun lab ->
	    if not (Hashtbl.fold (fun pi l acc -> acc || List.exists (list_assoc_data lab) l) h false) then
	      typing_error loc 
		"there should be at least one declared symbol depending on label %a in this axiom" Jc_output_misc.label lab)
	 labels
    )
    data.axiomatics_decls

let update_axiomatic axiomatic pi =
  match axiomatic with
    | Some(id,data) ->
	pi.jc_logic_info_axiomatic <- Some id;
	data.axiomatics_defined_ids <- pi :: data.axiomatics_defined_ids
    | None -> ()
  

let rec decl_aux ~only_types ~axiomatic acc d =
  let loc = d#pos in
  let in_axiomatic = axiomatic <> None in
  match d#node with
    | JCDvar (ty, id, init) ->
	if not only_types then
	  begin
	    if in_axiomatic then
	      typing_error loc "not allowed inside axiomatic specification";
            let e = Option_misc.map (expr []) init in
            let vi = get_vardecl id in
            Hashtbl.add variables_table vi.jc_var_info_tag (vi, e);
	    acc
	  end
	else 
	  acc
    | JCDfun (ty, id, pl, specs, body) -> 
	if not only_types then
	  begin
	if in_axiomatic then
	  typing_error loc "not allowed inside axiomatic specification";
        let loc = match Jc_options.position_of_label id#name with
	  | Some loc -> loc
	  | None -> id#pos 
	in
        let param_env, fi = get_fundecl id#name in
        let vi = fi.jc_fun_info_result in
        let s = List.fold_right 
                  (clause param_env vi) specs 
                  { jc_fun_requires = assertion_true;
                    jc_fun_free_requires = assertion_true;
		    jc_fun_decreases = None;
                    jc_fun_default_behavior = 
		      Loc.dummy_position ,"default", default_behavior;
                    jc_fun_behavior = [] }
        in
	reset_return_label ();
        let b = Option_misc.map 
	  (unit_expr $ expr (("\\result",vi)::param_env)) body 
	in
	fi.jc_fun_info_has_return_label <- get_return_label ();
        Hashtbl.add functions_table fi.jc_fun_info_tag (fi,loc,s,b);
	acc
	  end
	else 
	  acc
    | JCDenum_type(id,min,max) ->
	if only_types then
	  begin
	if in_axiomatic then
	  typing_error loc "not allowed inside axiomatic specification";
	begin
	  try
	    let _ = Hashtbl.find enum_types_table id in
	    typing_error d#pos "duplicate range type `%s'" id
	  with Not_found ->
            let ri =
              { jc_enum_info_name = id;
		jc_enum_info_min = min;
		jc_enum_info_max = max;
              }
            in
	    (*
              let to_int = make_logic_fun ("integer_of_"^id) integer_type in
              let to_int_ = make_fun_info ("integer_of_"^id) integer_type in
              let of_int = make_fun_info (id^"_of_integer") (JCTenum ri) in
	    *)
            Hashtbl.add enum_types_table id (ri (*,to_int,to_int_,of_int*));
	    (*
              Hashtbl.add enum_conversion_logic_functions_table to_int id;
              Hashtbl.add enum_conversion_functions_table to_int_ id;
              Hashtbl.add enum_conversion_functions_table of_int id
	    *)
	    acc
	end
	  end
	else 
	  acc
    | JCDtag(id, _, parent, fields, inv) ->
	if not only_types then
	  begin
	Jc_options.lprintf "Typing tag %s@." id;
	if in_axiomatic then
	  typing_error loc "not allowed inside axiomatic specification";
        let struct_info, _ = Hashtbl.find structs_table id in
        (* declare invariants as logical functions *)
        let invariants =
          List.fold_left
            (fun acc (id, x, e) ->
               if !Jc_common_options.inv_sem = InvNone then
                 typing_error id#pos
                   "use of structure invariants requires declaration \
of an invariant policy";
               let vi =
                 var (JCTpointer (JCtag(struct_info, []), Some zero,
                                  Some zero)) x in
               let p = assertion [(x, vi)] e in
               let pi = make_pred id#name in
               pi.jc_logic_info_parameters <- [vi];
               pi.jc_logic_info_labels <- [LabelHere];
               eprintf "generating logic fun %s with one default label@."
                 pi.jc_logic_info_name;
               Hashtbl.replace logic_functions_table 
                 pi.jc_logic_info_tag (pi, JCAssertion p);
               Hashtbl.replace logic_functions_env id#name pi;
               (pi, p) :: acc)
            []
            inv
        in 
        Hashtbl.replace structs_table id (struct_info, invariants);
	acc
	  end
	else 
	  acc

    | JCDvariant_type(id, tags) -> acc
    | JCDunion_type(id,_discr,tags) -> acc

(*    | JCDrectypes(pdecls) ->
        (* first pass: adding structure names *)
        List.iter (fun d -> match d.jc_pdecl_node with
                     | JCDstructtype(id,_,_,_) ->
                         (* parent type may not be declared yet *)
                         ignore (add_typedecl d (id,None))
                     | _ -> assert false
                  ) pdecls;
        (* second pass: adding structure fields *)
        List.iter (fun d -> match d.jc_pdecl_node with
                     | JCDstructtype(id,parent,fields,_) ->
                         let root,struct_info = add_typedecl d (id,parent) in
                         let env = List.map (field struct_info root) fields in
                         struct_info.jc_struct_info_fields <- env;
                         Hashtbl.replace structs_table id (struct_info,[])
                     | _ -> assert false
                  ) pdecls;
        (* third pass: typing invariants *)
        List.iter decl pdecls*)

    | JCDlogic_type(id) ->
	if only_types then
	  begin
	Jc_options.lprintf "Typing logic type declaration %s@." id;
        begin 
          try
            let _ = Hashtbl.find logic_type_table id in
            typing_error d#pos "duplicate logic type `%s'" id 
          with Not_found ->
            Hashtbl.add logic_type_table id id;
	    acc
        end
	  end
	else 
	  acc
    | JCDlemma(id,is_axiom,labels,e) ->
	if not only_types then
	  begin
	Jc_options.lprintf "Typing lemma/axiom %s@." id;
	if is_axiom && not in_axiomatic then
	  typing_error loc "allowed only inside axiomatic specification";
(*
	let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
        let te = assertion [] e in
        if in_axiomatic && is_axiom then
	  (ABaxiom(d#pos,id,labels,te))::acc
	else
	  begin
	    Hashtbl.add lemmas_table id (d#pos,is_axiom,labels,te);
	    acc
	  end
	  end
	else 
	  acc
    | JCDglobal_inv(id, e) ->
	if not only_types then
	  begin
	if in_axiomatic then
	  typing_error loc "not allowed inside axiomatic specification";
        let a = assertion [] e in
        let li = make_pred id in
        if !Jc_common_options.inv_sem = InvArguments then 
          Hashtbl.replace logic_functions_table 
            li.jc_logic_info_tag (li, JCAssertion a);
        Hashtbl.add global_invariants_table li a;
	acc
	  end
	else 
	  acc
    | JCDexception(id,tyopt) ->
	if not only_types then
	  begin
	if in_axiomatic then
	  typing_error loc "not allowed inside axiomatic specification";
        let tt = Option_misc.map type_type tyopt in
        Hashtbl.add exceptions_table id (exception_info tt id);
	acc
	  end
	else 
	  acc
    | JCDlogic_var (ty, id, body) -> assert false
(*         let ty, vi = add_logic_constdecl (ty, id) in *)
(*         let t = Option_misc.map  *)
(* 	  (function body -> *)
(* 	     let t = term [] body in *)
(*              if not (subtype t#typ ty) then *)
(*                typing_error d#pos *)
(*                  "inferred type differs from declared type" *)
(*              else (t,mintype t#pos t#typ ty) *)
(* 	  ) body *)
(*         in *)
(*         Hashtbl.add logic_constants_table vi.jc_var_info_tag (vi, t) *)
    | JCDlogic (None, id, labels, pl, body) ->
	if not only_types then
	  begin
(*
	    let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
            let param_env,ty,pi = add_logic_fundecl (None,id,labels,pl) in
            let p = match body with
          | JCreads reads ->
	      if not in_axiomatic then
		typing_error loc "allowed only inside axiomatic specification";
              JCReads (
                (List.map 
                   (fun a -> 
                      let _,_,tl = 
                        location param_env a 
                      in tl)) reads)
          | JCexpr body ->
              JCAssertion(assertion param_env body)
		(*
		  | JCaxiomatic l ->
		  JCAxiomatic(List.map (fun (id,e) -> (id,assertion param_env e)) l)
		*)
	  | JCinductive l ->
	      JCInductive(List.map 
			    (fun (id,labels,e) -> 
(*
			       let labels = match labels with 
				   [] -> [ LabelHere ] 
				 | _ -> labels 
			       in
*)
			       let a = assertion param_env e in
				 check_positivity a#pos pi a;
			       (id,labels,a)) 
			    l)
            in
	    update_axiomatic axiomatic pi;
            Hashtbl.add logic_functions_table pi.jc_logic_info_tag (pi, p);
	    acc
	  end
	else 
	  acc
    | JCDlogic (Some ty, id, labels, pl, body) ->
	if not only_types then
	  begin
(*
	    let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
            let param_env, ty, pi = add_logic_fundecl (Some ty,id,labels,pl) in
            let ty = match ty with Some ty -> ty | None -> assert false in
            let t = match body with
              | JCreads [] -> JCReads []
              | JCreads reads ->
		  if not in_axiomatic then
		    typing_error loc "allowed only inside axiomatic specification";
		  JCReads (
                    (List.map 
                       (fun a -> 
			  let _,_,tl = location param_env a 
			  in tl)) reads)
              | JCexpr body ->
		  let t = term param_env body in
		    if pl = [] && not (subtype t#typ ty) 
		      || pl <> [] && not (subtype_strict t#typ ty) then 
			typing_error d#pos
			  "inferred type differs from declared type" 
		    else 
		      begin
			if pl = [] then
			  (* constant *)
			  Hashtbl.add logic_constants_table pi.jc_logic_info_tag (pi, t);
			JCTerm t
		      end
		      (*
			| JCaxiomatic l ->
			JCAxiomatic(List.map (fun (id,e) -> (id,assertion param_env e)) l)
		      *)
	      | JCinductive _ ->
		  typing_error d#pos
                    "only predicates can be inductively defined" 	      
            in
	    update_axiomatic axiomatic pi;
            Hashtbl.add logic_functions_table pi.jc_logic_info_tag (pi, t);
	    acc
	  end
	else 
	  acc
    | JCDint_model _|JCDabstract_domain _|JCDannotation_policy _
    | JCDseparation_policy _|JCDinvariant_policy _ ->
        assert false
    | JCDaxiomatic(id,l) -> 
	Jc_options.lprintf "Typing axiomatic %s@." id;
	let data = 
	  {
	    axiomatics_defined_ids = [];
	    axiomatics_decls = [];
	  }
	in
	data.axiomatics_decls <- List.fold_left (decl_aux ~only_types ~axiomatic:(Some (id,data))) [] l;
	if not only_types then
	  begin
	    check_consistency id data;
	    Hashtbl.add axiomatics_table id data
	  end;
	acc
	  
let decl ~only_types d = 
  ignore (decl_aux ~only_types ~axiomatic:None [] d)	

let declare_struct_info d = match d#node with
  | JCDtag(id, _, parent, _, _) ->
      let rec si = {
        jc_struct_info_params = [];
        jc_struct_info_name = id;
        jc_struct_info_fields = [];
        jc_struct_info_parent = None;
        jc_struct_info_hroot = si;
        jc_struct_info_root = None;
      } in
      Hashtbl.add structs_table id (si, []);
      (* declare the "mutable" field (if needed) *)
      if parent = None && !Jc_common_options.inv_sem = InvOwnership then
        create_mutable_field si
  | _ -> ()

let rec declare_function d = match d#node with
  | JCDfun(ty,id,pl,_specs,_body) ->
      ignore 
        (add_fundecl (ty,id#pos,id#name,pl))
(*   | JCDlogic(Some ty,id,labels,[],_body) -> *)
(*       ignore  *)
(* 	(add_logic_constdecl (ty,id)) *)
  | JCDlogic(ty,id,labels,pl,_body) ->
(*
      let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
      ignore (add_logic_fundecl (ty,id,labels,pl))
  | JCDaxiomatic(_id,l) -> 
      List.iter declare_function l
  | _ -> ()

let declare_variable d = match d#node with
  | JCDvar(ty,id,_init) ->
      add_vardecl (ty,id)
  | _ -> ()

let compute_struct_info_parent d = match d#node with
  | JCDtag(id, _, Some(parent, _), _, _) ->
      let si, _ = Hashtbl.find structs_table id in
      let psi = find_struct_info d#pos parent in
      si.jc_struct_info_parent <- Some(psi, [])
  | _ -> ()

let fixpoint_struct_info_roots () =
  let modified = ref false in
  Hashtbl.iter
    (fun _ (si, _) ->
       match si.jc_struct_info_parent with
         | Some(psi, _) ->
             if si.jc_struct_info_hroot != psi.jc_struct_info_hroot then begin
               si.jc_struct_info_hroot <- psi.jc_struct_info_hroot;
               modified := true
             end
         | None -> ())
    structs_table;
  !modified

let type_variant d = match d#node with
  | JCDvariant_type(id, tags) | JCDunion_type(id,_,tags) ->
      (* declare the variant *)
      let vi = {
        jc_root_info_name = id;
        jc_root_info_hroots = [];
        jc_root_info_kind = 
	  (match d#node with 
     | JCDvariant_type _ -> Rvariant
	     | JCDunion_type(_,true,_) -> RdiscrUnion
	     | JCDunion_type(_,false,_) -> RplainUnion
	     | _ -> assert false
	  );
	jc_root_info_union_size_in_bytes = 0;
      } in
      Hashtbl.add roots_table id vi;
      (* tags *)
      let roots = List.map
        (fun tag ->
           (* find the structure *)
           let st, _ = try
             Hashtbl.find structs_table tag#name
           with Not_found ->
             typing_error tag#pos
               "undefined tag: %s" tag#name
           in
           (* the structure must be root *)
           if st.jc_struct_info_parent <> None then
             typing_error tag#pos
               "the tag %s is not root" tag#name;
           (* the structure must not be used by another variant *)
           match st.jc_struct_info_root with
             | None ->
                 (* update the structure variant and return the root *)
                 st.jc_struct_info_root <- Some vi;
                 st
             | Some prev -> typing_error tag#pos
                 "tag %s is already used by type %s" tag#name
                   prev.jc_root_info_name)
        tags
      in
      if root_is_union vi then
	let size = 
	  List.fold_left 
	    (fun size st -> max size (struct_size_in_bytes st)) 0 roots
	in
	vi.jc_root_info_union_size_in_bytes <- size
      else ();
      (* update the variant *)
      vi.jc_root_info_hroots <- roots
  | _ -> ()

let declare_tag_fields d = match d#node with
  | JCDtag(id, _, _, fields, inv) ->
      let struct_info, _ = Hashtbl.find structs_table id in
      let root = struct_info.jc_struct_info_hroot in
      let fields = List.map (field struct_info root) fields in
      struct_info.jc_struct_info_fields <- fields;
      Hashtbl.replace structs_table id (struct_info, [])
  | _ -> ()

let check_struct d = match d#node with
  | JCDtag(id, _, _, _, _) ->
      let loc = d#pos in
      let st = find_struct_info loc id in
      if st.jc_struct_info_hroot.jc_struct_info_root = None then
        typing_error loc "the tag %s is not used by any type"
          st.jc_struct_info_name
  | _ -> ()

(* type declarations in the right order *)
let type_file ast =
(*
  (* 1. logic types *)
  let is_logic_type d = 
    match d#node with JCDlogic_type _ -> true | _ -> false
  in
  let logic_types,ast = List.partition is_logic_type ast in
  List.iter decl logic_types;
  (* 2. enumerations *)
  let is_enum d = 
    match d#node with JCDenum_type _ -> true | _ -> false
  in
  let enums,ast = List.partition is_enum ast in
  List.iter decl enums;
*)
  List.iter (decl ~only_types:true) ast;
  (* 3. records and variants *)
  List.iter declare_struct_info ast;
  List.iter compute_struct_info_parent ast;
  while fixpoint_struct_info_roots () do () done;
  List.iter type_variant ast;
  List.iter declare_tag_fields ast;
  List.iter check_struct ast;
  (* 4. declaring global variables *)
  List.iter declare_variable ast;
  (* 5. declaring coding and logic functions *)
  List.iter declare_function ast;
  (* 6. remaining declarations *)
  List.iter (decl ~only_types:false) ast

let print_file fmt () =
  let functions =
    Hashtbl.fold
      (fun _ (finfo,_,fspec,slist) f ->
         Jc_output.JCfun_def
           (finfo.jc_fun_info_result.jc_var_info_type,finfo.jc_fun_info_name,
            finfo.jc_fun_info_parameters,fspec,slist)
         :: f
      ) functions_table []
  in
  let logic_functions =
    Hashtbl.fold
      (fun _ (linfo,tora) f ->
         Jc_output.JClogic_fun_def
           (linfo.jc_logic_info_result_type,linfo.jc_logic_info_name,
            linfo.jc_logic_info_labels,
            linfo.jc_logic_info_parameters, tora)
         :: f
      ) logic_functions_table []
  in
(*  let logic_constants =
    Hashtbl.fold
      (fun _ (vi,t) f ->
         Jc_output.JClogic_const_def
           (vi.jc_var_info_type, vi.jc_var_info_name, Option_misc.map fst t)
        :: f
      ) logic_constants_table []
  in *)
  let logic_types =
    Hashtbl.fold
      (fun _ (s) f ->
        Jc_output.JClogic_type_def s
        :: f
      ) logic_type_table []
  in
  let variables =
    Hashtbl.fold
      (fun _ (vinfo,vinit) f ->
         Jc_output.JCvar_def
           (vinfo.jc_var_info_type,vinfo.jc_var_info_name,vinit)
         :: f
      ) variables_table []
  in
  let structs =
    Hashtbl.fold
      (fun name (sinfo,_) f ->
         let super = match sinfo.jc_struct_info_parent with
           | None -> None
           | Some(st, _) -> Some st.jc_struct_info_name
         in
         Jc_output.JCstruct_def
           (name,super,sinfo.jc_struct_info_fields,[])
         :: f
      ) structs_table []
  in
  let variants =
    Hashtbl.fold
      (fun name vinfo f ->
        let tags =
          List.map (fun sinfo -> sinfo.jc_struct_info_name)
            vinfo.jc_root_info_hroots
        in
        Jc_output.JCvariant_type_def (name,tags)
        :: f
      ) roots_table []
  in
  let enums =
    Hashtbl.fold
      (fun name rinfo f ->
         Jc_output.JCenum_type_def
           (name,rinfo.jc_enum_info_min,rinfo.jc_enum_info_max)
         :: f
      ) enum_types_table []
  in
  let axioms =
    Hashtbl.fold
      (fun name (loc,is_axiom,labels, a) f ->
         Jc_output.JClemma_def (name,is_axiom, labels,a)
         :: f
      ) lemmas_table []
  in
  let global_invariants =
    Hashtbl.fold
      (fun li a f ->
         Jc_output.JCglobinv_def (li.jc_logic_info_name,a)
         :: f
      ) global_invariants_table []
  in
  let exceptions =
    Hashtbl.fold
      (fun name ei f ->
         Jc_output.JCexception_def (name,ei)
         :: f
      ) exceptions_table []
  in
  (* make all structured types mutually recursive.
     make all functions mutually recursive.
     make all logic functions and constants mutually recursive.
  *)
  let tfile =
    (List.rev enums)
    @ (List.rev structs)
    @ (List.rev variants)
    @ (List.rev exceptions)
    @ (List.rev variables)
    @ (List.rev logic_types)
    @ (Jc_output.JCrec_fun_defs
      (* (List.rev logic_constants @*) (List.rev logic_functions))
    :: (List.rev axioms)
    @ (List.rev global_invariants)
    @ [Jc_output.JCrec_fun_defs (List.rev functions)]
  in
  Jc_output.print_decls fmt tfile;

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
