(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
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

open Stdlib
open Env
open Envset
open Region
open Ast
open Fenv
open Constructors
open Common
open Struct_tools

open Format

exception Typing_error of Why_loc.position * string

let typing_error ~loc =
  Format.kfprintf
    (fun _fmt -> raise @@ Typing_error (loc, flush_str_formatter ()))
    str_formatter

let typing_warning = Format.eprintf

let uenv = Type_var.(create { f = typing_error })

let reset_uenv () = Type_var.reset uenv
let print_uenv () = Format.printf "%a" Type_var.print uenv
let add_poly_args poly_args = List.map (fun e -> Type_var.add_type_var uenv e) poly_args

let logic_type_table = StringHashtblIter.create 97
let exceptions_table = StringHashtblIter.create 97
let enum_types_table = StringHashtblIter.create 97
let structs_table = StringHashtblIter.create 97
let roots_table = StringHashtblIter.create 97

let mutable_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)
let committed_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)

let logic_functions_table = IntHashtblIter.create 97
let logic_functions_env = Hashtbl.create 97
let logic_constants_table = Hashtbl.create 97
let logic_constants_env = Hashtbl.create 97
let functions_table = IntHashtblIter.create 97
let functions_env = Hashtbl.create 97
let variables_table = IntHashtblIter.create 97
let variables_env = Hashtbl.create 97

(* Store the generated user predicates *)
let pragma_gen_sep = Hashtbl.create 10
let pragma_gen_frame = Hashtbl.create 10
let pragma_gen_same = Hashtbl.create 10

(* Keep the pragma which are defined
   before one of its argument *)
let pragma_before_def = Hashtbl.create 10

let () =
  List.iter
    (fun (ty, x, whyid, pl) ->
       let pi =
         match ty with
         | None -> make_pred x
         | Some ty -> make_logic_fun x ty
       in
       let pl =
         List.map
           (fun ty -> var ~formal:true ty "_")
           pl
       in
       pi.li_parameters <- pl;
       pi.li_final_name <- whyid;
       Hashtbl.add logic_functions_env x pi)
    Common.builtin_logic_symbols;
  List.iter
    (fun (ty, x, whyid, pl, treat) ->
       let pi = make_fun_info x ty in
       let pl =
         List.map
           (fun ty -> (true, var ~formal:true ty "_"))
           pl
       in
       pi.fun_parameters <- pl;
       pi.fun_final_name <- whyid;
       pi.fun_builtin_treatment <- treat;
       Hashtbl.add functions_env x pi)
    Common.builtin_function_symbols;
  List.iter
    (fun (name, enum) ->
       StringHashtblIter.add enum_types_table name enum)
    Common.builtin_enum_symbols

let real_of_integer =
  Hashtbl.find logic_functions_env "\\real_of_integer"

type axiomatic_decl =
  | ADprop of Why_loc.position * string * Env.label list * [ `Axiom | `Lemma ] * Constructors.assertion

type axiomatic_data = {
  mutable axiomatics_defined_ids : logic_info list;
  mutable axiomatics_decls : axiomatic_decl list;
}

let axiomatics_table = StringHashtblIter.create 17

let field_tag_counter = ref 0

let create_mutable_field st =
  incr field_tag_counter;
  let name = "committed_" ^ st.si_name in
  let fi = {
    fi_tag = !field_tag_counter;
    fi_name = name;
    fi_final_name = Envset.get_unique_name name;
    fi_type = boolean_type;
    fi_hroot = st.si_hroot;
    fi_struct = st;
    fi_rep = false;
    fi_abstract = false;
    fi_bitsize = 0;
    fi_bitoffset = 0
  }
  in
  Hashtbl.add committed_fields_table st.si_name fi

let find_struct_info ~loc id =
  try
    let st, _ = StringHashtblIter.find structs_table id in st
  with
  | Not_found ->
    typing_error ~loc "undeclared structure %s" id

let find_struct_root st =
  match st.si_hroot.si_root with
  | None -> raise Not_found
  | Some vi -> vi

let is_type_var =
  function
  | JCTtype_var _ -> true
  | _ -> false

let cast_needed ~loc ty =
  typing_error
    ~loc
    "At this point a concrete outermost type is needed (got %a). One can use a cast to concretize the type."
    print_type ty

let bad_type ~loc ty s =
  if is_type_var ty then
    cast_needed ~loc ty
  else
    typing_error ~loc s

let check_not_var ~loc ty =
  if is_type_var ty then
    cast_needed ~loc ty

let is_real t =
  match t with
  | JCTnative Treal -> true
  | _ -> false

let is_double t =
  match t with
  | JCTnative (Tgenfloat `Double) -> true
  | _ -> false

let is_float t =
  match t with
  | JCTnative (Tgenfloat `Float) -> true
  | _ -> false

let is_gen_float t =
  match t with
  | JCTnative (Tgenfloat _) -> true
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

let is_enum =
  function
  | JCTenum _ -> true
  | _ -> false

let is_bit =
  function
  | JCTenum { ei_type = Int _; _ } ->true
  | _ -> false

let is_root_struct st =
  match st.si_parent with
  | None -> true
  | Some _ -> false

let lub_numeric_types ~loc t1 t2 =
  match t1, t2 with
  | JCTnative (Tgenfloat _), JCTnative (Tgenfloat _) when !Options.float_instruction_set = FISx87 ->
    JCTnative (Tgenfloat `Binary80)
  | JCTnative (Tgenfloat `Float), JCTnative (Tgenfloat `Float) -> JCTnative (Tgenfloat `Float)
  | JCTnative (Tgenfloat _), JCTnative (Tgenfloat _) -> JCTnative (Tgenfloat `Double)
  (* note: there is an invariant that when not in FISx87, `Binary80 never occurs *)
  | JCTnative Tinteger, _ | _, JCTnative Tinteger -> JCTnative Tinteger
  | JCTenum ei1, JCTenum ei2 when Enum_info.equal ei1 ei2 -> JCTenum ei1
  | JCTnative Treal, _ | _, JCTnative Treal -> JCTnative Treal
  | _ ->
    typing_error
      ~loc
      "This operation on numeric values requires potentially unsafe or ambiguous type conversion that should be \
       explicitly specified (the values' types are `%a' and `%a')"
      print_type t1 print_type t2

let rec substruct st =
  function
  | JCtag (st', _) as pc ->
    if st == st' then true
    else
      let vi = struct_root st and vi' = struct_root st' in
      vi == vi' && root_is_union vi ||
      begin match st.si_parent with
      | None -> false
      | Some (p, []) -> substruct p pc
      | Some (_p, _) -> assert false (* TODO *)
      end
  | JCroot vi ->
    struct_root st == vi

let rec superstruct st =
  function
  | JCtag (st', _) ->
    let vi' = struct_root st' in
    not (root_is_union vi') && substruct st' (JCtag (st, []))
  | JCroot _vi ->
    false

let rec deep_substruct ~constrs =
  let true_, false_ = (true, fun _ -> constrs#true_), (false, fun _ -> constrs#true_) in
  let deep_substruct ~assumps = deep_substruct ~constrs ~assumps in
  fun ?(assumps=[]) si si' ->
    let deep_substruct = deep_substruct ~assumps:((si, si') :: assumps) in
    let rec compat_fields fis fis' =
      match fis, fis' with
      | fi :: fis, fi' :: fis' ->
        let (&&) (r, conds) f =
          if r then let r', conds' = f () in r', fun p -> constrs#and_ (conds p) @@ conds' p
          else false_
        in
        let rec compat_type ty ty' =
          match ty, ty' with
          | JCTnative t, JCTnative t' -> t = t', fun _ -> constrs#true_
          | JCTenum ei, JCTenum ei' -> ei.ei_type = ei'.ei_type, fun _ -> constrs#true_
          | JCTlogic (name, args), JCTlogic (name', args') when name = name' ->
            List.fold_left2 (fun acc ty ty' -> acc && fun () -> compat_type ty ty') true_ args args'
          | JCTlogic ("padding", []), _ -> true_
          | JCTpointer (JCtag (si, _), _, _), JCTpointer (JCtag (si', _) as pc', _, _) ->
            if substruct si pc' then true, fun p -> constrs#instanceof (constrs#deref p fi') si
            else if List.memq (si, si') assumps then true_
            else deep_substruct si si'
          | _ -> false_
        in
        (fi.fi_bitsize = fi'.fi_bitsize, fun _ -> constrs#true_) && fun () ->
          compat_type fi.fi_type fi'.fi_type && fun () ->
            compat_fields fis fis'
      | _ :: _, [] -> true_
      | [], _ :: _  -> false_
      | [], [] -> true_
    in
    let r, conds = compat_fields si.si_fields si'.si_fields in
    if r then r, fun p -> constrs#or_ (constrs#instanceof p si) @@ conds p
    else false_

let deep_substruct_nconstrs =
  let module M = Map.Make (PairOrd (StructOrd) (StructOrd)) in
  let cache = ref M.empty in
  let constrs =
    let mk = new nexpr ~label:LabelHere in
    object
      method true_ = mk @@ JCNEconst (JCCboolean true)
      method and_ ne1 ne2 = mk @@ JCNEbinary (ne1, `Bland, ne2)
      method or_ ne1 ne2 = mk @@ JCNEbinary (ne1, `Blor, ne2)
      method deref ne fi = mk @@ JCNEderef (ne, fi.fi_name)
      method instanceof ne st = mk @@ JCNEinstanceof (ne, st.si_name)
    end
  in
  let deep_substruct = deep_substruct ~constrs in
  fun si si' ->
    match M.find_or_none (si, si') !cache with
    | Some r -> r
    | None ->
      let r = deep_substruct si si' in
      cache := M.add (si, si') r !cache;
      r

let same_hierarchy st1 st2 =
  let vi1 = pointer_class_root st1 in
  let vi2 = pointer_class_root st2 in
  vi1 == vi2

let subtype ?(strict=false) t1 t2 =
  match t1, t2 with
  | JCTnative t1, JCTnative t2 ->
    t1 = t2 ||
    (* integer is subtype of real *)
    (match t1, t2 with
     | Tinteger, Treal -> true
     | _ -> false)
  | JCTenum ei1, JCTenum ei2 ->
    Enum_info.(ei1 = ei2) ||
    not strict &&
    Num.ge_num ei1.ei_min ei2.ei_min &&
    Num.le_num ei1.ei_max ei2.ei_max
  | JCTenum _, JCTnative Tinteger -> true
  | JCTnative Tinteger, JCTenum _ -> false
  | JCTlogic s1, JCTlogic s2 -> s1 = s2
  | JCTpointer (JCtag (s1, []), _, _), JCTpointer (pc, _, _) ->
    substruct s1 pc
  | JCTpointer (JCroot v1, _, _), JCTpointer (JCroot v2, _, _) ->
    v1 == v2
  | JCTnull, (JCTnull | JCTpointer _) ->
    true
  | _ -> false

let mintype ~loc t1 t2 =
  try
    match t1, t2 with
    | JCTnative Tinteger, JCTnative Treal
    | JCTnative Treal, JCTnative Tinteger ->
      JCTnative Treal
    | JCTnative n1, JCTnative n2 ->
      if n1 = n2 then t1 else raise Not_found
    (* TODO: integer is subtype of real *)
    | JCTenum e1, JCTenum e2 ->
      if Enum_info.(e1 = e2) then t1 else Common.integer_type
    | (JCTenum _ | JCTnative Tinteger), (JCTenum _ | JCTnative Tinteger) ->
      Common.integer_type
    | JCTlogic s1, JCTlogic s2 ->
      if s1 = s2 then t1 else raise Not_found
    | JCTpointer (JCtag (s1, []), _, _), JCTpointer (pc, _, _) when substruct s1 pc -> t2
    | JCTpointer (pc, _, _), JCTpointer (JCtag(s1, []), _, _) when substruct s1 pc -> t1
    | JCTpointer (JCroot v1, _, _), JCTpointer (JCroot v2, _, _) ->
      if v1 == v2 then t1 else raise Not_found
    | JCTnull, JCTnull -> JCTnull
    | JCTnull, JCTpointer _ -> t2
    | JCTpointer _, JCTnull -> t1
    | JCTany, t | t, JCTany -> t
    | JCTpointer(JCtag (_, _ :: _), _, _), JCTpointer _
    | JCTpointer _, JCTpointer (JCtag (_, _ :: _), _, _) -> assert false
    (* TODO: parameterized type *)
    | _ -> raise Not_found
  with
  | Not_found ->
    typing_error
      ~loc
      "incompatible types: %a and %a"
      print_type t1 print_type t2

let unit_expr e =
  if e#typ = unit_type then
    e
  else
    new expr_with ~typ:unit_type ~region:dummy_region ~original_type:e#typ e

let rec same_type_no_coercion t1 t2 =
  match t1, t2 with
  | JCTnative t1, JCTnative t2 -> t1 = t2
  | JCTenum ei1, JCTenum ei2 -> ei1.ei_type = ei2.ei_type
  | JCTlogic (name1, args1), JCTlogic (name2, args2) ->
    name1 = name2 && List.for_all2 same_type_no_coercion args1 args2
  | JCTpointer (pc1, _, _), JCTpointer (pc2, _, _) ->
    pointer_class_root pc1 == pointer_class_root pc2
  | JCTnull, JCTnull -> true
  | JCTnull, JCTpointer _
  | JCTpointer _, JCTnull -> true
  | _ -> false

let comparable_types t1 t2 =
  match t1, t2 with
  | JCTnative Tinteger, JCTnative Treal -> true
  | JCTnative Treal, JCTnative Tinteger -> true
  | JCTnative t1, JCTnative t2 -> t1 = t2
  | JCTenum ei1, JCTenum ei2 -> Enum_info.(ei1 = ei2)
  | JCTenum _, JCTnative Tinteger -> true
  | JCTnative Tinteger, JCTenum _ -> true
  | JCTlogic s1, JCTlogic s2 -> s1 = s2
  | JCTpointer (pc1, _ ,_), JCTpointer (pc2, _, _) ->
    pointer_class_root pc1 == pointer_class_root pc2
  | JCTnull, JCTnull -> true
  | JCTnull, JCTpointer _
  | JCTpointer _, JCTnull -> true
  | _ -> false

let rec list_assoc_name f id l =
  match l with
  | [] -> raise Not_found
  | fi :: r ->
    if f fi = id then fi
    else list_assoc_name f id r

let rec find_field_struct loc st allow_mutable =
  function
  | ("mutable" | "committed") as x ->
    if allow_mutable && false (* ownership -- to be reimplemented *) then
      let table =
        if x = "mutable" then mutable_fields_table
        else committed_fields_table
      in
      Hashtbl.find table (root_name st)
    else typing_error ~loc "field %s cannot be used here" x
  | f ->
    try
      list_assoc_name (fun f -> f.fi_name) f st.si_fields
    with
    | Not_found ->
      match st.si_parent with
      | None -> raise Not_found
      | Some (st, _) -> find_field_struct loc st allow_mutable f

let find_field_struct loc st allow_mutable f =
  try find_field_struct loc st allow_mutable f
  with
  | Not_found ->
    typing_error ~loc "no field %s in structure %s" f st.si_name

let find_field ~loc ty f allow_mutable =
  match ty with
  | JCTpointer (JCtag (st, _), _, _) -> find_field_struct loc st allow_mutable f
  | JCTpointer (JCroot _, _, _)
  | JCTnative _
  | JCTenum _
  | JCTlogic _
  | JCTnull
  | JCTany -> typing_error ~loc "not a structure type"
  | JCTtype_var _ -> cast_needed ~loc ty

let find_fun_info id = Hashtbl.find functions_env id

let find_logic_info id = Hashtbl.find logic_functions_env id

(* types *)

let rec type_type t =
  match t#node with
  | JCPTnative n -> JCTnative n
  | JCPTpointer (id, _, a, b) ->
    (* first we try the most precise type (the tag) *)
    begin try
      let st, _ = StringHashtblIter.find structs_table id in
      JCTpointer (JCtag (st, []), a, b)
    with
    | Not_found ->
      try
        let vi = StringHashtblIter.find roots_table id in
        JCTpointer (JCroot vi, a, b)
      with
      | Not_found ->
        typing_error ~loc:t#pos "unknown type or tag: %s" id
    end
  | JCPTidentifier (id, l) ->
    try
      JCTtype_var (Type_var.find_type_var uenv id)
    with
    | Not_found ->
      try
        let l = List.map type_type l in
        let _,lp = StringHashtblIter.find logic_type_table id in
        let len_l = List.length l in
        let len_lp = List.length lp in
        if not (len_l = len_lp) then
          typing_error ~loc:t#pos "Here the type %s is used with %i arguments instead of %i " id len_l len_lp;
        JCTlogic (id, l)
      with
      | Not_found ->
        try
          let ei = StringHashtblIter.find enum_types_table id in
          JCTenum ei
        with
        | Not_found ->
          typing_error ~loc:t#pos "unknown type %s" id

let unary_op (t: [< operator_type]) (op: [< unary_op]) = op, t

let bin_op (t: [< operator_type]) (op: [< bin_op]) = op, t

(******************************************************************************)
(*                                  Patterns                                  *)
(******************************************************************************)

(* constants *)

let const c =
  match c with
  | JCCvoid -> unit_type, dummy_region,c
  | JCCinteger _ -> integer_type, dummy_region,c
  | JCCreal _ -> real_type, dummy_region,c
  | JCCboolean _ -> boolean_type, dummy_region, c
  | JCCnull -> null_type, Region.make_var JCTnull "null", c
  | JCCstring _ -> string_type, dummy_region,c

let valid_pointer_type st =
  JCTpointer (st, Some (Num.num_of_int 0), Some (Num.num_of_int 0))

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
      typing_error
        ~loc:pat#pos
        "the variable %s appears twice in the pattern" id;
    try
      StringMap.find id vars
    with
    | Not_found ->
      let vi = var ety id in
      vi.vi_assigned <- true;
      vi
  in
  let tpn, ty, newenv =
    match pat#node with
    | JCPPstruct (id, lpl) ->
      let pc =
        match ety with
        | JCTpointer(pc, _, _) -> pc
        | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull | JCTany
        | JCTtype_var _ ->
          bad_type
            ~loc:pat#pos
            ety
            "this pattern doesn't match a structure nor a variant"
      in
      (* tag *)
      let st = find_struct_info id#pos id#name in
      if not (substruct st pc) then
        typing_error
          ~loc:id#pos
          "tag %s is not a subtag of %s"
          st.si_name (Print_misc.pointer_class pc);
      (* fields *)
      let env, tlpl =
        List.fold_left
          (fun (env, acc) (l, p) ->
             let fi = find_field_struct l#pos st false l#name in
             let env, tp = pattern env vars p fi.fi_type in
             env, (fi, tp) :: acc)
          (env, [])
          lpl
      in
      JCPstruct (st, List.rev tlpl), valid_pointer_type (JCtag(st, [])), env
    | JCPPvar id ->
      let vi = get_var ety id in
      JCPvar vi, ety, (id#name, vi) :: env
    | JCPPor(p1, p2) ->
      let _, tp1 = pattern env vars p1 ety in
      let vars = pattern_vars vars tp1 in
      let env, tp2 = pattern env vars p2 ety in
      JCPor (tp1, tp2), ety, env
    | JCPPas(p, id) ->
      let env, tp = pattern env vars p ety in
      let vi = get_var (tp#typ) id in
      JCPas (tp, vi), ety, (id#name, vi) :: env
    | JCPPany ->
      JCPany, ety, env
    | JCPPconst c ->
      let ty, _, c = const c in
      Type_var.add uenv pat#pos ty ety;
      JCPconst c, ety, env
  in
  newenv, new pattern ~typ:ty ~pos:pat#pos tpn

let pattern = pattern [] StringMap.empty

(******************************************************************************)
(*                                   Terms                                    *)
(******************************************************************************)

let num_op t (op: [< arithmetic_op | mod_arithmetic_op ]) = op, t

let num_un_op t (op: [< unary_op ]) e = JCTunary (unary_op t op, e)

let make_logic_unary_op ~loc ~(op : unary_op) e2 =
  let t2 = e2#typ in
  match op with
  | `Unot ->
    Type_var.add uenv loc (JCTnative Tboolean) t2;
    t2, dummy_region, num_un_op (operator_of_native Tboolean) op  e2
  | `Uminus ->
    check_not_var ~loc t2;
    if is_numeric t2 then
      let t = lub_numeric_types ~loc t2 t2 in
      t, dummy_region, num_un_op (operator_of_type t) `Uminus e2
    else
      typing_error ~loc "numeric type expected"
  | `Uminus_mod when is_enum t2 ->
    t2, dummy_region, num_un_op (operator_of_type t2) `Uminus_mod e2
  | `Uminus_mod -> typing_error ~loc "enum type expected"
  | `Ubw_not when is_bit t2 ->
    t2, dummy_region, num_un_op (operator_of_type t2) `Ubw_not e2
  | `Ubw_not -> typing_error ~loc "pre-defined integral type expected"

(* [term_expand t1 t2 e] prepares [e] of type [t1] for coercion to type [t2] by expanding it to an unbounded type *)
let term_expand t1 t2 e =
  let tn1, e =
    match t1 with
    | JCTenum _ri -> Tinteger, term_with_node ~typ:(JCTnative Tinteger) e @@ JCTrange_cast (e, None)
    | JCTnative t -> t, e
    | _ -> assert false
  in
  match tn1, t2 with
  | Tinteger, JCTnative Treal ->
    begin match e#node with
    | JCTconst (JCCinteger n) ->
      new term
        ~typ:real_type
        ~region:e#region
        ~mark:e#mark
        ~pos:e#pos
        (JCTconst (JCCreal (n ^ ".0")))
    | _ ->
      let app = {
        app_fun = real_of_integer;
        app_args = [e];
        app_region_assoc = [];
        app_label_assoc = [];
      }
      in
      new term
        ~typ:real_type
        ~region:e#region
        ~mark:e#mark
        ~pos:e#pos
        (JCTapp app)
    end
  | _ -> e

(* Only expanding coercions done by term_precoerce can be implicit *)
let term_implicit_coerce t1 t2 e =
  let result () = term_expand t1 t2 e in
  let fail () =
    typing_error
      ~loc:e#pos
      "Invalid implicit coercion from type `%a' to type `%a'"
      print_type t1 print_type t2
  in
  match t1, t2 with
  | JCTnative t1, JCTnative t2 ->
    begin match t1, t2 with
    | Tinteger, Treal -> result ()
    | _ when t1 = t2 -> e
    | _ -> fail ()
    end
  | JCTenum e1, JCTenum e2 when e1 == e2 -> e
  | JCTenum _, JCTenum _ -> fail ()
  | JCTenum _, JCTnative Tinteger -> result ()
  | JCTnative Tinteger, JCTenum _ -> fail ()
  | JCTlogic s1, JCTlogic s2 when s1 = s2 -> e
  | JCTlogic _, JCTlogic _ -> fail ()
  | JCTpointer (JCtag (s1, []), _, _), JCTpointer (pc, _, _) when substruct s1 pc -> e
  | JCTpointer (JCtag _, _, _), JCTpointer _ -> fail ()
  | JCTpointer (JCroot v1, _, _), JCTpointer (JCroot v2, _, _) when v1 == v2-> e
  | JCTpointer (JCroot _, _, _), JCTpointer (JCroot _, _, _) -> fail ()
  | JCTnull, (JCTnull | JCTpointer _) -> e
  | _ -> fail ()

let logic_bin_op (t : [< operator_type ]) (op : [< bin_op ]) : term_bin_op = bin_op t op

let make_logic_bin_op ~loc ~(op : bin_op) e1 e2 =
  let t1 = e1#typ and t2 = e2#typ in
  (** Test only that neither t1 nor t2 is a type variable,
      thus they can contain type variables *)
  check_not_var ~loc t1;
  check_not_var ~loc t2;
  let return t ~region e =
    t, region, e
  in
  let return_numeric ?(region=dummy_region) ?t () =
    let t' = lub_numeric_types ~loc t1 t2 in
    return
      (t |? t')
      ~region
      (JCTbinary (term_implicit_coerce t1 t' e1,
                 logic_bin_op (operator_of_type t') op,
                 term_implicit_coerce t2 t' e2))
  in
  let return_boolean = return_numeric ~t:boolean_type in
  let return_numeric = return_numeric ?t:None in
  match op with
  | `Bgt | `Blt | `Bge | `Ble when is_numeric t1 && is_numeric t2 ->
    return_boolean ()
  | `Bgt | `Blt | `Bge | `Ble ->
    typing_error ~loc "numeric types expected for >, <, >= and <="
  | `Beq | `Bneq when is_numeric t1 && is_numeric t2 ->
    return_boolean ()
  | `Beq | `Bneq
    when is_pointer_type t1 && is_pointer_type t2 && comparable_types t1 t2 ->
    return
      boolean_type
      ~region:dummy_region
      (JCTbinary (e1, logic_bin_op `Pointer op, e2))
  | `Beq | `Bneq ->
    typing_error ~loc "numeric or compatible pointer types expected for == and !="
  | `Badd when is_pointer_type t1 && is_integer t2 ->
    return
      t1
      ~region:e1#region
      (JCTshift (e1, term_implicit_coerce t2 (JCTnative Tinteger) e2))
  | `Badd when is_numeric t1 && is_numeric t2 ->
    return_numeric ()
  | `Badd ->
    typing_error ~loc "unexpected types for +"
  | `Badd_mod when is_enum t1 && same_type_no_coercion t1 t2 ->
    return_numeric ()
  | `Badd_mod ->
    typing_error ~loc "unexpected types for +%%"
  | `Bsub when is_pointer_type t1 && is_integer t2 ->
    let e2 =
      new term_with
        e2
        ~node:(Tuple.T3.trd @@ make_logic_unary_op loc `Uminus (term_implicit_coerce t2 (JCTnative Tinteger) e2))
    in
    return t1 ~region:e1#region (JCTshift (e1, e2))
  | `Bsub when is_pointer_type t1 && is_pointer_type t2 && comparable_types t1 t2 ->
    return integer_type ~region:dummy_region (JCTbinary (e1, bin_op `Pointer `Bsub, e2))
  | `Bsub when is_numeric t1 && is_numeric t2 ->
    return_numeric ()
  | `Bsub ->
    typing_error ~loc "unexpected types for -"
  | `Bsub_mod when is_enum t1 && same_type_no_coercion t1 t2 ->
    return_numeric ()
  | `Bsub_mod ->
    typing_error ~loc "unexpected types for +%%"
  | `Bmul | `Bdiv | `Bmod
    when is_numeric t1 && is_numeric t2 ->
    return_numeric ()
  | `Bmul_mod | `Bdiv_mod | `Bmod_mod
    when is_enum t1 && is_enum t2 ->
    return_numeric ()
  | `Bbw_and | `Bbw_or | `Bbw_xor
  | `Blogical_shift_right | `Barith_shift_right | `Bshift_left | `Bshift_left_mod
    when is_bit t1 && is_bit t2 ->
    return_numeric ()
  | `Bmul | `Bdiv | `Bmod ->
    typing_error ~loc "numeric types expected for *, / or %%"
  | `Bmul_mod | `Bdiv_mod | `Bmod_mod ->
    typing_error ~loc "enum types expected for *%% or /%%"
  | `Bbw_and | `Bbw_or | `Bbw_xor
  | `Blogical_shift_right | `Barith_shift_right | `Bshift_left| `Bshift_left_mod  ->
    typing_error ~loc "pre-defined integral types expected for bitwise operations"
  | `Bland | `Blor when (match t1, t2 with JCTnative Tboolean, JCTnative Tboolean -> true | _ -> false) ->
    return
      (JCTnative Tboolean)
      ~region:dummy_region
      (JCTbinary (e1, logic_bin_op (operator_of_native Tboolean) op, e2))
  | `Bland | `Blor -> typing_error ~loc "booleans expected"
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
      typing_error ~loc:e#pos "label `%a' not found" Print_misc.label x
  in
  let iter_subs ?(env=env) label =
    List.iter
      (fun e -> ignore (type_labels env ~result_label label e))
      (Iterators.INExpr.subs e)
  in
  e#set_label label;
  match e#node with
  | JCNEconst _ | JCNEderef _ | JCNEbinary _
  | JCNEunary _ | JCNEassign _ | JCNEinstanceof _ | JCNEcast _ | JCNEcast_mod _
  | JCNEif _ | JCNEoffset _ | JCNEaddress _ | JCNEbase_block _ | JCNEfresh _
  | JCNEalloc _ | JCNEfree _ | JCNEreinterpret _ | JCNElet _
  | JCNEassert _ | JCNEloop _ | JCNEreturn _ | JCNEtry _
  | JCNEthrow _ | JCNEpack _ | JCNEunpack _ | JCNEmatch _ | JCNEquantifier _
  | JCNEmutable _ | JCNEeqtype _ | JCNEsubtype _ | JCNErange _ ->
    iter_subs label;
    env
  | JCNEvar id ->
    if id = "\\result" then begin
      match label, result_label with
      | Some lab1, Some lab2 ->
        if lab1 <> lab2 then
          typing_error
            ~loc:e#pos
            "\\result not allowed here (lab1 = %a, lab2= %a)"
            Print_misc.label lab1 Print_misc.label lab2
      | None, _
      | _, None -> typing_error ~loc:e#pos "\\result not allowed here"
    end;
    env
  | JCNEcontract (req, dec, behs, e) ->
    ignore (type_labels_opt env ~result_label:None (Some LabelHere) req);
    Option.iter
      (fun (dec, _) ->
         ignore (type_labels env ~result_label:None (Some LabelHere) dec)) dec;
    List.iter (behavior_labels env) behs;
    type_labels env ~result_label (Some LabelHere) e
  | JCNEapp (_, l, _) ->
    List.iter (check e) l;
    iter_subs label;
    env
  | JCNEold _ ->
    check e LabelOld;
    iter_subs (Some LabelOld);
    env
  | JCNEat (_, l) ->
    check e l;
    iter_subs (Some l);
    env
  | JCNEblock el ->
    List.fold_left
      (fun env e -> type_labels env ~result_label label e)
      env el
  | JCNElabel (lab, _) ->
    let lab = {
      lab_name = lab;
      lab_final_name = lab;
      lab_times_used = 0;
    } in
    let env = (LabelName lab) :: env in
    iter_subs ~env label;
    env

and type_labels_opt env ~result_label label e =
  match e with
  | None -> env
  | Some e -> type_labels env ~result_label label e

and behavior_labels env
    (_loc, _id, _throws, assumes, requires, assigns, allocates, ensures) =
  let here = Some LabelHere in
  let _ = type_labels_opt env ~result_label:None here assumes in
  let _ = type_labels_opt env ~result_label:None here requires in
  let env = LabelOld :: LabelPost :: env in
  Option.iter
    (fun (_, a) ->
       List.iter
         (fun e ->
            ignore(type_labels env
                     ~result_label:(Some LabelPost) (Some LabelOld) e)) a)
    assigns;
  Option.iter
    (fun (_, a) ->
       List.iter
         (fun e ->
            ignore(type_labels env
                     ~result_label:(Some LabelHere) (Some LabelHere) e)) a)
    allocates;
  let _ = type_labels env ~result_label:here here ensures in
  ()

let type_labels env ~result_label label e =
  ignore (type_labels env ~result_label label e)

let get_label e =
  match e#label with
  | None -> typing_error ~loc:e#pos "a memory state is needed here (\\at missing?)"
  | Some l -> l

let label_assoc ~loc id cur_label fun_labels effective_labels =
  match cur_label, fun_labels, effective_labels with
  | Some l, [lf], [] -> [lf,l]
  | _ ->
    try
      List.map2
        (fun l1 l2 -> (l1,l2))
        fun_labels effective_labels
    with
    | Invalid_argument _ ->
      typing_error
        ~loc
        "wrong number of labels for %s (expected %d, got %d)"
        id (List.length fun_labels) (List.length effective_labels)

let rec term env (e : nexpr) =
  let ft = term env in
  let lab = ref "" in
  let label () = get_label e in
  let t, tr, te =
    match e#node with
    | JCNEconst c ->
      let t, tr, c = const c in
      t, tr, JCTconst c
    | JCNElabel (l, e1) ->
      let te1 = ft e1 in
      lab := l;
      te1#typ, te1#region, te1#node
    | JCNEvar id ->
      begin try
        let vi =
          try List.assoc id env
          with
          | Not_found -> Hashtbl.find variables_env id
        in
        vi.vi_type, vi.vi_region, JCTvar vi
      with
      | Not_found ->
        let pi =
          try Hashtbl.find logic_functions_env id
          with
          | Not_found ->
            typing_error ~loc:e#pos "unbound term identifier %s" id
        in
        if pi.li_parameters <> [] then
          typing_error ~loc:e#pos "applying logic function `%s' without arguments" id;
        let app = {
          app_fun = pi;
          app_args = [];
          app_region_assoc = [];
          app_label_assoc = [];
        } in
        let ty =
          match pi.li_result_type with
          | Some t -> t
          | None -> assert false (* check it is a function *)
        in
        let ty = (Type_var.instance pi.li_poly_args) ty in
        ty, Region.make_var ty pi.li_name, JCTapp app
      end
    | JCNEderef (e1, f) ->
      let te1 = ft e1 in
      let fi = find_field ~loc:e#pos te1#typ f true in
      fi.fi_type,
      Region.make_field te1#region fi,
      JCTderef (te1, label (), fi)
    | JCNEbinary (e1, op, e2) ->
      make_logic_bin_op ~loc:e#pos ~op (ft e1) (ft e2)
    | JCNEunary (op, e1) ->
      make_logic_unary_op ~loc:e#pos ~op (ft e1)
    | JCNEapp (id, labs, args) ->
      begin try
        let pi = find_logic_info id in
        let subst = Type_var.instance pi.li_poly_args in
        let tl =
          try
            List.map2
              (fun vi e ->
                 let ty = subst vi.vi_type in
                 let te = ft e in
                 let te = term_implicit_coerce te#typ ty te in
                 Type_var.add uenv te#pos te#typ ty;
                 te)
              pi.li_parameters
              args
          with
          | Invalid_argument _ ->
            typing_error
              ~loc:e#pos
              "wrong number of arguments for %s" id
        in
        let ty =
          match pi.li_result_type with
          | None -> JCTnative Tboolean
          | Some ty -> ty
        in
        let ty = Type_var.subst uenv (subst ty) in
        let label_assoc =
          label_assoc ~loc:e#pos id e#label pi.li_labels labs
        in
        let app = {
          app_fun = pi;
          app_args = tl;
          app_region_assoc = [];
          app_label_assoc = label_assoc;
        } in
        ty, Region.make_var ty pi.li_name, JCTapp app
      with
      | Not_found ->
        typing_error ~loc:e#pos "unbound logic function identifier %s" id
      end
    | JCNEinstanceof (e1, t) ->
      boolean_type,
      dummy_region,
      JCTinstanceof (ft e1, label (), find_struct_info e#pos t)
    | JCNEcast (e1, t) ->
      let te1 = ft e1 in
      let ty = type_type t in
      begin match ty with
      | JCTnative Tinteger ->
        if is_integer te1#typ then
          integer_type, te1#region, JCTrange_cast (te1, None)
        else
          bad_type ~loc:e#pos ty "bad cast to integer"
      | JCTnative Treal ->
        if is_integer te1#typ then
          real_type, te1#region, JCTreal_cast (te1, Integer_to_real)
        else if is_real te1#typ then
          real_type, te1#region, te1#node
        else if is_double te1#typ then
          real_type, te1#region, JCTreal_cast (te1, Double_to_real)
        else if is_float te1#typ then
          real_type, te1#region, JCTreal_cast (te1, Float_to_real)
        else
          bad_type ~loc:e#pos te1#typ "bad cast to real"
      | JCTnative (Tgenfloat f) ->
        if is_real te1#typ || is_integer te1#typ then
          JCTnative (Tgenfloat f), te1#region, JCTreal_cast (te1, Round (f, Round_nearest_even))
        else
          begin match te1#typ with
          | JCTnative (Tgenfloat f1) ->
            let e =
              match f1, f with
              | `Binary80,`Binary80 -> te1#node
              | `Double,`Double -> te1#node
              | `Float,`Float -> te1#node
              | _ ->
                JCTreal_cast (te1, Round (f, Round_nearest_even))
            in
            JCTnative (Tgenfloat f), te1#region, e
          | _ -> bad_type ~loc:e#pos te1#typ "bad cast to floating-point number"
          end
      | JCTnative _ -> assert false (* TODO *)
      | JCTenum ri ->
        if is_integer te1#typ || is_enum te1#typ then
          JCTenum ri, dummy_region, JCTrange_cast (te1, Some ri)
        else
          bad_type ~loc:e#pos te1#typ "integer type expected"
      | JCTpointer (JCtag (st, _) as st_pc, _, _) ->
        begin match te1#typ with
        | JCTpointer (st1, a, b) ->
          if superstruct st st1 then
            ty, te1#region, te1#node
          else if substruct st st1 then
            JCTpointer (JCtag (st, []), a, b), te1#region, JCTdowncast (te1, label (), st)
          else
            begin match st1 with
            | JCroot ri | JCtag ({ si_root = Some ri; _ }, [])
              when ri == struct_root st && List.length ri.ri_hroots > 1 ->
              (* union downcast -- currently translated similar to usual one ==> TODO: support unions *)
              JCTpointer (JCtag (st, []), a, b), te1#region, JCTdowncast (te1, label (), st)
            | JCtag (st', []) when same_hierarchy st_pc st1 ->
              let deep_substruct = deep_substruct_nconstrs in
              let r, _ = deep_substruct st' st in
              if r then ty, te1#region, te1#node (* implcit cast to deep superstruct *)
              else
                let r, conds = deep_substruct st st' in
                if r then (* deep downcast *)
                  let typ = JCTpointer (JCtag (st, []), a, b) in
                  let term = new term ~typ ~region:te1#region
                  and conds = term env (conds e1) in
                  typ, te1#region, JCTif (conds, term te1#node, term (JCTdowncast (te1, label (), st)))
                else (* sidecast *)
                  JCTpointer (JCtag (st, []), None, None), te1#region, JCTsidecast (te1, label (), st)
            | _ -> typing_error ~loc:e#pos "invalid cast: structures from different hierarchies"
            end
        | JCTnull -> typing_error ~loc:e#pos "invalid cast"
        | JCTnative _ | JCTlogic _ | JCTenum _ | JCTany
        | JCTtype_var _ -> bad_type ~loc:e#pos te1#typ "only structures can be cast"
        end
      | JCTpointer (JCroot _, _, _)  -> assert false (* TODO *)
      | JCTtype_var _| JCTlogic _| JCTany| JCTnull -> assert false (* TODO *)
      end
    | JCNEcast_mod (e1, t) ->
      let te1 = ft e1 in
      let ty = type_type t in
      begin match ty with
      | JCTenum ri when is_integer te1#typ || is_enum te1#typ ->
        JCTenum ri, dummy_region, JCTrange_cast_mod (te1, ri)
      | _ -> typing_error ~loc:e#pos "invalid modulo cast"
      end
    | JCNEif (e1, e2, e3) ->
      let te1 = ft e1 and te2 = ft e2 and te3 = ft e3 in
      Type_var.add uenv e#pos (JCTnative Tboolean) te1#typ;
      let t =
        let t2 = te2#typ and t3 = te3#typ in
        if subtype ~strict:true t2 t3 then t3
        else if subtype ~strict:true t3 t2 then t2
        else begin
          Type_var.add uenv e#pos t2 t3;
          Type_var.subst uenv t2
        end
      in
      t, te2#region, JCTif(te1, te2, te3)
    | JCNEoffset (k, e1) ->
      let te1 = ft e1 in
      begin match te1#typ with
      | JCTpointer (JCtag(st, _), _, _) ->
        integer_type, dummy_region, JCToffset(k, te1, st)
      | JCTpointer(JCroot _, _, _) ->
        assert false (* TODO *)
      | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull | JCTany -> typing_error ~loc:e#pos "pointer expected"
      | JCTtype_var _ -> cast_needed ~loc:te1#pos te1#typ
      end
    | JCNEaddress (Addr_absolute,e1) ->
      let te1 = ft e1 in
      if is_integer te1#typ then
        JCTnull, dummy_region, JCTaddress(Addr_absolute,te1)
      else
        bad_type ~loc:te1#pos te1#typ "integer expected"
    | JCNEaddress (Addr_pointer, e1) ->
      let te1 = ft e1 in
      begin match te1#typ with
      | JCTpointer(JCtag(_st, _), _, _) ->
        integer_type, dummy_region, JCTaddress(Addr_pointer,te1)
      | JCTpointer(JCroot _, _, _) ->
        assert false (* TODO *)
      | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull | JCTany -> typing_error ~loc:e#pos "pointer expected"
      | JCTtype_var _ -> cast_needed ~loc:te1#pos te1#typ
      end
    | JCNEbase_block (e1) ->
      let te1 = ft e1 in
      if is_pointer_type te1#typ then
        te1#typ, te1#region, JCTbase_block(te1)
      else
        bad_type ~loc:te1#pos te1#typ "pointer expected"
    | JCNElet (pty, id, Some e1, e2) ->
      let te1 = ft e1 in
      let ty =
        match pty with
        | None -> te1#typ
        | Some pty ->
          let ty = type_type pty in
          Type_var.add uenv e1#pos te1#typ ty;
          Type_var.subst uenv ty
      in
      let vi = var ~bound:true ty id in
      let te2 = term ((id, vi) :: env) e2 in
      te2#typ, te2#region, JCTlet (vi, term_implicit_coerce ty te1#typ te1, te2)
    | JCNElet (_ (* Some pty *), _id, None, _e2) ->
      typing_error ~loc:e#pos "let without initial value"
    | JCNEmatch (arg, pel) ->
      let targ = ft arg in
      let rty, tpel =
        match pel with
        | [] -> assert false (* should not be allowed by the parser *)
        | (p1, e1) :: rem ->
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
      rty, targ#region, JCTmatch (targ, List.rev tpel)
    | JCNEold e1 ->
      let te1 = ft e1 in
      te1#typ, te1#region, JCTold te1
    | JCNEat(e1, lab) ->
      let te1 = ft e1 in
      te1#typ, te1#region, JCTat (te1, lab)
    | JCNEmutable (_e, _t) -> assert false (* TODO *)
    | JCNErange (Some e1, Some e2) ->
      let e1 = ft e1 and e2 = ft e2 in
      let t1 = e1#typ and t2 = e2#typ in
      assert (is_numeric t1 && is_numeric t2);
      let t = lub_numeric_types ~loc:e#pos t1 t2 in
      t, dummy_region, JCTrange (Some (term_implicit_coerce t1 t e1), Some (term_implicit_coerce t2 t e2))
    | JCNErange (Some e, None) ->
      let e = ft e in
      let t = e#typ in
      assert (is_numeric t);
      t, dummy_region,JCTrange (Some e,None)
    | JCNErange (None, Some e) ->
      let e = ft e in
      let t = e#typ in
      assert (is_numeric t);
      t, dummy_region, JCTrange (None,Some e)
    | JCNErange (None, None) ->
      integer_type, dummy_region, JCTrange(None,None)
    (* Not terms: *)
    | JCNEassign _ | JCNEalloc _ | JCNEfree _ | JCNEreinterpret _ | JCNEblock _ | JCNEassert _ | JCNEfresh _
    | JCNEloop _ | JCNEreturn _ | JCNEtry _ | JCNEthrow _ | JCNEpack _
    | JCNEunpack _ | JCNEquantifier _ | JCNEcontract _
    | JCNEeqtype _ | JCNEsubtype _ ->
      typing_error
        ~loc:e#pos
        "construction %a not allowed in logic terms"
        Print_n.expr e
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

let rel_bin_op t (op: [< comparison_op]) =
  (bin_op t op :> pred_rel_op)

let make_and a1 a2 =
  match a1#node, a2#node with
  | JCAtrue, _ -> a2
  | _, JCAtrue -> a1
  | JCAand l1, JCAand l2 -> new assertion (JCAand (l1 @ l2))
  | JCAand l1, _ -> new assertion (JCAand(l1 @ [a2]))
  | _ , JCAand l2 -> new assertion (JCAand (a1 :: l2))
  | _ -> new assertion (JCAand [a1; a2])

let rec make_and_list =
  function
  | [] -> assert false
  | [a] -> a
  | f :: r -> make_and f (make_and_list r)

let make_or a1 a2 =
  match a1#node, a2#node with
  | JCAfalse, _ -> a2
  | _, JCAfalse -> a1
  | JCAor l1, JCAor l2 -> new assertion (JCAor (l1 @ l2))
  | JCAor l1 , _  -> new assertion (JCAor (l1 @ [a2]))
  | _ , JCAor l2 -> new assertion (JCAor (a1 :: l2))
  | _ -> new assertion (JCAor [a1; a2])

let make_rel_bin_op ~loc ~(op : [< comparison_op]) e1 e2 =
  let t1 = e1#typ and t2 = e2#typ in
  check_not_var ~loc:e1#pos t1;
  check_not_var ~loc:e2#pos t2;
  let return () =
    let t = lub_numeric_types ~loc t1 t2 in
    JCArelation
      (term_implicit_coerce t1 t e1,
       rel_bin_op (operator_of_type t) op,
       term_implicit_coerce t2 t e2)
  in
  match op with
  | `Bgt | `Blt | `Bge | `Ble when is_numeric t1 && is_numeric t2 ->
    return ()
  | `Bgt | `Blt | `Bge | `Ble ->
    typing_error ~loc "numeric types expected for >, <, >= and <="
  | `Beq | `Bneq when is_numeric t1 && is_numeric t2 ->
    return ()
  | `Beq | `Bneq ->
    let t = eq_operator_of_type (mintype loc t1 t2) in
    if comparable_types t1 t2 then
      JCArelation (e1, rel_bin_op t op, e2)
    else
      typing_error ~loc "terms should have the same type for == and !="

let tag env hierarchy t =
  let check_hierarchy loc st =
    if hierarchy <> "" &&
       root_name st != hierarchy
    then
      typing_error
        ~loc
        "this is in the hierarchy of %s, while it should be in the hierarchy of %s"
        (root_name st)
        hierarchy
  in
  let tt =
    match t#node with
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
      | _ -> bad_type ~loc:tof#pos ttof#typ "tag pointer expression expected"
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
    | JCTbottom, JCTtypeof (_, st)
    | JCTtypeof (_, st), JCTbottom -> Some st
    | JCTtag st1, JCTtag st2
    | JCTtypeof (_, st1), JCTtag st2
    | JCTtag st1, JCTtypeof (_, st2)
    | JCTtypeof (_, st1), JCTtypeof (_, st2) ->
      if st1.si_hroot != st2.si_hroot then
        typing_error
          ~loc:e#pos
          "the hierarchy %s and %s are different"
          (root_name st1)
          (root_name st2)
      else
        Some st1.si_hroot
  in
  let ta =
    match e#node with
    | JCNElabel(l, e) ->
      let te = fa e in
      lab := l;
      te#node
    | JCNEbinary (e1, (`Bland | `Blor | `Bimplies | `Biff as op), e2) ->
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
        let subst = Type_var.instance pi.li_poly_args in
        let tl = try
            List.map2
              (fun vi e ->
                 let ty = subst vi.vi_type in
                 let te = ft e in
                 Type_var.add uenv te#pos te#typ ty;
                 te)
              pi.li_parameters args
          with
          | Invalid_argument _ ->
            typing_error ~loc:e#pos "wrong number of arguments for %s" id
        in
        let label_assoc =
          label_assoc e#pos id e#label pi.li_labels labs
        in
        let app = {
          app_fun = pi;
          app_args = tl;
          app_region_assoc = [];
          app_label_assoc = label_assoc;
        } in
        JCAapp app
      with
      | Not_found ->
        typing_error ~loc:e#pos "unbound predicate identifier %s" id
      end
    | JCNEinstanceof(e1, t) ->
      JCAinstanceof (ft e1, label (), find_struct_info e#pos t)
    | JCNEcast _ -> assert false (* TODO *)
    | JCNEcast_mod _ -> assert false (* TODO *)
    | JCNEif(e1,e2,e3) ->
      let te1 = ft e1 and te2 = fa e2 and te3 = fa e3 in
      Type_var.add uenv e1#pos te1#typ (JCTnative Tboolean);
      JCAif(te1,te2,te3)
    | JCNElet (ty, id, Some e1, e2) ->
      let te1 = ft e1 in
      let ty1 =
        match ty with
        | None -> te1#typ
        | Some ty ->
          let ty = type_type ty in
          if comparable_types ty te1#typ then ty
          else
            bad_type
              ~loc:e1#pos
              te1#typ
              "type not compatible with declared type"
      in
      let vi = var ~bound:true ty1 id in
      let env = (id, vi) :: env in
      let te2 = assertion env e2 in
      JCAlet (vi, term_implicit_coerce te1#typ ty1 te1, te2)
    | JCNElet (_ty, _id, None, _e2) ->
      assert false (* TODO *)
    | JCNEmatch (arg, pel) ->
      let targ = ft arg in
      let tpal = List.map
          (fun (pat, body) ->
             let vars, tpat = pattern pat targ#typ in
             let tbody = assertion (vars @ env) body in
             tpat, tbody)
          pel
      in
      JCAmatch (targ, tpal)
    | JCNEquantifier (q, ty, idl, trigs, e1) ->
      let ty = type_type ty in
      (make_quantifier q e#pos ty idl env trigs e1)#node
    | JCNEold e1 ->
      JCAold(fa e1)
    | JCNEat(e1, lab) ->
      JCAat(fa e1, lab)
    | JCNEmutable(e, t) ->
      let te = ft e in
      let te_st =
        match te#typ with
        | JCTpointer(JCtag(st, _), _, _) -> st
        | _ -> bad_type ~loc:e#pos te#typ "tag pointer expression expected"
      in
      let tt = tag env (root_name te_st) t in
      JCAmutable (te, te_st, tt)
    | JCNEeqtype (tag1, tag2) ->
      let ttag1 = tag env "" tag1 in
      let ttag2 = tag env "" tag2 in
      let st = struct_for_tags ttag1 ttag2 in
      JCAeqtype (ttag1, ttag2, st)
    | JCNEsubtype (tag1, tag2) ->
      let ttag1 = tag env "" tag1 in
      let ttag2 = tag env "" tag2 in
      let st = struct_for_tags ttag1 ttag2 in
      JCAsubtype (ttag1, ttag2, st)
    (* Boolean terms: *)
    | JCNEconst _ | JCNEvar _ | JCNEderef _ ->
      let t = ft e in
      begin match t#typ with
      | JCTnative Tboolean -> JCAbool_term t
      | _ -> typing_error ~loc:e#pos "non boolean expression"
        end
    | JCNEfresh e1 ->
      let te1 = ft e1 in
      if is_pointer_type te1#typ then JCAfresh(te1)
      else
        bad_type ~loc:te1#pos te1#typ "pointer expected"
    (* Not assertions: *)
    | JCNEoffset _ | JCNEaddress _ | JCNEbase_block _
    | JCNErange _ | JCNEassign _ | JCNEalloc _ | JCNEfree _ | JCNEreinterpret _
    | JCNEassert _ | JCNEblock _ | JCNEloop _ | JCNEreturn _ | JCNEtry _
    | JCNEthrow _ | JCNEpack _ | JCNEunpack _ | JCNEbinary _ | JCNEunary _
    | JCNEcontract _ ->
      typing_error ~loc:e#pos "construction not allowed in logic assertions"
  in
  new assertion
    ~mark: !lab
    ?label: e#label
    ~pos: e#pos
    ta

and make_quantifier q loc ty idl env trigs e : assertion =
  match idl with
    | [] -> assertion env e (*Here the triggers disappear if idl start empty*)
    | id :: r ->
        let vi = var ~bound:true ty id#name in
        let env = ((id#name, vi) :: env) in
        let trigs_id,trigs_r =
          match r with
            | [] -> (*id is the last variable,
                      the trigger should stay here*)
                triggers env trigs,[]
            | _ -> [],trigs in
        let f =
          JCAquantifier (q, vi, trigs_id, make_quantifier q loc ty r env trigs_r e)
        in
        new assertion ~pos:loc f

and triggers env l =
  let pat e =
    match e#node with
    | JCNEapp (id,_,_) ->
        let pi = find_logic_info id in
        (match pi.li_result_type with
          | None ->   JCAPatP (assertion env e)
          | Some _ -> JCAPatT (term env e))
    | JCNEat _ | JCNEinstanceof _ | JCNEoffset _ -> JCAPatT (term env e)
    | JCNEbinary (_, #comparison_op, _) -> JCAPatP (assertion env e)
    | _ -> typing_error ~loc:e#pos "IllformedPattern" in
  List.map (List.map pat) l

(******************************************************************************)
(*                                Expressions                                 *)
(******************************************************************************)

let loop_annot =
  let cnt = ref 0 in
  fun ~behaviors ~free_invariant ~variant ->
    incr cnt;
    {
      loop_tag = !cnt;
      loop_behaviors = behaviors;
      loop_free_invariant = free_invariant;
      loop_variant = variant;
    }

let rec location_set env e =
  let ty, r, locs_node =
    match e#node with
    | JCNElabel (_l, _e) ->
      assert false (* TODO *)
    | JCNEvar id ->
      let vi =
        try List.assoc id env
        with
        | Not_found ->
          try Hashtbl.find variables_env id
          with
          | Not_found ->
            typing_error ~loc:e#pos "unbound identifier %s" id
      in
      begin match vi.vi_type with
      | JCTpointer _ ->
        vi.vi_type, vi.vi_region, JCLSvar vi
      | _ -> assert false
      end
    | JCNEbinary (e, `Badd, i) ->
      begin try
        let ty, tr, te = location_set env e in
        let ti = term env i in
        begin match ty, ti#typ with
        | JCTpointer (_st, _, _), t2 when is_integer t2 ->
          begin match ti#node with
          | JCTrange (t1, t2) -> ty, tr, JCLSrange (te, t1, t2)
          | _ -> ty, tr, JCLSrange (te, Some ti, Some ti)
          end
        | JCTpointer _, _ ->
          typing_error
            ~loc:i#pos
            "integer expected, %a found"
            print_type ti#typ
        | _ ->  typing_error ~loc:e#pos "pointer expected"
        end
      with
      | Typing_error _ ->
        let t1 = term env e in
        let ty, tr, te = t1#typ, t1#region, t1 in
        let ti = term env i in
        begin match ty, ti#typ with
        | JCTpointer (_st, _, _), t2 when is_integer t2 ->
          begin match ti#node with
          | JCTrange (t1, t2) -> ty, tr, JCLSrange_term (te, t1, t2)
          | _ -> ty, tr, JCLSrange_term (te, Some ti, Some ti)
          end
        | JCTpointer _, _ ->
          typing_error
            ~loc:i#pos
            "integer expected, %a found"
            print_type ti#typ
        | _ ->
          typing_error ~loc:e#pos "pointer expected"
        end
      end
    | JCNEbinary _ ->
      assert false
    | JCNEderef(ls, f) ->
      let t,tr,tls = location_set env ls in
      let fi = find_field e#pos t f false in
      let fr = Region.make_field tr fi in
      fi.fi_type, fr, JCLSderef(tls, get_label e, fi, fr)
    | JCNEat(ls, lab) ->
      let t,tr,tls = location_set env ls in
      t,tr,JCLSat(tls,lab)
    | JCNEfresh _
    | JCNErange _ | JCNEeqtype _ | JCNEmutable _ | JCNEold _
    | JCNEquantifier _ | JCNEmatch _ | JCNEunpack _ | JCNEpack _ | JCNEthrow _
    | JCNEtry _ |JCNEreturn _ | JCNEloop _ |JCNEblock _ | JCNEassert _
    | JCNElet _ |JCNEfree _ | JCNEalloc _ | JCNEreinterpret _ | JCNEoffset _ | JCNEaddress _
    | JCNEif _ | JCNEcast _ | JCNEcast_mod _ | JCNEbase_block _
    | JCNEinstanceof _ | JCNEassign _ | JCNEapp _ | JCNEunary _
    | JCNEconst _ | JCNEcontract _ | JCNEsubtype _ ->
        typing_error ~loc:e#pos "invalid memory location"
  in
  let locs =
    new location_set
      ~pos: e#pos
      ~typ:ty
      ~region:r
      ?label: e#label
      locs_node
  in
  ty, r, locs

let rec location env e =
  let deref_location_set_exn ls f =
    let t, tr, tls = location_set env ls in
    let fi = find_field e#pos t f false in
    let fr = Region.make_field tr fi in
    fi.fi_type, fr, JCLderef (tls, get_label e, fi, fr)
  in
  let deref_term_exn t f =
    let t1 = term env t in
    let fi = find_field e#pos t1#typ f false in
    let fr = Region.make_field t1#region fi in
    fi.fi_type, fr, JCLderef_term (t1, fi)
  in
  let rec has_range ls =
    match ls#node with
    | JCNErange _ -> true
    | JCNEbinary (ls, `Badd, off) -> has_range off || has_range ls
    | JCNEderef (ls, _) -> has_range ls
    | _ -> false
  in
  let ty, r, loc_node =
    match e#node with
    | JCNElabel (_l, _e) ->
      assert false (* TODO *)
    | JCNEvar id ->
      let vi =
        try List.assoc id env
        with
        | Not_found ->
          try Hashtbl.find variables_env id
          with
          | Not_found ->
            typing_error ~loc:e#pos "unbound identifier %s" id
      in
      vi.vi_type, vi.vi_region, JCLvar vi
    | JCNEderef (ls, f)
      when has_range ls ->
      begin try
        deref_location_set_exn ls f
      with Typing_error _ ->
        deref_term_exn ls f
      end
    | JCNEderef (t, f) ->
      begin try
        deref_term_exn t f
      with Typing_error _ ->
        deref_location_set_exn t f
      end
    | JCNEat (e, lab) ->
      let t, tr, tl = location env e in
      t, tr, JCLat(tl, lab)
    | JCNEcast _ ->
      let t = term env e in
      begin match t#typ with
      | JCTpointer _ ->
        t#typ, t#region, JCLsingleton t
      | _ -> typing_error ~loc:e#pos "non-pointer singleton term used as location"
      end
    | JCNErange _ | JCNEeqtype _ | JCNEmutable _ | JCNEold _
    | JCNEquantifier _ | JCNEmatch _ | JCNEunpack _ | JCNEpack _ | JCNEthrow _
    | JCNEtry _ | JCNEreturn _ | JCNEloop _ | JCNEblock _ | JCNEassert _
    | JCNElet _ | JCNEfree _ | JCNEalloc _ | JCNEoffset _ | JCNEreinterpret _ | JCNEaddress _
    | JCNEif _ | JCNEcast_mod _ | JCNEbase_block _
    | JCNEinstanceof _ | JCNEassign _ | JCNEapp _ | JCNEunary _ | JCNEbinary _
    | JCNEconst _ | JCNEcontract _ | JCNEsubtype _ | JCNEfresh _ ->
      typing_error ~loc:e#pos "invalid memory location"
  in
  let loc =
    new location
      ~pos: e#pos
      ~typ:ty
      ~region:r
      ?label: e#label
      loc_node
  in
  ty, r, loc

let behavior env vi_result (loc, id, throws, assumes, _requires, assigns, allocates, ensures) =
  let throws, env_result =
    match throws with
    | None -> None, (vi_result.vi_name, vi_result) :: env
    | Some id ->
      try
        let ei =
          StringHashtblIter.find exceptions_table id#name
        in
        let tei =
          match ei.exi_type with
          | Some tei -> tei
          | None ->
            typing_error
              ~loc:id#pos
              "exception without value"
        in
        let vi = var tei "\\result" in
        vi.vi_final_name <- "result";
        Some ei, (vi.vi_name,vi)::env
      with
      | Not_found ->
        typing_error
          ~loc:id#pos
          "undeclared exception %s" id#name
  in
  let assumes = Option.map (assertion env) assumes in
  let assigns =
    Option.map
      (fun (loc, l) ->
         (loc, List.map
            (fun a -> let _,_,tl = location env_result a in
              (match tl#node with
               | JCLvar vi -> vi.vi_assigned <- true
               | _ -> ());
              tl)
            l))
      assigns
  in
  let allocates =
    Option.map
      (fun (loc, l) ->
         (loc, List.map
            (fun a -> let _,_,tl = location env_result a in
              (match tl#node with
               | JCLvar vi -> vi.vi_assigned <- true
               | _ -> ());
              tl)
            l))
      allocates
  in
  let b = {
    b_throws = throws;
    b_assumes = assumes;
    b_assigns = assigns;
    b_allocates = allocates;
    b_ensures = assertion env_result ensures;
    b_free_ensures = Assertion.mktrue () }
  in
  (loc, id, b)


let loopbehavior env (names, inv, ass) =
  (names,
   Option.map (assertion env) inv,
   Option.map
     (fun (_p,locs) ->
        List.map
          (fun l ->
             let _, _, tl = location env l in tl)
          locs)
     ass)

let make_unary_op ~loc ~(op : Ast.unary_op) e2 =
  let t2 = e2#typ in
  let result () =
    let t = lub_numeric_types ~loc t2 t2 in
    t, dummy_region, JCEunary (unary_op (operator_of_type t) op, e2)
  in
  match op with
  | `Unot when t2 = JCTnative Tboolean ->
    t2, dummy_region, JCEunary (unary_op (operator_of_type t2) op, e2)
  | `Unot ->
    typing_error ~loc "boolean expected"
  | `Uminus when is_numeric t2 || is_gen_float t2 -> result ()
  | `Uminus -> typing_error ~loc "numeric type expected"
  | `Ubw_not | `Uminus_mod when is_enum t2 -> result ()
  | `Ubw_not | `Uminus_mod -> typing_error ~loc:loc "enum type expected"

let expand t1 t2 e =
  let tn1, e =
    match t1 with
    | JCTenum _ri -> Tinteger, expr_with_node ~typ:(JCTnative Tinteger) e @@ JCErange_cast (e, None)
    | JCTnative t -> t, e
    | _ -> assert false
  in
  match tn1, t2 with
  | Tinteger, JCTnative Treal ->
    begin match e#node with
    | JCEconst (JCCinteger n) ->
      new expr
        ~typ:real_type
        ~region:e#region
        ~pos:e#pos
        (JCEconst (JCCreal (n ^ ".0")))
    | _ ->
      new expr
        ~typ: real_type
        ~pos: e#pos
        (JCEapp
           {
             call_fun = JClogic_fun real_of_integer;
             call_args = [e];
             call_region_assoc = [];
             call_label_assoc = [];
           })
    end
  | _ -> e

let implicit_coerce ?(expand_int=true) t1 t2 e =
  let result () = expand t1 t2 e in
  let fail () =
    typing_error
      ~loc:e#pos
      "Invalid implicit coercion from type `%a' to type `%a'"
      print_type t1 print_type t2
  in
  match t1, t2 with
  | JCTnative t1, JCTnative t2 ->
    begin match t1, t2 with
    | Tinteger, Treal -> result ()
    | _ when t1 = t2 -> e
    | _ -> fail ()
    end
  | JCTenum e1, JCTenum e2 when e1 == e2 -> e
  | JCTenum _, JCTenum _ -> fail ()
  | JCTenum _, JCTnative Tinteger when expand_int -> result ()
  | JCTnative Tinteger, JCTenum _ -> fail ()
  | JCTlogic s1, JCTlogic s2 when s1 = s2 -> e
  | JCTlogic _, JCTlogic _ -> fail ()
  | JCTpointer (JCtag (s1, []), _, _), JCTpointer (pc, _, _) when substruct s1 pc -> e
  | JCTpointer (JCtag _, _, _), JCTpointer _ -> fail ()
  | JCTpointer (JCroot v1, _, _), JCTpointer (JCroot v2, _, _) when v1 == v2-> e
  | JCTpointer (JCroot _, _, _), JCTpointer (JCroot _, _, _) -> fail ()
  | JCTnull, (JCTnull | JCTpointer _) -> e
  | _ -> fail ()

let make_bin_op loc (op: operational_op) e1 e2 =
  let t1 = e1#typ and t2 = e2#typ in
  let return ~t ~region e =
    t, region, e
  in
  let return_numeric ?t () =
    let t' = lub_numeric_types ~loc t1 t2 in
    let implicit_coerce = implicit_coerce ~expand_int:false in
    return
      ~t:(t |? t')
      ~region:dummy_region
      (JCEbinary (implicit_coerce t1 t' e1,
                  bin_op (operator_of_type t') op,
                  implicit_coerce t2 t' e2))
  in
  let return_boolean = return_numeric ~t:boolean_type in
  let return_numeric = return_numeric ?t:None in
  match op with
  | `Bgt | `Blt | `Bge | `Ble
    when is_numeric t1 && is_numeric t2
         || is_gen_float t1 && is_gen_float t2 ->
    return_boolean ()
  | `Bgt | `Blt | `Bge | `Ble ->
    typing_error ~loc "numeric types expected for <, >, <= and >="
  | `Beq | `Bneq
    when is_numeric t1 && is_numeric t2
         || is_gen_float t1 && is_gen_float t2 ->
    return_boolean ()
  | `Beq | `Bneq when t1 = boolean_type && t2 = boolean_type ->
    return ~t:boolean_type ~region:dummy_region (JCEbinary (e1, bin_op `Boolean op, e2))
  | `Beq | `Bneq when is_pointer_type t1 && is_pointer_type t2 && comparable_types t1 t2 ->
    return ~t:boolean_type ~region:dummy_region (JCEbinary(e1, bin_op `Pointer op, e2))
  | `Beq | `Bneq ->
    typing_error
      ~loc
      "numeric, boolean or pointer types expected for == and !="
  | `Badd when is_pointer_type t1 && is_integer t2 ->
    return ~t:t1 ~region:e1#region (JCEshift (e1, expand t2 (JCTnative Tinteger) e2))
  | `Badd when is_numeric t1 && is_numeric t2 || is_gen_float t1 && is_gen_float t2 ->
    return_numeric ()
  | `Badd ->
    typing_error ~loc "unexpected types for +"
  | `Badd_mod when is_enum t1 && same_type_no_coercion t1 t2 ->
    return_numeric ()
  | `Badd_mod ->
    typing_error ~loc "enum type expected for +%%"
  | `Bsub when is_pointer_type t1 && is_integer t2 ->
    let e2 =
      new expr_with
        e2
        ~node:(Tuple.T3.trd @@ make_unary_op loc `Uminus (implicit_coerce t2 (JCTnative Tinteger) e2))
    in
    return ~t:t1 ~region:e1#region @@ JCEshift (e1, e2)
  | `Bsub when is_pointer_type t1 && is_pointer_type t2 && comparable_types t1 t2 ->
    return ~t:integer_type ~region:dummy_region (JCEbinary (e1, bin_op `Pointer `Bsub, e2))
  | `Bsub when is_numeric t1 && is_numeric t2 || is_gen_float t1 && is_gen_float t2 ->
    return_numeric ()
  | `Bsub -> typing_error ~loc "unexpected types for -"
  | `Bsub_mod when is_enum t1 && same_type_no_coercion t1 t2 ->
    return_numeric ()
  | `Bsub_mod ->
    typing_error ~loc "enum type expected for -%%"
  | `Bmul | `Bdiv | `Bmod when is_numeric t1 && is_numeric t2 || is_gen_float t1 && is_gen_float t2->
    return_numeric ()
  | `Bmul | `Bdiv | `Bmod ->
    typing_error ~loc "numeric types expected for multiplicative operators"
  | `Bmul_mod | `Bdiv_mod | `Bmod_mod when is_enum t1 && same_type_no_coercion t1 t2 ->
    return_numeric ()
  | `Bmul_mod | `Bdiv_mod | `Bmod_mod ->
    typing_error ~loc "enum type expected for *%% or /%%"
  | `Bbw_and | `Bbw_or | `Bbw_xor when is_boolean t1 && is_boolean t2 ->
    return
      ~t:boolean_type
      ~region:dummy_region
      (JCEbinary (e1, bin_op (operator_of_native Tboolean) op, e2))
  | `Bbw_and | `Bbw_or | `Bbw_xor
  | `Blogical_shift_right | `Barith_shift_right | `Bshift_left | `Bshift_left_mod
    when is_bit t1 && is_bit t2 ->
    return_numeric ()
  | `Bbw_and | `Bbw_or | `Bbw_xor
  | `Blogical_shift_right | `Barith_shift_right | `Bshift_left | `Bshift_left_mod ->
    typing_error ~loc:loc "pre-defined integral types expected for bitwise operators"
  | `Bland | `Blor as op when t1 = JCTnative Tboolean && t2 = JCTnative Tboolean ->
    return
      ~t:(JCTnative Tboolean)
      ~region:dummy_region
      (JCEbinary (e1, bin_op (operator_of_native Tboolean) op, e2))
  | `Bland | `Blor ->
    typing_error ~loc:loc "booleans expected"
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
  let ty, region, typed_e =
    match e#node with
    (* old expressions *)
    | JCNEconst c ->
      let t, tr, tc = const c in
      t, tr, JCEconst tc
    | JCNElabel (l, e1) ->
      let te1 = fe e1 in
      lab := l;
      te1#typ, te1#region, te1#node
    | JCNEvar id ->
      begin try
        let vi =
          try List.assoc id env
          with
          | Not_found -> Hashtbl.find variables_env id
        in
        vi.vi_type, vi.vi_region, JCEvar vi
      with
      | Not_found ->
        let pi =
          try
            Hashtbl.find logic_functions_env id
          with
          | Not_found ->
            typing_error ~loc:e#pos "unbound identifier %s" id
        in
        let app =
          {
            call_fun = JClogic_fun pi;
            call_args = [];
            call_region_assoc = [];
            call_label_assoc = [];
          }
        in
        let ty =
          match pi.li_result_type with
          | Some r -> r
          | None -> assert false (* check it is a function *)
        in
        ty, Region.make_var ty pi.li_name, JCEapp app
      end

    | JCNEderef (e1, f) ->
      let te1 = fe e1 in
      let fi = find_field e#pos te1#typ f false in
      fi.fi_type, Region.make_field te1#region fi, JCEderef (te1, fi)
    | JCNEbinary (e1, (#logical_op as op), e2) ->
      let te1 = fe e1 and te2 = fe e2 in
      begin match op with
      | `Bland ->
        make_bin_op e#pos `Bland te1 te2
      | `Blor ->
        make_bin_op e#pos `Blor te1 te2
      | `Bimplies | `Biff ->
        typing_error ~loc:e#pos "unexpected operator in expression"
      end
    | JCNEbinary (e1, (#operational_op as op), e2) ->
      make_bin_op e#pos op (fe e1) (fe e2)
    | JCNEunary(op, e1) ->
      make_unary_op e#pos op (fe e1)
    | JCNEapp (id, labs, args) ->
      begin try
        let fi = find_fun_info id in
        assert (labs = []);
        let tl = try
            List.map2
              (fun (_valid,vi) e ->
                 let ty = vi.vi_type in
                 let te = fe e in
                 if subtype te#typ ty then te
                 else
                   typing_error
                     ~loc:e#pos
                     "type %a expected instead of %a"
                     print_type ty print_type te#typ)
              fi.fun_parameters args
          with
          | Invalid_argument _ ->
            typing_error ~loc:e#pos "wrong number of arguments for %s" id
        in
        let ty = fi.fun_result.vi_type in
        ty,
        Region.make_var ty fi.fun_name,
        JCEapp {
          call_fun = JCfun fi;
          call_args = tl;
          call_region_assoc = [];
          call_label_assoc = [];
        }
      with
      | Not_found ->
        try begin
          let pi = find_logic_info id in
          let tl =
            try
              List.map2
                (fun vi e ->
                   let ty = vi.vi_type in
                   let te = fe e in
                   if subtype ~strict:true te#typ ty
                   then te
                   else
                     typing_error
                       ~loc:e#pos
                       "type %a expected instead of %a"
                       print_type ty print_type te#typ)
                pi.li_parameters args
            with
            | Invalid_argument _ ->
              typing_error
                ~loc:e#pos
                "wrong number of arguments for %s"
                id
          in
          let ty =
            match pi.li_result_type with
            | None -> JCTnative Tboolean
            | Some ty -> ty
          in
          let label_assoc =
            match e#label, pi.li_labels, labs with
            | Some l, [lf], [] -> [lf,l]
            | _ ->
              try
                List.map2
                  (fun l1 l2 -> (l1,l2))
                  pi.li_labels labs
              with
              | Invalid_argument _ ->
                typing_error
                  ~loc:e#pos
                  "wrong number of labels for %s"
                  id
          in
          let app = {
            call_fun = JClogic_fun pi;
            call_args = tl;
            call_region_assoc = [];
            call_label_assoc = label_assoc;
          } in
          ty, Region.make_var ty pi.li_name, JCEapp app
        end
        with
        | Not_found ->
          typing_error ~loc:e#pos "unbound function or logic function identifier %s" id
      end
    | JCNEassign (e1, e2) ->
      let te1 = fe e1 and te2 = fe e2 in
      let t1 = te1#typ and t2 = te2#typ in
      let te2 =
        if subtype t2 t1 then
          match t2 with
          | JCTnull -> new expr_with ~typ:t1 te2
          | _ -> te2
        else
          (* particular case for floats: implicit cast *)
          begin
            match (t1, t2) with
            | JCTnative (Tgenfloat f1), JCTnative (Tgenfloat f2) ->
              begin match (f2,f1) with
              | `Binary80,`Binary80 -> te2
              | `Double,`Double -> te2
              | `Float,`Float -> te2
              | _ ->
                new expr ~typ:t1 ~pos:te2#pos
                  (JCEreal_cast(te2, Round(f1,Round_nearest_even)))
              end
            | _ ->
              typing_error
                ~loc:e2#pos
                "type '%a' expected in assignment instead of '%a'"
                print_type t1 print_type t2
          end
      in
      begin match te1#node with
      | JCEvar v ->
        v.vi_assigned <- true;
        unit_type, dummy_region, JCEassign_var(v, te2)
      | JCEderef(e, f) ->
        unit_type, dummy_region, JCEassign_heap(e, f, te2)
      | _ -> typing_error ~loc:e1#pos "not an lvalue"
      end
    | JCNEinstanceof (e1, t) ->
      let te1 = fe e1 in
      let st = find_struct_info e#pos t in
      boolean_type, dummy_region, JCEinstanceof (te1, st)
    | JCNEreinterpret (e1, t) ->
      unit_type,
      dummy_region,
      JCEreinterpret (fe e1, find_struct_info e#pos t)
    | JCNEcast (e1, t) ->
      let te1 = fe e1 in
      let ty = type_type t in
      begin match ty with
      | JCTnative Tinteger ->
        if is_integer te1#typ then
          integer_type, te1#region, JCErange_cast (te1, None)
        else
          typing_error ~loc:e#pos "bad cast to integer"
      | JCTnative Treal ->
        if is_integer te1#typ then
          real_type, te1#region, JCEreal_cast (te1, Integer_to_real)
        else if is_real te1#typ then
          real_type, te1#region, te1#node
        else if is_double te1#typ then
          real_type, te1#region, JCEreal_cast (te1, Double_to_real)
        else if is_float te1#typ then
          real_type, te1#region, JCEreal_cast (te1, Float_to_real)
        else
          typing_error ~loc:e#pos "bad cast to real"
      | JCTnative (Tgenfloat f) ->
        if is_real te1#typ || is_integer te1#typ then
          JCTnative (Tgenfloat f), te1#region, JCEreal_cast (te1, Round (f, Round_nearest_even))
        else begin match te1#typ with
          | JCTnative (Tgenfloat f1) ->
            let e =
              match f1, f with
              | `Binary80, `Binary80 -> te1#node
              | `Double,`Double -> te1#node
              | `Float,`Float -> te1#node
              | _ ->
                JCEreal_cast (te1, Round (f, Round_nearest_even))
            in
            JCTnative (Tgenfloat f), te1#region, e
          | _ -> typing_error ~loc:e#pos "bad cast to floating-point number"
        end
      | JCTnative _ -> assert false (* TODO *)
      | JCTenum ri ->
        if is_integer te1#typ || is_enum te1#typ then
          JCTenum ri, dummy_region, JCErange_cast (te1, Some ri)
        else
          typing_error ~loc:e#pos "integer type expected"
      | JCTpointer (JCtag (st, _) as st_pc, _, _) ->
        begin match te1#typ with
        | JCTpointer (st1, a, b) ->
          if superstruct st st1 then
            ty, te1#region, te1#node
          else if substruct st st1 then
            JCTpointer (JCtag (st, []), a, b), te1#region, JCEdowncast (te1, st)
          else
            begin match st1 with
            | JCroot ri | JCtag ({ si_root = Some ri; _ }, [])
              when ri == struct_root st && List.length ri.ri_hroots > 1 ->
              (* union downcast -- now supported siilar to usual one ==> TODO: support unions *)
              JCTpointer (JCtag (st, []), a, b), te1#region, JCEdowncast (te1, st)
            | JCtag (st', []) when same_hierarchy st_pc st1 ->
              let deep_substruct = deep_substruct_nconstrs in
              let r, _ = deep_substruct st' st in
              if r then ty, te1#region, te1#node (* implcit cast to deep superstruct *)
              else
                let r, conds = deep_substruct st st' in
                if r then (* deep downcast *)
                  let typ = JCTpointer (JCtag (st, []), a, b) in
                  typ, te1#region,
                  JCEblock [
                    new expr ~typ:unit_type @@
                    JCEassert ([new identifier "safety"], Acheck,
                               new assertion_with ~mark:"type_tags" @@ assertion env @@ conds e1);
                    new expr ~typ ~region:te1#region te1#node]
                else (* sidecast *)
                  JCTpointer (JCtag (st, []), None, None), te1#region, JCEsidecast (te1, st)
            | _ -> typing_error ~loc:e#pos "invalid cast: structures from different hierarchies"
            end
        | _ -> typing_error ~loc:e#pos "invalid cast"
        end
      | _ -> typing_error ~loc:e#pos "invalid cast"
      end
    | JCNEcast_mod (e1, t) ->
      let te1 = fe e1 in
      let ty = type_type t in
      begin match ty with
      | JCTenum ri when is_integer te1#typ || is_enum te1#typ ->
        JCTenum ri, dummy_region, JCErange_cast_mod (te1, ri)
      | _ -> typing_error ~loc:e#pos "invalid modulo cast"
      end
    | JCNEif (e1, e2, e3) ->
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
      | _ -> typing_error ~loc:e1#pos "boolean expression expected"
      end
    | JCNEoffset (k, e1) ->
      let te1 = fe e1 in
      begin match te1#typ with
      | JCTpointer(JCtag(st, _), _, _) ->
        integer_type, dummy_region, JCEoffset(k, te1, st)
      | JCTpointer(JCroot _, _, _) ->
        assert false (* TODO *)
      | _ -> typing_error ~loc:e#pos "pointer expected"
      end
    | JCNEaddress (Addr_absolute, e1) ->
      let te1 = fe e1 in
      if is_integer  te1#typ then
        JCTnull, dummy_region, JCEaddress(Addr_absolute,te1)
      else
        typing_error ~loc:e#pos "integer expected"
    | JCNEaddress (Addr_pointer, e1) ->
      let te1 = fe e1 in
      begin match te1#typ with
      | JCTpointer(JCtag(_st, _), _, _) ->
        integer_type, dummy_region, JCEaddress(Addr_pointer,te1)
      | JCTpointer(JCroot _, _, _) ->
        assert false (* TODO *)
      | _ -> typing_error ~loc:e#pos "pointer expected"
      end
    | JCNEbase_block(e1) ->
      let te1 = fe e1 in
      if is_pointer_type te1#typ then
        JCTnull, dummy_region, JCEbase_block(te1)
      else
        typing_error ~loc:e#pos "pointer expected"
    | JCNEalloc(e1, t) ->
      let st = find_struct_info e#pos t in
      let ty = JCTpointer(JCtag(st, []), Some zero, None) in
      let te1 = fe e1 in
      let te1 = implicit_coerce te1#typ (JCTnative Tinteger) te1 in
      ty, Region.make_var ty "alloc", JCEalloc (te1, st)
    | JCNEfree e1 ->
      unit_type, dummy_region, JCEfree (fe e1)
    | JCNElet(tyo, id, e1o, e2) ->
      let ty, te1o =
        match tyo, e1o with
        | None, None ->
          typing_error ~loc:e#pos "let with no initial value must have a type"
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
            typing_error
              ~loc:e#pos
              "inferred type is not a subtype of declared type"
      in
      let vi = var ~bound:true ty id in
      let te2 = expr ((id, vi)::env) e2 in
      te2#typ,
      te2#region,
      JCElet (vi, Option.map (fun e -> implicit_coerce e#typ ty e) te1o, te2)
    (* old statements *)
    | JCNEassert(behav,asrt,e1) ->
      unit_type, dummy_region, JCEassert(behav,asrt,assertion env e1)
    | JCNEcontract(req,dec,behs,e) ->
      let requires = Option.map (assertion env) req in
      let decreases =
        Option.map
          (fun (t, rel) ->
             let t = term env t in
             let t = term_implicit_coerce t#typ integer_type t in
             t, rel)
          dec
      in
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
    | JCNEloop (behs, vo, body) ->
      let behaviors = List.map (loopbehavior env) behs in
      let variant =
        Option.map
          (fun (v,r) ->
             let r = Option.map
                 (fun id -> find_logic_info id#name) r
             in
             let v = ft v in
             (Option.map_default r ~default:(term_expand v#typ (JCTnative Tinteger) v) ~f:(Fn.const v), r))
          vo
      in
      (unit_type,
       dummy_region,
       JCEloop (
         loop_annot ~behaviors
           ~free_invariant:(Assertion.mktrue ())
           ~variant,
         fe body))
    | JCNEreturn None ->
      unit_type, dummy_region, JCEreturn_void
    | JCNEreturn(Some e1) ->
      let te1 = fe e1 in
      let vi = List.assoc "\\result" env in
      if subtype te1#typ vi.vi_type then
        (unit_type,
         te1#region,
         JCEreturn(vi.vi_type, te1))
      else
        typing_error ~loc:e#pos "type `%a' expected in return instead of `%a'"
          print_type vi.vi_type print_type te1#typ
    | JCNEtry (body, catches, finally) ->
      let tbody = unit_expr (fe body) in
      let tfinally = unit_expr (fe finally) in
      let tcatches = List.map begin function (id, v, cbody) ->
        if id#name = Norm.return_label#name then set_return_label ();
        let ei = try
            StringHashtblIter.find exceptions_table id#name
          with Not_found ->
            typing_error ~loc:id#pos "undeclared exception: %s" id#name
        in
        match ei.exi_type with
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
          StringHashtblIter.find exceptions_table id#name
        with Not_found ->
          typing_error ~loc:id#pos "undeclared exception %s" id#name
      in
      let region, te1o = match e1o with
        | None -> dummy_region, None
        | Some e1 ->
          let te1 = fe e1 in
          let tei = match ei.exi_type with
            | Some tei -> tei
            | None -> typing_error ~loc:e#pos "this exception has no argument"
          in
          if subtype te1#typ tei then
            te1#region, Some te1
          else
            typing_error ~loc:e#pos "type `%a' expected instead of `%a'"
              print_type tei print_type te1#typ
      in
      Common.any_type, region, JCEthrow(ei, te1o)
    | JCNEpack(e1, t) ->
      let te1 = fe e1 in
      begin match te1#typ with
      | JCTpointer(JCtag(st, _), _, _) ->
        let as_t = match t with
          | Some t -> find_struct_info t#pos t#name
          | None -> st
        in
        unit_type, te1#region, JCEpack(st, te1, as_t)
      | _ -> typing_error ~loc:e#pos "only structures can be packed"
      end
    | JCNEunpack (e1, t) ->
      let te1 = fe e1 in
      begin match te1#typ with
      | JCTpointer (JCtag(st, []), _, _) ->
        let from_t =
          match t with
          | Some t -> find_struct_info t#pos t#name
          | None ->
            let rec res =
              {
                si_params = [];
                si_name = "bottom";
                si_parent = None;
                si_final = false;
                si_hroot = res;
                si_fields = [];
                si_root = None;
              }
            in
            res
        in
        unit_type, te1#region, JCEunpack (st, te1, from_t)
      | _ -> typing_error ~loc:e#pos "only structures can be unpacked"
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
    | JCNEeqtype _ | JCNErange _ | JCNEsubtype _ | JCNEfresh _ ->
      typing_error ~loc:e#pos "construction not allowed in expressions"
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
  | JCCrequires e | JCCdecreases(e,_) ->
      type_labels [LabelHere] ~result_label:None (Some LabelHere) e
  | JCCbehavior(_, _, _, assumes, requires, assigns, allocates, ensures) ->
      Option.iter
        (type_labels [LabelHere] ~result_label:None (Some LabelHere)) assumes;
      Option.iter
        (type_labels [LabelHere] ~result_label:None (Some LabelHere)) requires;
      Option.iter
        (fun (_, x) ->
           List.iter
             (type_labels [LabelOld; LabelPre; LabelPost; LabelHere]
                ~result_label:(Some LabelPost) (Some LabelOld)) x)
        assigns;
      Option.iter
        (fun (_, x) ->
           List.iter
             (type_labels [LabelOld; LabelPre; LabelPost; LabelHere]
(* warning: allocates L: L evaluated in the post-state *)
                ~result_label:(Some LabelHere) (Some LabelHere)) x)
        allocates;
      type_labels [LabelOld; LabelPre; LabelHere]
        ~result_label:(Some LabelHere) (Some LabelHere) ensures

(** Apply [type_labels] in all expressions of a normalized declaration,
with the correct label environment. *)
let rec type_labels_in_decl d = match d#node with
  | JCDvar(_, _, init) ->
      Option.iter (type_labels [] ~result_label:None None) init
  | JCDfun(_, _, _, clauses, body) ->
      Option.iter
        (type_labels [LabelHere; LabelPre] ~result_label:None (Some LabelHere))
        body;
      List.iter type_labels_in_clause clauses
  | JCDtag(_, _, _, _, invs) ->
      List.iter
        (fun (_, _, e) ->
           type_labels [LabelHere] ~result_label:None (Some LabelHere) e) invs
  | JCDlemma(_, _, _, labels, body) ->
    type_labels labels ~result_label:None (default_label labels) body
  | JCDlogic(_, _, _, _labels, _, JCnone) -> ()
  | JCDlogic(_, _, _, labels, _, JCreads el) ->
    List.iter
      (type_labels labels
         ~result_label:(Some LabelPost) (default_label labels)) el
  | JCDlogic(_, _, _, labels, _, JCexpr e) ->
    type_labels labels  ~result_label:None (default_label labels) e
  | JCDlogic(_, _, _, _labels, _, JCinductive l) ->
    List.iter (fun (_,labels,e) ->
      type_labels labels
        ~result_label:None (default_label labels) e) l
  | JCDglobal_inv(_, body) ->
    type_labels [LabelHere] ~result_label:None (Some LabelHere) body
  | JCDvariant_type _ | JCDunion_type _ | JCDenum_type _ | JCDlogic_type _
  | JCDexception _ | JCDlogic_var _ ->  ()
  | JCDaxiomatic (_id, l) -> List.iter type_labels_in_decl l

(* <====== A partir d'ici, c'est pas encore fait *)

let clause env vi_result c acc =
  match c with
  | JCCrequires e ->
    { acc with
      fs_requires =
        make_and (assertion env e) acc.fs_requires; }
  | JCCdecreases (e, r) ->
    assert (acc.fs_decreases = None);
    let pi = Option.map
        (fun id ->
           let pi =
               try Hashtbl.find logic_functions_env id#name
               with Not_found ->
                 typing_error ~loc:e#pos "unbound ordering relation %s" id#name
           in pi)
        r
    in
    let t = term env e in
    let t = term_implicit_coerce t#typ integer_type t in
    { acc with fs_decreases = Some (t, pi) }
  | JCCbehavior b ->
    let (loc,id,b) = behavior env vi_result b in
    if id = "default" then
      { acc with fs_default_behavior = loc,id,b }
    else
      { acc with fs_behavior = (loc, id, b) :: acc.fs_behavior }

let param (t, id) =
  let ty = type_type t in
  let vi = var ~formal:true ty id in
  (id, vi)

let fun_param (v, t, id) =
  let ty = type_type t in
  let vi = var ~formal:true ty id in
  (v, id, vi)

let assertion_true = new assertion JCAtrue

let field st root bitoffset ((rep, abs), t, id, bitsize) =
  let ty = type_type t in
  incr field_tag_counter;
  let name = st.si_name ^ "_" ^ id in
  let fi =
    {
      fi_tag = !field_tag_counter;
      fi_name = id ;
      fi_final_name = Envset.get_unique_name name;
      fi_type = ty;
      fi_hroot = root;
      fi_struct = st;
      fi_rep = rep || (not (is_pointer_type ty));
      fi_abstract = abs;
      fi_bitsize = bitsize;
      fi_bitoffset = bitoffset
    }
  in
  fi

let lemmas_table = StringHashtblIter.create 17
let global_invariants_table = IntHashtblIter.create 17

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
      (fun (_valid,v) -> (v.vi_name, v))
      fi.fun_parameters
  in
  param_env, fi

let add_fundecl (ty,_loc,id,pl) =
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
    fi.fun_parameters <- List.map (fun (v,_,x) -> (v,x)) params;
    Hashtbl.replace functions_env id fi;
    param_env, fi

let add_logic_fundecl (ty,id,poly_args,labels,pl) =
  try
    let pi = Hashtbl.find logic_functions_env id in
    let ty = pi.li_result_type in
    let param_env =
      List.map (fun v -> v.vi_name, v) pi.li_parameters
    in
    param_env, ty, pi
  with Not_found ->
    let poly_args = add_poly_args poly_args in
    let param_env = List.map param pl in
    let ty = Option.map type_type ty in
    let pi = match ty with
      | None -> make_pred id
      | Some ty -> make_logic_fun id ty
    in
    pi.li_parameters <- List.map snd param_env;
    pi.li_poly_args <- poly_args;
    pi.li_labels <- labels;
    Hashtbl.replace logic_functions_env id pi;
    param_env, ty, pi


let type_range_of_term ty t =
  match ty with
    | JCTenum ri ->
        let mint =
          new term ~pos:t#pos ~typ:integer_type
            (JCTconst(JCCinteger (Num.string_of_num ri.ei_min)))
        in
        let mina = new assertion (JCArelation(mint,(`Ble,`Integer),t)) in
        let maxt =
          new term ~pos:t#pos ~typ:integer_type
            (JCTconst(JCCinteger (Num.string_of_num ri.ei_max)))
        in
        let maxa = new assertion (JCArelation(t,(`Ble,`Integer),maxt)) in
        new assertion (JCAand [ mina; maxa ])
    | JCTpointer (JCtag(st, _), _n1opt, n2opt) ->
      let maxcstr =
        match n2opt with
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
    | JCTpointer (JCroot _vi, _, _) ->
      assert false (* TODO, but need to change JCToffset before *)
    | _ -> Assertion.mktrue ()

(** [check_positivity pi a] checks whether the assertion [a] as exactly one positive occurrence of pi in a *)

let rec signed_occurrences pi a =
  match a#node with
  | JCArelation _ | JCAbool_term _ | JCAtrue | JCAfalse -> (0,0)
  | JCAapp app -> ((if app.app_fun == pi then 1 else 0),0)
  | JCAquantifier (Forall, _vi, _, p) -> signed_occurrences pi p
  | JCAquantifier (Exists, _vi, _, _p) -> assert false (* TODO *)
  | JCAimplies (p1, p2) ->
      let (pos1,neg1) = signed_occurrences pi p1 in
      let (pos2,neg2) = signed_occurrences pi p2 in
      (neg1+pos2,pos1+neg2)
  | JCAand l | JCAor l ->
      List.fold_left
        (fun (p,n) a ->
           let (pos1,neg1) = signed_occurrences pi a in
           (p+pos1,n+neg1)) (0,0) l
  | JCAat (p, _) | JCAold p -> signed_occurrences pi p
  | JCAnot p ->
      let (pos,neg) = signed_occurrences pi p in
      (neg,pos)
  | JCAiff (_, _) -> assert false (* TODO *)
  | JCAsubtype (_, _, _) -> assert false (* TODO *)
  | JCAeqtype (_, _, _) -> assert false (* TODO *)
  | JCAmutable (_, _, _) -> assert false (* TODO *)
  | JCAif (_, _, _) -> assert false (* TODO *)
  | JCAinstanceof (_, _, _) -> assert false (* TODO *)
  | JCAlet (_, _,_) -> assert false (* TODO *)
  | JCAmatch (_, _) -> assert false (* TODO *)
  | JCAfresh _ -> assert false (* TODO *)

let check_positivity loc pi a =
  let (pos,_neg) = signed_occurrences pi a in
  if pos = 0 then
    typing_error ~loc:loc "predicate has no positive occurrence in this case";
  if pos > 1 then
    typing_error ~loc:loc "predicate has too many positive occurrences in this case"

(** [check_consistency id data] attempt to detect trivial inconsistency cases in axiomatics

    pis = data.axiomatics_defined_ids is the set of logic ids defined in this axiomatic

    check 1:
      for each lemma: check that at least one pi of pis occurs

    check 2:
      for each lemma with labels l1,..,lk: for each li, there should be at least one occurrence
      of some pi of pis applied to label li.

*)

let rec term_occurrences table t =
  let term = term_occurrences table in
  match t#node with
  | JCTconst _
  | JCTvar _ -> ()
  | JCTrange_cast (t, _)
  | JCTrange_cast_mod (t, _)
  | JCTat (t, _)
  | JCTold t
  | JCTaddress (_, t)
  | JCTbase_block t
  | JCTunary (_, t)
  | JCToffset (_, t, _)
  | JCTderef (t, _, _)
  | JCTinstanceof (t, _, _)
  | JCTdowncast (t, _, _)
  | JCTsidecast (t, _, _)
  | JCTreal_cast (t, _) ->
    term t
  | JCTbinary (t1, _, t2)
  | JCTshift (t1, t2)
  | JCTlet (_, t1, t2) ->
    term t1;
    term t2
  | JCTapp app ->
    begin
      List.iter term app.app_args;
      try
        let li_tag = app.app_fun.li_tag in
        let labs = app.app_label_assoc in
        Hashtbl.(replace table li_tag @@ labs :: find table li_tag)
      with
      | Not_found -> ()
    end
  | JCTmatch (t, l) ->
    term t;
    List.iter (term % snd) l
  | JCTrange (to1, to2) ->
    Option.(
      iter term to1;
      iter term to2)
  | JCTif (t, t1, t2) ->
    term t;
    term t1;
    term t2

let rec occurrences table a =
  let assertion = occurrences table in
  let term = term_occurrences table in
  let tag t =
    match t#node with
    | JCTtag _ | JCTbottom -> ()
    | JCTtypeof (t, _) -> term_occurrences table t
  in
  match a#node with
  | JCAtrue | JCAfalse -> ()
  | JCAapp app ->
    begin
      List.iter term app.app_args;
      try
        let l = Hashtbl.find table app.app_fun.li_tag in
        Hashtbl.replace table app.app_fun.li_tag (app.app_label_assoc :: l)
      with Not_found -> ()
    end
  | JCAnot a
  | JCAquantifier (_, _, _, a)
  | JCAold a
  | JCAat (a, _) ->
    assertion a
  | JCAiff (a1, a2)
  | JCAimplies (a1, a2) ->
    assertion a1;
    assertion a2
  | JCAand l | JCAor l ->
    List.iter assertion l
  | JCArelation(t1, _op, t2) ->
    term t1;
    term t2
  | JCAsubtype (t1, t2, _)
  | JCAeqtype (t1, t2, _) ->
    tag t1;
    tag t2
  | JCAmutable (t, _, t') ->
    term t;
    tag t'
  | JCAif (t, a1, a2) ->
    term t;
    assertion a1;
    assertion a2
  | JCAinstanceof (t, _, _)
  | JCAbool_term t
  | JCAfresh t ->
    term t
  | JCAlet (_, t, a) ->
    term t;
    assertion a
  | JCAmatch (t, l) ->
    term t;
    List.iter (assertion % snd) l

let rec list_assoc_data lab l =
  match l with
    | [] -> false
    | (_,d):: r ->
        d=lab || list_assoc_data lab r

let check_consistency id data =
  let pis = data.axiomatics_defined_ids in
  List.iter
    (function
      | ADprop (_, axid, labels, `Axiom, a) ->
        let h = Hashtbl.create 17 in
        List.iter
          (fun pi -> Hashtbl.add h pi.li_tag [])
          pis;
        occurrences h a;
        Options.lprintf "@[<v 2>occurrences table for axiom %s in axiomatic %s:@\n" axid id;
        Hashtbl.iter
          (fun pi l ->
             Options.lprintf "%d: @[" pi;
             List.iter
               (fun label_assoc ->
                  Options.lprintf "%a ;"
                    Why_pp.(print_list comma (fun fmt (_l1,l2) -> Print_misc.label fmt l2)) label_assoc)
               l;
             Options.lprintf "@]@\n")
          h;
        Options.lprintf "@]@.";
        if Hashtbl.fold (fun _pi l acc -> acc && l=[]) h true then
          typing_warning
            "axiom %s should contain at least one occurrence of a symbol declared in axiomatic %s" axid id;
        List.iter
          (fun lab ->
             if not (Hashtbl.fold (fun _pi l acc -> acc || List.exists (list_assoc_data lab) l) h false) then
               typing_warning
                 "there should be at least one declared symbol depending on label %a in this axiom"
                 Print_misc.label lab)
          labels
      | ADprop (_, _, _, `Lemma, _) -> ())
    data.axiomatics_decls

let occurrences tags a =
  let h = Hashtbl.create 10 in
  List.iter (fun tag -> Hashtbl.add h tag []) tags;
  occurrences h a;
  List.map (Hashtbl.find h) tags

let update_axiomatic axiomatic pi =
  match axiomatic with
    | Some(id,data) ->
        pi.li_axiomatic <- Some id;
        data.axiomatics_defined_ids <- pi :: data.axiomatics_defined_ids
    | None -> ()

exception Identifier_Not_found of string

let create_pragma_gen_frame_sub frame_or_sub loc id logic =
  let info =
    try
      find_logic_info logic
    with
    | Not_found -> typing_error ~loc:loc "logic unknown %s" logic
  in
  let params1 = info.li_parameters in
  let params2 = List.map (fun v -> var ~unique:true v.vi_type 
    (v.vi_name^"_dest"))
    info.li_parameters in
  let pi = make_pred id in
  pi.li_parameters <- params1@params2;
  let label1 = LabelName {
    lab_name = "L1";
    lab_final_name = "L1";
    lab_times_used = 0;
  } in
  let label2 = LabelName {
    lab_name = "L2";
    lab_final_name = "L2";
    lab_times_used = 0;
  } in
  pi.li_labels <- [label1;label2];
  Hashtbl.replace logic_functions_env id pi;
  let def =
    let params param =
      List.map
        (fun x -> new term ~pos:loc ~typ:x.vi_type (JCTvar x))
        param in
    begin match info.li_result_type with
    | None ->
      let app label param = new assertion (JCAapp { app_fun = info;
                                                    app_args = params param;
                                                    app_region_assoc = [];
                                                    app_label_assoc = 
                                                      label_assoc loc "bug in the generation" 
                                                        (Some label) info.li_labels []
                                                  })
      in
      make_and (app label1 params1) (app label2 params2)
    | Some ty ->
      let term label param =
        new term ~pos:loc ~typ:ty
          (JCTapp { app_fun = info;
                    app_args = params param;
                    app_region_assoc = [];
                    app_label_assoc =
                      label_assoc loc "bug in the generation"
                        (Some label) info.li_labels []}) in
      new assertion
        (make_rel_bin_op loc `Beq
           (term label1 params1) (term label2 params2))
    end
  in
  let def = JCAssertion def in
  IntHashtblIter.add logic_functions_table pi.li_tag (pi, def);
  Hashtbl.add
    pragma_gen_frame
    pi.li_tag
    (pi, info, params1, params2, frame_or_sub)

let create_pragma_gen_sep_logic_aux loc kind id li =
  let translate_param (p,restr) =
    match p#node,restr with
    | JCPTnative _,_ ->
      typing_error ~loc:loc "A Separation pragma can't reference \"pure\" type"
    | JCPTidentifier (s,[]),_ -> (* Should be the identifier of a logic *)
      let info =
        try
          find_logic_info s
        with Not_found -> raise (Identifier_Not_found s)
      in `Logic (info,restr)
    | JCPTidentifier (_s,_l),_ ->
      typing_error ~loc:loc "A Separation pragma can't reference a logic type"
    | JCPTpointer (_,[],None,None),[] ->
      let ty = type_type p in
      `Pointer (newvar ty)
    | JCPTpointer _, _::_ ->
      typing_error ~loc:loc
        "In a separation pragma pointer can't\
         be at that time restreint to some field"
    | JCPTpointer _,_ ->
      failwith "TODO : sorry I'm lazy. But what have you done?" in
  let change_var_name = function
    |`Logic (info,restr) ->
      let params = info.li_parameters in
      let new_params = List.map copyvar params in
      `Logic (info,restr,new_params)
    |`Pointer _ as e -> e in
  let to_param = function
    | `Logic (_,_,new_params) -> new_params
    | `Pointer var -> [var]
  in
  let params = List.map translate_param li in
  let params = List.map change_var_name params in
  let param_env = List.concat (List.map to_param params) in
  let pi = make_pred id in
  pi.li_parameters <- param_env;
  let cur_label = LabelName {
    lab_name = "L";
    lab_final_name = "L";
    lab_times_used = 0;
  } in
  pi.li_labels <- [cur_label];
  Hashtbl.replace logic_functions_env id pi;
  (* create a dumb definition with the correct effect
     which will be replace by the correcte one at the end *)
  let to_def =
    function
    | `Logic (info,_,params) ->
      let param = List.map
          (fun x -> new term ~pos:loc ~typ:x.vi_type (JCTvar x))
          params in
      new assertion begin
        match info.li_result_type with
        | None ->
          JCAapp {app_fun = info;
                  app_args = param;
                  app_region_assoc = [];
                  app_label_assoc =
                    label_assoc loc "bug in the generation"
                      (Some cur_label) info.li_labels []
                 }
        | Some ty ->
          let term = new term ~pos:loc
            ~typ:ty
            (JCTapp {app_fun = info;
                     app_args = param;
                     app_region_assoc = [];
                     app_label_assoc = []}) in
          make_rel_bin_op loc `Beq term term
      end
    | `Pointer var ->
      let t = new term ~pos:loc ~typ:var.vi_type (JCTvar var) in
      new assertion (make_rel_bin_op loc `Beq t t) in
  let def = JCAssertion (make_and_list (List.map to_def params)) in
  IntHashtblIter.add logic_functions_table pi.li_tag (pi, def);
  Hashtbl.add pragma_gen_sep pi.li_tag
    (kind,params)


let create_pragma_gen_sep_logic loc kind id li =
  try
    create_pragma_gen_sep_logic_aux loc kind id li
  with Identifier_Not_found ident ->
    Hashtbl.add pragma_before_def ident (loc,kind,id,li)

let create_if_pragma_before ident =
  List.iter (fun (loc,kind,id,li) ->
               create_pragma_gen_sep_logic loc kind id li)
    (Hashtbl.find_all pragma_before_def ident);
    (Hashtbl.remove_all pragma_before_def ident)

let test_if_pragma_notdefined () =
  if not (Hashtbl.is_empty pragma_before_def) then
    Hashtbl.iter (fun ident (loc,_kind,id,_li) ->
    typing_error ~loc:loc "The pragma %s has not been defined because
%s appeared nowhere" id ident) pragma_before_def


(*let test_*)


let rec decl_aux ~only_types ~axiomatic acc d =
  reset_uenv ();
  let loc = d#pos in
  let in_axiomatic = axiomatic <> None in
  match d#node with
    | JCDvar (_ty, id, init) ->
        if not only_types then
          begin
            if in_axiomatic then
              typing_error ~loc:loc "not allowed inside axiomatic specification";
            let e = Option.map (expr []) init in
            let vi = get_vardecl id in
            IntHashtblIter.add variables_table vi.vi_tag (vi, e);
            acc
          end
        else
          acc
    | JCDfun (_ty, id, _pl, specs, body) ->
        if not only_types then
          begin
            if in_axiomatic then
              typing_error ~loc:loc "not allowed inside axiomatic specification";
            let loc = match Options.position_of_label id#name with
              | Some loc -> loc
              | None -> id#pos
            in
            let param_env, fi = get_fundecl id#name in
            let vi = fi.fun_result in
            let s = List.fold_right
              (clause param_env vi) specs
              { fs_requires = assertion_true;
                fs_free_requires = assertion_true;
                fs_decreases = None;
                fs_default_behavior =
                  Why_loc.dummy_position ,"default", default_behavior;
                fs_behavior = [] }
            in
            reset_return_label ();
            let b = Option.map
              (unit_expr % expr (("\\result",vi)::param_env)) body
            in
            fi.fun_has_return_label <- get_return_label ();
            IntHashtblIter.add functions_table fi.fun_tag (fi,loc,s,b);
            acc
          end
        else
          acc
    | JCDenum_type (id, min, max) ->
        if only_types then begin
        if in_axiomatic then
          typing_error ~loc:loc "not allowed inside axiomatic specification";
        try
          let _ = StringHashtblIter.find enum_types_table id in
          typing_error ~loc:d#pos "duplicate range type `%s'" id
        with
        | Not_found ->
          let ri =
            let (module E) = enum id in
              {
                ei_type = Enum (module E);
                ei_min = min;
                ei_max = max;
              }
            in
            StringHashtblIter.add enum_types_table id ri;
            acc
      end else
          acc
    | JCDtag (id, _, _parent, _fields, inv) ->
      if not only_types then begin
        Options.lprintf "Typing tag %s@." id;
        if in_axiomatic then
          typing_error ~loc:loc "not allowed inside axiomatic specification";
        let struct_info, _ = StringHashtblIter.find structs_table id in
        (* declare invariants as logical functions *)
        let invariants =
          List.fold_left
            (fun acc (id, x, e) ->
               if false (* ownership -- to be re-implemented ==> enable structure invariants *) then
                 typing_error ~loc:id#pos
                   "use of structure invariants requires declaration of an invariant policy";
               let vi =
                 var (JCTpointer (JCtag(struct_info, []), Some zero,
                                  Some zero)) x in
               let p = assertion [(x, vi)] e in
               let pi = make_pred id#name in
               pi.li_parameters <- [vi];
               pi.li_labels <- [LabelHere];
               eprintf "generating logic fun %s with one default label@."
                 pi.li_name;
               IntHashtblIter.replace logic_functions_table
                 pi.li_tag (pi, JCAssertion p);
               Hashtbl.replace logic_functions_env id#name pi;
               (pi, p) :: acc)
            []
            inv
        in
        StringHashtblIter.replace
          structs_table id (struct_info, invariants);
        acc
      end else acc
    | JCDvariant_type (_id, _tags) -> acc
    | JCDunion_type (_id, _discr, _tags) -> acc

    | JCDlogic_type(id,l) ->
      if only_types then begin
        Options.lprintf "Typing logic type declaration %s@." id;
        try
          let _ = StringHashtblIter.find logic_type_table id in
          typing_error ~loc:d#pos "duplicate logic type `%s'" id
        with
        | Not_found ->
          let l = List.map Type_var.type_var_from_string l in
          StringHashtblIter.add logic_type_table id (id,l);
          acc
      end else
        acc
    | JCDlemma (id, is_axiom, poly_args, labels, e) ->
      if not only_types then begin
        Options.lprintf "Typing lemma/axiom %s@." id;
        if is_axiom && not in_axiomatic then
          typing_error ~loc:loc "allowed only inside axiomatic specification";
        let poly_args = add_poly_args poly_args in
        let te = assertion [] e in
        let te = Type_var.subst_type_in_assertion uenv te in
        if in_axiomatic then
          (ADprop (d#pos, id, labels, (if is_axiom then `Axiom else `Lemma), te)) :: acc
        else begin
          StringHashtblIter.add lemmas_table id (d#pos, is_axiom, poly_args, labels, te);
          acc
        end
      end else
        acc
    | JCDglobal_inv (id, e) ->
      if not only_types then begin
        if in_axiomatic then
          typing_error ~loc:loc "not allowed inside axiomatic specification";
        let a = assertion [] e in
        let li = make_pred id in
        let idx = li.li_tag in
        if true (* ownership -- to be re-imlpemented *) then
          IntHashtblIter.replace logic_functions_table
            idx (li, JCAssertion a);
        IntHashtblIter.add global_invariants_table idx (li, a);
        acc
      end else
        acc
    | JCDexception (id, tyopt) ->
      if not only_types then begin
        if in_axiomatic then
          typing_error ~loc:loc "not allowed inside axiomatic specification";
        let tt = Option.map type_type tyopt in
        StringHashtblIter.add exceptions_table id (exception_info tt id);
        acc
      end else
        acc
    | JCDlogic_var (_ty, _id, _body) -> assert false
    | JCDlogic (None, id, poly_args, labels, pl, body) ->
        if not only_types then
          begin
            (*
              let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
            *)
            let param_env,_ty,pi = add_logic_fundecl (None,id,poly_args,labels,pl) in
            create_if_pragma_before id;
            let p = match body with
              | JCnone ->
                  if not in_axiomatic then
                    typing_error ~loc:loc "allowed only inside axiomatic specification";
                  JCNone
              | JCreads reads ->
                  if not in_axiomatic then
                    typing_error ~loc:loc "allowed only inside axiomatic specification";
                  JCReads (
                    (List.map
                       (fun a ->
                          let _,_,tl =
                            location param_env a
                          in tl)) reads)
              | JCexpr body ->
                JCAssertion(assertion param_env body)
              | JCinductive l ->
                  JCInductive(List.map
                                (fun (id,labels,e) ->
                                   let a = assertion param_env e in
                                   check_positivity a#pos pi a;
                                   (id,labels,a))
                                l)
            in
            update_axiomatic axiomatic pi;
            IntHashtblIter.add
              logic_functions_table pi.li_tag (pi, p);
            acc
          end
        else
          acc
    | JCDlogic (Some ty, id, poly_args, labels, pl, body) ->
        if not only_types then
          begin
            (*
              let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
            *)
            let param_env, ty, pi = add_logic_fundecl (Some ty,id,poly_args,labels,pl) in
            create_if_pragma_before id;
            let ty = match ty with Some ty -> ty | None -> assert false in
            let t = match body with
              | JCnone -> JCNone
              | JCreads reads ->
                  if not in_axiomatic then
                    typing_error ~loc:loc "allowed only inside axiomatic specification";
                  JCReads (
                    (List.map
                       (fun a ->
                          let _,_,tl = location param_env a
                          in tl)) reads)
              | JCexpr body ->
                  let t = term param_env body in
                  if pl = [] && not (subtype t#typ ty)
                    || pl <> [] && not (subtype ~strict:true t#typ ty) then
                      typing_error ~loc:d#pos
                        "inferred type differs from declared type"
                  else
                    begin
                      if pl = [] then
                        (* constant *)
                        Hashtbl.add logic_constants_table pi.li_tag (pi, t);
                      JCTerm t
                    end
                      (*
                        | JCaxiomatic l ->
                        JCAxiomatic(List.map (fun (id,e) -> (id,assertion param(_env e)) l)
                      *)
              | JCinductive _ ->
                  typing_error ~loc:d#pos
                    "only predicates can be inductively defined"
            in
            update_axiomatic axiomatic pi;
            IntHashtblIter.add
              logic_functions_table pi.li_tag (pi, t);
            acc
          end
        else
          acc
    | JCDaxiomatic(id,l) ->
        Options.lprintf "Typing axiomatic %s@." id;
        let data =
          {
            axiomatics_defined_ids = [];
            axiomatics_decls = [];
          }
        in
        data.axiomatics_decls <- List.fold_left
          (decl_aux ~only_types ~axiomatic:(Some (id,data))) [] l;
        if not only_types then
          begin
            if not String.(length id >= 15 && equal "LF__Axiomatic__" @@ sub id 0 15) then
              check_consistency id data;
            StringHashtblIter.add axiomatics_table id data
          end;
        acc

let decl ~only_types d =
  ignore (decl_aux ~only_types ~axiomatic:None [] d)

let declare_struct_info d =
  match d#node with
  | JCDtag (id, _, parent, _, _) ->
    let rec si =
      {
        si_params = [];
        si_name = id;
        si_fields = [];
        si_parent = None;
        si_final = true;
        si_hroot = si;
        si_root = None;
      }
    in
    StringHashtblIter.add structs_table id (si, []);
    (* declare the "mutable" field (if needed) *)
    if parent = None && false (* ownership -- to be re-implemented *) then
      create_mutable_field si
  | _ -> ()

let rec declare_function d =
  reset_uenv ();
  match d#node with
  | JCDfun(ty,id,pl,_specs,_body) ->
      ignore
        (add_fundecl (ty,id#pos,id#name,pl))
(*   | JCDlogic(Some ty,id,labels,[],_body) -> *)
(*       ignore  *)
(*      (add_logic_constdecl (ty,id)) *)
  | JCDlogic(ty,id,poly_args,labels,pl,_body) ->
(*
      let labels = match labels with [] -> [ LabelHere ] | _ -> labels in
*)
      ignore (add_logic_fundecl (ty,id,poly_args,labels,pl))
  | JCDaxiomatic(_id,l) ->
      List.iter declare_function l
  | _ -> ()

let declare_variable d = match d#node with
  | JCDvar(ty,id,_init) ->
      add_vardecl (ty,id)
  | _ -> ()

let compute_struct_info_parent d =
  match d#node with
  | JCDtag (id, _, Some (parent, _), _, _) ->
    let si, _ = StringHashtblIter.find structs_table id in
    let psi = find_struct_info d#pos parent in
    psi.si_final <- false;
    si.si_parent <- Some (psi, [])
  | _ -> ()

let fixpoint_struct_info_roots () =
  let modified = ref false in
  StringHashtblIter.iter
    (fun _ (si, _) ->
       match si.si_parent with
         | Some(psi, _) ->
             if si.si_hroot != psi.si_hroot then begin
               si.si_hroot <- psi.si_hroot;
               modified := true
             end
         | None -> ())
    structs_table;
  !modified

let type_variant d = match d#node with
  | JCDvariant_type(id, tags) | JCDunion_type(id,_,tags) ->
      (* declare the variant *)
      let vi = {
        ri_name = id;
        ri_hroots = [];
        ri_kind =
          (match d#node with
             | JCDvariant_type _ -> Rvariant
             | JCDunion_type(_,true,_) ->
                 Region.some_bitwise_region := true;
                 RdiscrUnion
             | JCDunion_type(_,false,_) ->
                 Region.some_bitwise_region := true;
                 RplainUnion
             | _ -> assert false
          );
        ri_union_size_in_bytes = 0;
      } in
      StringHashtblIter.add roots_table id vi;
      (* tags *)
      let roots = List.map
        (fun tag ->
           (* find the structure *)
           let st, _ = try
             StringHashtblIter.find structs_table tag#name
           with Not_found ->
             typing_error ~loc:tag#pos
               "undefined tag: %s" tag#name
           in
           (* the structure must be root *)
           if st.si_parent <> None then
             typing_error ~loc:tag#pos
               "the tag %s is not root" tag#name;
           (* the structure must not be used by another variant *)
           match st.si_root with
             | None ->
                 (* update the structure variant and return the root *)
                 st.si_root <- Some vi;
                 st
             | Some prev -> typing_error ~loc:tag#pos
                 "tag %s is already used by type %s" tag#name
                   prev.ri_name)
        tags
      in
      if root_is_union vi then
        let size =
          List.fold_left
            (fun size st -> max size (struct_size_in_bytes st)) 0 roots
        in
        vi.ri_union_size_in_bytes <- size
      else ();
      (* update the variant *)
      vi.ri_hroots <- roots
  | _ -> ()

let declare_tag_fields d = match d#node with
  | JCDtag(id, _, _, fields, _inv) ->
      let struct_info, _ = StringHashtblIter.find structs_table id in
      let root = struct_info.si_hroot in
      let _, fields =
        List.fold_left
          (fun (off, fs) (_, _, _, bs as f) -> off + bs, field struct_info root off f :: fs)
          (0, [])
          fields
      in
      struct_info.si_fields <- fields;
      StringHashtblIter.replace structs_table id (struct_info, [])
  | _ -> ()

let check_struct d = match d#node with
  | JCDtag(id, _, _, _, _) ->
      let loc = d#pos in
      let st = find_struct_info loc id in
      if st.si_hroot.si_root = None then
        typing_error ~loc:loc "the tag %s is not used by any type"
          st.si_name
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
  List.iter (decl ~only_types:false) ast;
  (* 7. test if all the pragma have been defined *)
  test_if_pragma_notdefined ()

let print_file fmt () =
  let functions =
    IntHashtblIter.fold
      (fun _ (finfo,_,fspec,slist) f ->
         Print.JCfun_def
           (finfo.fun_result.vi_type,finfo.fun_name,
            finfo.fun_parameters,fspec,slist)
         :: f
      ) functions_table []
  in
  let logic_functions =
    IntHashtblIter.fold
      (fun _ (linfo,tora) f ->
         Print.JClogic_fun_def
           (linfo.li_result_type,linfo.li_name,
            linfo.li_poly_args,
            linfo.li_labels,
            linfo.li_parameters, tora)
         :: f
      ) logic_functions_table []
  in
(*  let logic_constants =
    Hashtbl.fold
      (fun _ (vi,t) f ->
         Print.JClogic_const_def
           (vi.vi_type, vi.vi_name, Option.map fst t)
        :: f
      ) logic_constants_table []
  in *)
  let logic_types =
    StringHashtblIter.fold
      (fun _ (s,l) f -> Print.JClogic_type_def (s,l) :: f)
      logic_type_table
      []
  in
  let variables =
    IntHashtblIter.fold
      (fun _ (vinfo,vinit) f ->
         Print.JCvar_def
           (vinfo.vi_type,vinfo.vi_name,vinit)
         :: f
      ) variables_table []
  in
  let structs =
    StringHashtblIter.fold
      (fun name (sinfo,_) f ->
         let super = match sinfo.si_parent with
           | None -> None
           | Some(st, _) -> Some st.si_name
         in
         Print.JCstruct_def
           (name,super,sinfo.si_fields,[])
         :: f
      ) structs_table []
  in
  let variants =
    StringHashtblIter.fold
      (fun name vinfo f ->
        let tags =
          List.map (fun sinfo -> sinfo.si_name)
            vinfo.ri_hroots
        in
        Print.JCvariant_type_def (name,tags)
        :: f
      ) roots_table []
  in
  let enums =
    StringHashtblIter.fold
      (fun name rinfo f ->
         Print.JCenum_type_def
           (name,rinfo.ei_min,rinfo.ei_max)
         :: f
      ) enum_types_table []
  in
  let axioms =
    StringHashtblIter.fold
      (fun name (_loc,is_axiom,poly_args,labels, a) f ->
         Print.JClemma_def (name,is_axiom, poly_args, labels,a)
         :: f
      ) lemmas_table []
  in
  let global_invariants =
    IntHashtblIter.fold
      (fun _ (li, a) f ->
         Print.JCglobinv_def (li.li_name,a) :: f)
      global_invariants_table
      []
  in
  let exceptions =
    StringHashtblIter.fold
      (fun name ei f ->
         Print.JCexception_def (name,ei)
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
    @ (Print.JCrec_fun_defs
      (* (List.rev logic_constants @*) (List.rev logic_functions))
    :: (List.rev axioms)
    @ (List.rev global_invariants)
    @ [Print.JCrec_fun_defs (List.rev functions)]
  in
  Print.print_decls fmt tfile;

(*
Local Variables:
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End:
*)
