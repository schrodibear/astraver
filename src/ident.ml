(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: ident.ml,v 1.52 2004-05-25 12:33:03 filliatr Exp $ i*)

type t = { stamp : int; name : string; label : string option }

let hashcons = 
  let h = Hashtbl.create 97 in
  fun id -> try Hashtbl.find h id with Not_found -> Hashtbl.add h id id; id 

let create s = hashcons { stamp = 0; name = s; label = None }

let string s = s.name

module I = struct type t_ = t type t = t_ let compare = compare end

module Idset = Set.Make(I)
type set = Idset.t

module Idmap = Map.Make(I)
type 'a map = 'a Idmap.t

let is_index s = 
  let n = String.length s in
  (n > 0) && (match s.[n-1] with '0'..'9' -> true | _ -> false)

let rec next id n s =
  let id' = create (id ^ string_of_int n) in
  if Idset.mem id' s then
    next id (succ n) s
  else
    id'

let next_away id s = 
  if id.name <> "_" && Idset.mem id s then 
    let id0 = id.name in
    let id0 = if is_index id0 then id0 ^ "_" else id0 in
    next id0 0 s 
  else 
    id

let print fmt s = Format.fprintf fmt "%s" s.name

let lprint fmt s = match s.label with
  | None -> Format.fprintf fmt "%s" s.name
  | Some l -> Format.fprintf fmt "%s@@%s" s.name l

let dbprint fmt s = Format.fprintf fmt "%a#%d" lprint s s.stamp

(*s Possibly anonymous names *)

type name = Anonymous | Name of t

let print_name fmt = function
  | Name id -> print fmt id
  | Anonymous -> Format.fprintf fmt "_"

(*s Labelled identifiers. *)

let at_id id d = hashcons { id with label = Some d }

let is_at id = id.label <> None

let un_at = function
  | { label = Some d } as id -> hashcons { id with label = None }, d
  | _ -> invalid_arg "Ident.un_at"

(*s Bound variables. *)

let bound =
  let n = ref 0 in
  fun s -> incr n; hashcons { s with stamp = !n }

(*s Exceptions names and constructors *)

let exn_type = create "EM"
let exn_val = create "Val"
let exn_exn = create "Exn"
let exn_post = create "qcomb"
let exn_qval = create "Qval"
let exn_qexn = create "Qexn"
let exist = create "exist"
let decomp n = create ("decomp" ^ string_of_int n)

let exit_exn = create "Exit"

(*s Pre-defined. *)

let anonymous = create "_"
let implicit = create "?"
let default_post = create "%default_post"

let t_add = create "%add"
let t_sub = create "%sub"
let t_mul = create "%mul"
let t_div = create "%div"
let t_neg = create "%neg"

let t_add_int = create "add_int"
let t_sub_int = create "sub_int"
let t_mul_int = create "mul_int"
let t_div_int = create "div_int"
let t_neg_int = create "neg_int"

let t_add_real = create "add_real"
let t_sub_real = create "sub_real"
let t_mul_real = create "mul_real"
let t_div_real = create "div_real"
let t_neg_real = create "neg_real"

let t_mod_int = create "mod_int"
let t_sqrt_real = create "sqrt_real"

let t_real_of_int = create "real_of_int"
let t_int_of_real = create "int_of_real"

let t_lt = create "%lt"
let t_le = create "%le"
let t_gt = create "%gt"
let t_ge = create "%ge"
let t_eq = create "%eq"
let t_neq = create "%neq"

let t_eq_int = create "eq_int"
let t_eq_bool = create "eq_bool"
let t_eq_real = create "eq_real"
let t_eq_unit = create "eq_unit"

let t_neq_int = create "neq_int"
let t_neq_bool = create "neq_bool"
let t_neq_real = create "neq_real"
let t_neq_unit = create "neq_unit"

let t_lt_int = create "lt_int"
let t_le_int = create "le_int"
let t_gt_int = create "gt_int"
let t_ge_int = create "ge_int"

let t_lt_real = create "lt_real"
let t_le_real = create "le_real"
let t_gt_real = create "gt_real"
let t_ge_real = create "ge_real"

let t_zwf_zero = create "%zwf_zero"
let result = create "result"
let default = create "H"
let array_length = create "array_length"
let access = create "access"
let store = create "store"
let annot_bool = create "annot_bool"
let well_founded = create "well_founded"
let well_founded_induction = create "well_founded_induction"
let if_then_else = create "if_then_else"
let false_rec = create "False_rec"

let any_int = create "why_any_int"
let any_unit = create "why_any_unit"
let any_real = create "why_any_real"

(*s tests *)

let is_wp id =
  String.length id.name >= 2 && id.name.[0] == 'W' && id.name.[1] == 'P'

let is_variant id =
  String.length id.name >= 7 && String.sub id.name 0 7 = "Variant"

let is_comparison id = 
  id == t_lt || id == t_le || id == t_gt || id == t_ge || 
  id == t_eq || id == t_neq 

let is_poly id =
  is_comparison id || 
  id == t_add || id == t_sub || id == t_mul || id == t_div || id == t_neg

let is_int_comparison id =
  id == t_eq_int || id == t_neq_int ||
  id == t_lt_int || id == t_le_int || id == t_gt_int || id == t_ge_int 

let is_real_comparison id = 
  id == t_eq_real || id == t_neq_real ||
  id == t_lt_real || id == t_le_real || id == t_gt_real || id == t_ge_real 

let is_bool_comparison id = id == t_eq_bool || id == t_neq_bool
let is_unit_comparison id = id == t_eq_unit || id == t_neq_unit

let is_eq id = 
  id == t_eq || id == t_eq_int || id == t_eq_real || 
  id == t_eq_bool || id == t_eq_unit

let is_neq id = 
  id == t_neq || id == t_neq_int || id == t_neq_real || 
  id == t_neq_bool || id == t_neq_unit

let is_relation id = 
  is_comparison id || is_int_comparison id || is_real_comparison id ||
  is_bool_comparison id || is_unit_comparison id

let is_int_arith_binop id =
  id == t_add_int || id == t_sub_int || id == t_mul_int || id == t_div_int ||
  id == t_mod_int

let is_real_arith_binop id =
  id == t_add_real || id == t_sub_real || id == t_mul_real || 
  id == t_div_real

let is_arith_binop id =
  is_int_arith_binop id || is_real_arith_binop id

let is_int_arith_unop id = 
  id == t_neg_int

let is_real_arith_unop id =
  id == t_neg_real || id == t_sqrt_real

let is_int_arith id = 
  is_int_arith_binop id || is_int_arith_unop id

let is_real_arith id =
  is_real_arith_binop id || is_real_arith_unop id

let is_arith id =
  is_int_arith id || is_real_arith id || id == t_real_of_int
