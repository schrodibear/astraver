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

(*i $Id: ident.ml,v 1.44 2003-02-27 16:55:34 filliatr Exp $ i*)

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

let rec next id =
  if not (is_index id) then
    id ^ "0"
  else
    let n = String.length id in
    match id.[n - 1] with
      | '0'..'8' as c -> 
	  let id' = String.copy id in 
	  id'.[n - 1] <- Char.chr (Char.code c + 1); 
	  id'
      | '9' ->
	  let id' = String.sub id 0 (n - 1) in
	  (next (if is_index id' then id' else id' ^ "0")) ^ "0"
      | _ -> 
	  assert false

let rec next_away id s =
  if Idset.mem id s then next_away (create (next id.name)) s else id

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

let t_add_float = create "add_float"
let t_sub_float = create "sub_float"
let t_mul_float = create "mul_float"
let t_div_float = create "div_float"
let t_neg_float = create "neg_float"

let t_mod_int = create "mod_int"
let t_sqrt_float = create "sqrt_float"

let t_float_of_int = create "float_of_int"

let t_lt = create "%lt"
let t_le = create "%le"
let t_gt = create "%gt"
let t_ge = create "%ge"
let t_eq = create "%eq"
let t_neq = create "%neq"

let t_eq_int = create "eq_int"
let t_eq_bool = create "eq_bool"
let t_eq_float = create "eq_float"
let t_eq_unit = create "eq_unit"

let t_neq_int = create "neq_int"
let t_neq_bool = create "neq_bool"
let t_neq_float = create "neq_float"
let t_neq_unit = create "neq_unit"

let t_lt_int = create "lt_int"
let t_le_int = create "le_int"
let t_gt_int = create "gt_int"
let t_ge_int = create "ge_int"

let t_lt_float = create "lt_float"
let t_le_float = create "le_float"
let t_gt_float = create "gt_float"
let t_ge_float = create "ge_float"

let t_zwf_zero = create "%zwf_zero"
let result = create "result"
let default = create "_"
let array_length = create "array_length"
let access = create "access"
let store = create "store"
let annot_bool = create "annot_bool"
let well_founded = create "well_founded"
let well_founded_induction = create "well_founded_induction"
let if_then_else = create "if_then_else"

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

let is_float_comparison id = 
  id == t_eq_float || id == t_neq_float ||
  id == t_lt_float || id == t_le_float || id == t_gt_float || id == t_ge_float 

let is_bool_comparison id = id == t_eq_bool || id == t_neq_bool
let is_unit_comparison id = id == t_eq_unit || id == t_neq_unit

let is_eq id = 
  id == t_eq || id == t_eq_int || id == t_eq_float || 
  id == t_eq_bool || id == t_eq_unit

let is_neq id = 
  id == t_neq || id == t_neq_int || id == t_neq_float || 
  id == t_neq_bool || id == t_neq_unit

let is_relation id = 
  is_comparison id || is_int_comparison id || is_float_comparison id ||
  is_bool_comparison id || is_unit_comparison id

let is_int_arith_binop id =
  id == t_add_int || id == t_sub_int || id == t_mul_int || id == t_div_int ||
  id == t_mod_int

let is_float_arith_binop id =
  id == t_add_float || id == t_sub_float || id == t_mul_float || 
  id == t_div_float

let is_arith_binop id =
  is_int_arith_binop id || is_float_arith_binop id

let is_int_arith_unop id = 
  id == t_neg_int

let is_float_arith_unop id =
  id == t_neg_float || id == t_sqrt_float

let is_int_arith id = 
  is_int_arith_binop id || is_int_arith_unop id

let is_float_arith id =
  is_float_arith_binop id || is_float_arith_unop id

let is_arith id =
  is_int_arith id || is_float_arith id || id == t_float_of_int
