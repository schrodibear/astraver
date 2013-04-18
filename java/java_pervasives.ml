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



(*** Utility functions ***)


open Java_env

(* for method_info types *)

let get_method_info_class_or_interface_name mi =
  match mi.method_info_class_or_interface with
    | TypeClass ci -> ci.class_info_name
    | TypeInterface ii -> ii.interface_info_name
(*
    | TypeLogic _ -> assert false
*)

open Java_ast

(* for parsed exprs *)

let expr_no_loc e = 
  { java_pexpr_loc = Loc.dummy_position ; java_pexpr_node = e }

let expr_node_true = JPElit(Bool true)

let expr_true = expr_no_loc expr_node_true

let expr_zero = expr_no_loc (JPElit(Integer "0"))


open Java_tast

(* for typed statements *)

let make_statement_no_loc node = 
  { java_statement_loc = Loc.dummy_position ; java_statement_node = node }
    
(* for typed exprs *)

let make_expr_no_loc t node = 
  { java_expr_loc = Loc.dummy_position ;
    java_expr_type = t ;
    java_expr_node = node }
    
    
(*
let default_loop_annotation =
  { kml_loop_invariant = expr_true;
    kml_loop_assigns = None;
    kml_loop_variant = expr_zero;
  }

let default_method_specification =
  { kml_requires = expr_true;
  }
*)

open Java_env

let null_type = JTYnull
let unit_type = JTYbase Tunit
let boolean_type = JTYbase Tboolean
let integer_type = JTYbase Tinteger
let int_type = JTYbase Tint
let real_type = JTYbase Treal
let double_type = JTYbase Tdouble
let float_type = JTYbase Tfloat
let logic_string_type = JTYbase Tstring

let min_byte = Num.num_of_string "-128"
let max_byte = Num.num_of_string "127"
let min_short = Num.num_of_string "-32768"
let max_short = Num.num_of_string "32767"
let min_int = Num.num_of_string "-2147483648"
let max_int = Num.num_of_string "2147483647"
let min_long = Num.num_of_string "-9223372036854775808"
let max_long = Num.num_of_string "9223372036854775807"
let min_char = Num.num_of_string "0"
let max_char = Num.num_of_string "65535"

let in_byte_range n = Num.le_num min_byte n && Num.le_num n max_byte
let in_short_range n = Num.le_num min_short n && Num.le_num n max_short
let in_char_range n = Num.le_num min_char n && Num.le_num n max_char

(* variables *)

module StringSet = Set.Make(String)

(* used names (in order to rename identifiers when necessary) *)
let used_names = Hashtbl.create 97

let mark_as_used x = 
  Hashtbl.add used_names x ()

let () = 
  List.iter mark_as_used 
    (* Jessie reserved names *)
    [ "tag"; "type" ; "end" ; "begin" ; "let" ; "in"]

let is_used_name n = Hashtbl.mem used_names n

let use_name ?local_names n = 
  if is_used_name n then raise Exit; 
  begin match local_names with 
    | Some h -> if StringSet.mem n h then raise Exit 
    | None -> () 
  end;
  mark_as_used n;
  n

let rec next_name ?local_names n i = 
  let n_i = n ^ "_" ^ string_of_int i in
  try use_name ?local_names n_i 
  with Exit -> next_name ?local_names n (succ i)

let get_unique_name ?local_names n = 
  try use_name ?local_names n 
  with Exit -> next_name ?local_names n 0

let get_final_name id =
  if id = "\\result" then id else
    get_unique_name id


let new_var =
  let var_tag_counter = ref 0 in
  fun loc ty id ->
    incr var_tag_counter;
    let vi = {
      java_var_info_tag = !var_tag_counter;
      java_var_info_name = id;
      java_var_info_decl_loc = loc;
      java_var_info_final_name = get_final_name id;
      java_var_info_type = ty;
      java_var_info_assigned = false;
    }
    in vi

(* logic functions *)

let logic_info = 
  let logic_tag_counter = ref 0 in
  fun id ty labels pars ->
    incr logic_tag_counter;
    { java_logic_info_tag = !logic_tag_counter;
      java_logic_info_name = id;
      java_logic_info_labels = labels;
      java_logic_info_parameters = pars;
      java_logic_info_result_type = ty;
      java_logic_info_calls = [];
    }

(*
let real_max_fi = 
  let x = new_var Loc.dummy_position real_type "x" in
  let y = new_var Loc.dummy_position real_type "y" in
  logic_info "\\real_max" (Some real_type) [] [x;y] 
*)

let builtin_logic_symbols =
  [ (Some real_type, "\\cos", [real_type]) ;
    (Some real_type, "\\real_abs", [real_type]) ;
    (Some real_type, "\\real_max", [real_type; real_type]) ;
    (Some real_type, "\\real_min", [real_type; real_type]) ;
    (Some integer_type, "\\int_max", [integer_type; integer_type]) ;
    (Some integer_type, "\\int_min", [integer_type; integer_type]) ;
  ]


(* AG, 08/13/2009. 
   For (Java_typing.get_type_decl ... JPTimport(...)). *)
(* From a qualified identifier qid to a string.
  Can be used to implement Java_???.print_qualified_ident. *)
let rec qualified_ident2string qid separator = 
  match qid with
    | [] -> ""
    | [(_,id)] -> id
    | (_,id)::r ->
        (qualified_ident2string r separator) ^ separator ^ id

(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
