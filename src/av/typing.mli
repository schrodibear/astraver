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
open Ast
open Fenv
open Common

val default_label : label list -> label option

val typing_error : loc:Loc.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val is_root_struct : struct_info -> bool

val substruct : struct_info -> pointer_class -> bool

val logic_type_table : (string * type_var_info list) StringHashtblIter.t

val logic_constants_table :
  (int, logic_info * Fenv.logic_info Ast.term) Hashtbl.t

val logic_functions_table:
  (logic_info * term_or_assertion) IntHashtblIter.t

val functions_table :
  (fun_info * Loc.position * fun_spec * expr option) IntHashtblIter.t

val variables_table : (var_info * expr option) IntHashtblIter.t

val structs_table:
  (struct_info * (logic_info * assertion) list) StringHashtblIter.t

val roots_table: (root_info) StringHashtblIter.t

val enum_types_table: enum_info StringHashtblIter.t

val lemmas_table :
  (Loc.position * bool * type_var_info list * label list * assertion)
  StringHashtblIter.t

type axiomatic_decl =
  | ADprop of Loc.position * string * Env.label list * [ `Axiom | `Lemma ] * Constructors.assertion

type axiomatic_data = private
    {
      mutable axiomatics_defined_ids : logic_info list;
      mutable axiomatics_decls : axiomatic_decl list;
    }

val axiomatics_table : axiomatic_data StringHashtblIter.t

val global_invariants_table :
  (logic_info * assertion) IntHashtblIter.t

val exceptions_table: exception_info StringHashtblIter.t

exception Typing_error of Loc.position * string

val implicit_coerce : ?expand_int:bool -> jc_type -> jc_type -> expr -> expr

val type_range_of_term : jc_type -> term -> assertion

val find_struct_root : Env.struct_info -> Env.root_info

val type_file : nexpr decl list -> unit

val print_file : Format.formatter -> unit -> unit

val type_labels_in_decl : nexpr decl -> unit

val occurrences : int list -> assertion -> (label * label) list list list

val pragma_gen_sep :  (int,
   [ `Sep | `Inc | `Cni] *
   [ `Logic of Fenv.logic_info * string list * Env.var_info list
   | `Pointer of Env.var_info ] list) Stdlib.Hashtbl.t

val pragma_gen_frame :
  (int, Fenv.logic_info * Fenv.logic_info
    * Env.var_info list * Env.var_info list *
      [ `Frame | `Sub ]) Stdlib.Hashtbl.t

val pragma_gen_same :
  (int, Fenv.logic_info) Stdlib.Hashtbl.t

val comparable_types : jc_type -> jc_type -> bool

val same_type_no_coercion : jc_type -> jc_type -> bool
