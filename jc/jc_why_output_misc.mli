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

open Jc_why_output_ast
open Format

(* Logic types *)
val logic_type_var : string -> logic_type
val is_prop : logic_type -> bool

(* Terms *)
val match_term : (string * term) list -> term -> term -> (string * term) list
val make_var : string -> term

val make_positioned : Jc_position.t -> ?behavior:string -> ?kind:vc_kind -> term -> term
val make_located : Loc.floc -> ?behavior:string -> ?kind:vc_kind -> term -> term
val make_positioned_lex : Loc.position -> ?behavior:string -> ?kind:vc_kind -> term -> term

(* Assertions *)
val make_or : assertion -> assertion -> assertion
val make_and : assertion -> assertion -> assertion
val make_or_list : assertion list -> assertion
val make_and_list : assertion list -> assertion
val make_forall_list : (string * logic_type) list -> trigger list list -> assertion -> assertion
val make_impl : assertion -> assertion -> assertion
val make_impl_list : assertion -> assertion list -> assertion
val make_equiv : assertion -> assertion -> assertion

val is_not_true : assertion -> bool

val assertion_of_term : term -> assertion

val mk_positioned : Jc_position.t -> ?behavior:string -> ?kind:vc_kind -> assertion -> assertion
val mk_located : Loc.floc -> ?behavior:string -> ?kind:vc_kind -> assertion -> assertion
val mk_positioned_lex : Loc.position -> ?behavior:string -> ?kind:vc_kind -> assertion -> assertion

(* Why types *)
val int_type : why_type
val bool_type : why_type
val unit_type : why_type
val base_type : string -> why_type

(* Expressions *)
val mk_expr : expr_node -> expr
val mk_var : string -> expr
val void : expr
val make_or_expr : expr -> expr -> expr
val make_and_expr : expr -> expr -> expr
val make_app : ?ty:why_type -> string -> expr list -> expr
val make_logic_app : ?ty:why_type -> string -> expr list -> expr
val make_app_e : ?ty:why_type -> expr -> expr list -> expr

val make_positioned_e : Jc_position.t -> ?behavior:string -> ?kind:vc_kind -> expr -> expr
val make_located_e : Loc.floc -> ?behavior:string -> ?kind:vc_kind -> expr -> expr
val make_positioned_lex_e : Loc.position -> ?behavior:string -> ?kind:vc_kind -> expr -> expr

(** [make_label l e] adds label [l] to [e]
    In the case of a block, add it to the first instruction of the block, if there
    is one. *)
val make_label : string -> expr -> expr
(** [make_while cond inv dec e] builds
    [while cond do { invariant inv variant dec } e]
    applying simplifications if possible *)
val make_while : expr -> assertion -> variant option -> expr -> expr
val make_pre : assertion -> expr -> expr
val append : expr -> expr -> expr

(* Declarations *)
val id_no_loc : string -> why_id
val get_why_id : why_decl -> why_id
val iter_why_decl : (string -> unit) -> why_decl -> unit
val output_decls : ('a -> why_id) -> ((string -> unit) -> 'a -> 'b) -> ('a -> 'c) -> 'a list -> unit

(* Misc. utility functions *)
val abs_fname : string -> string
val fprintf_comma_string_list : formatter -> string list -> unit

(* Why *.loc files *)
val why_reg_pos : string -> (vc_kind option * string option * string option * string * int * int * int) -> unit
val why_get_pos : string -> (vc_kind option * string option * string option * string * int * int * int)
val why_print_locs : (formatter -> vc_kind -> unit) -> formatter -> unit

(* Jc *.loc files *)
val jc_reg_pos : string -> ?id:string -> ?kind:vc_kind -> ?name:string -> ?formula:string -> Loc.floc -> string
val jc_print_pos : (formatter -> vc_kind -> unit) -> formatter -> unit
