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



open Env

(** Type variables: unification, generalization, ... *)

(** The type of type variables. *)
type t = type_var_info

(** Obtain a fresh type variable. *)
val type_var_from_string: ?univ:bool -> string -> t
(** Univ set if the variable is universally quantified (prenex)
    The argument is the name of the variable.
It can be anything, it shall only be used for pretty-printing purposes. *)

(** Unique ID of a variable, different for each variable, even if it is
quantified. *)
val uid: t -> int

(** The name of a variable, which should only be used for
pretty-printing purposes. *)
val name: t -> string

(** The unique name of a variable, which is composed of its name and its UID. *)
val uname: t -> string

(** The environnement of unification *)
type env

(** The type of function used in case of unification error *)
type 'a typing_error = loc:Loc.position -> ('a, Format.formatter, unit, unit) format4 -> 'a

type typing_error_arg = { f : 'a. 'a typing_error }

val create : typing_error_arg -> env
val reset : env -> unit

(** Add a universally quantified type var to substitute with the string
    invalid_argument is raised if the string is yet bind *)
val add_type_var : env -> string -> t

(** Try to get a universally quantified var from a string
    Not_found is raised if there is no binding*)
val find_type_var : env -> string -> t

(** Add an equality for unification of logic type variable*)
val add : ?subtype:bool -> env ->  Loc.position -> jc_type -> jc_type -> unit

val subst : env -> jc_type -> jc_type

(** Get instances of a list of type variables,
    return a substitution function *)
val instance : t list -> (jc_type -> jc_type)

(** Print the set of universally quantified type variables,
    and the set of equalities *)
val print : Format.formatter -> env -> unit

(** Substitute in an assertion the type variable which are in
    the environnement env *)
val subst_type_in_assertion :
  env ->
  Fenv.logic_info Ast.assertion ->
  Fenv.logic_info Ast.assertion
