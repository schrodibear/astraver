
(*i $Id: ident.mli,v 1.15 2002-03-27 14:15:11 filliatr Exp $ i*)

(*s Identifiers. *)

type t

val create : string -> t

val string : t -> string

module Idset : Set.S with type elt = t
type set = Idset.t

module Idmap : Map.S with type key = t

val next_away : t -> set -> t

val print : Format.formatter -> t -> unit

(*s Possibly anonymous names *)

type name = Anonymous | Name of t

val print_name : Format.formatter -> name -> unit

(*s Qualified identifiers with labels. *)

val at_id : t -> string -> t
val un_at : t -> t * string
val is_at : t -> bool
val adr_id : t -> t

(*s Bound variables. *)

type bound

val bound : unit -> bound

val bound_id : bound -> int

val print_bound : Format.formatter -> bound -> unit

(*s Some pre-defined identifiers. *)

val anonymous : t

val t_add : t
val t_sub : t
val t_mul : t
val t_div : t
val t_mod : t
val t_neg : t
val t_sqrt : t

val t_lt : t
val t_le : t
val t_gt : t
val t_ge : t
val t_eq : t
val t_neq : t

val t_eq_int : t
val t_eq_bool : t
val t_eq_float : t
val t_eq_unit : t

val t_neq_int : t
val t_neq_bool : t
val t_neq_float : t
val t_neq_unit : t

val t_zwf_zero : t
val result : t
val default : t
val access : t
val store : t
val annot_bool : t
val well_founded : t
val well_founded_induction : t

val p_or : t
val p_and : t
val p_not : t

val is_eq_neq : t -> bool
val is_comparison : t -> bool
val is_relation : t -> bool
val is_arith : t -> bool
