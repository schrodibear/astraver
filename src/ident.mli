
(*s Indentifiers. *)

type t

val create : string -> t

val string : t -> string

type name = Anonymous | Name of t

module Idset : Set.S with type elt = t
type set = Idset.t

module Idmap : Map.S with type key = t

val next_away : t -> set -> t

val print : Format.formatter -> t -> unit

(*s Bound variables. *)

type bound

val bound : unit -> bound

val bound_id : bound -> int

(*s Some pre-defined Ident.ts. *)

val t_add : t
val t_sub : t
val t_mul : t
val t_div : t
val t_neg : t
val t_sqrt : t

val t_lt : t
val t_le : t
val t_gt : t
val t_ge : t
val t_eq : t
val t_noteq : t

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

val is_relation : t -> bool
val is_arith : t -> bool
