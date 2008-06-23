(** Type variables: unification, generalization, ... *)

(** The type of type variables. *)
type t

(** Obtain a fresh type variable. *)
val fresh: unit -> t

(** Find the value associated to a type variable. *)
val find: t -> t list -> 'a list -> 'a
(** Useful for type parameters.

[find v params param_values]: if [List.nth params i = v], return
[List.nth param_values i]. *)

(** Unique ID of a variable, different for each variable, even if it is
quantified. *)
val uid: t -> int
