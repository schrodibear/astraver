(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: effect.mli,v 1.11 2002-07-04 09:31:12 filliatr Exp $ i*)

(*s The abstract type of effects. *)

type t

val bottom : t

val add_read  : Ident.t -> t -> t
val add_reads : Ident.set -> t -> t
val add_write : Ident.t -> t -> t
val add_writes : Ident.set -> t -> t
val add_exn : Ident.t -> t -> t
val add_exns : Ident.set -> t -> t

val get_reads : t -> Ident.t list
val get_writes : t -> Ident.t list
val get_exns : t -> Ident.t list
val get_repr : t -> Ident.t list * Ident.t list * Ident.t list

val is_read  : t -> Ident.t -> bool    (* read-only *)
val is_write : t -> Ident.t -> bool    (* read-write *)
val is_exn : t -> Ident.t -> bool

val keep_writes : t -> t

val union : t -> t -> t

val remove : Ident.t -> t -> t
val remove_exn : Ident.t -> t -> t

val occur : Ident.t -> t -> bool

val subst : Logic.var_substitution -> t -> t

open Format

val print : formatter -> t -> unit

