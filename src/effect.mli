(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(*i $Id: effect.mli,v 1.10 2002-06-24 09:37:35 filliatr Exp $ i*)

(*s The abstract type of effects. *)

type t

val bottom : t

val add_read  : Ident.t -> t -> t
val add_reads : Ident.set -> t -> t
val add_write : Ident.t -> t -> t
val add_writes : Ident.set -> t -> t

val get_reads : t -> Ident.t list
val get_writes : t -> Ident.t list
val get_repr : t -> Ident.t list * Ident.t list

val is_read  : t -> Ident.t -> bool    (* read-only *)
val is_write : t -> Ident.t -> bool    (* read-write *)

val keep_writes : t -> t

val union : t -> t -> t

val remove : Ident.t -> t -> t

val occur : Ident.t -> t -> bool

val subst : Logic.var_substitution -> t -> t

open Format

val print : formatter -> t -> unit

