(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: effect.mli,v 1.6 2002-03-13 16:15:46 filliatr Exp $ i*)

(*s The abstract type of effects. *)

type t

val bottom : t

val add_read  : Ident.t -> t -> t
val add_reads : Ident.set -> t -> t
val add_write : Ident.t -> t -> t

val get_reads : t -> Ident.t list
val get_writes : t -> Ident.t list
val get_repr : t -> (Ident.t list) * (Ident.t list)

val is_read  : t -> Ident.t -> bool    (* read-only *)
val is_write : t -> Ident.t -> bool    (* read-write *)

val union : t -> t -> t

val remove : Ident.t -> t -> t

val occur : Ident.t -> t -> bool

val subst : (Ident.t * Ident.t) list -> t -> t

open Format

val print : formatter -> t -> unit

