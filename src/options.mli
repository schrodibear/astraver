(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.mli,v 1.4 2002-03-05 14:41:51 filliatr Exp $ i*)

(*s General options *)

val verbose : bool ref

val if_verbose : ('a -> unit) -> 'a -> unit
val if_verbose_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_verbose_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

val debug : bool ref

val if_debug : ('a -> unit) -> 'a -> unit
val if_debug_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_debug_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

(*i val dprintf : ('a, Format.formatter, unit) format -> 'a i*)

(*s Typing options *)

val type_only : bool ref
val wp_only : bool ref

(*s Prover options *)

type prover = Coq | Pvs

val prover : prover ref

