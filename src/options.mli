(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.mli,v 1.6 2002-03-20 16:01:44 filliatr Exp $ i*)

(*s General options *)

val verbose : bool ref

val if_verbose : ('a -> unit) -> 'a -> unit
val if_verbose_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_verbose_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

val debug : bool ref

val if_debug : ('a -> unit) -> 'a -> unit
val if_debug_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_debug_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

(*s Typing options *)

val parse_only : bool ref
val type_only : bool ref
val wp_only : bool ref

(*s Prover options *)

type prover = Coq | Pvs

val prover : prover ref

val valid : bool ref
