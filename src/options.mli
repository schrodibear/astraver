(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(*i $Id: options.mli,v 1.8 2002-07-18 14:45:06 filliatr Exp $ i*)

(*s General options *)

val verbose : bool

val if_verbose : ('a -> unit) -> 'a -> unit
val if_verbose_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_verbose_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

val debug : bool

val if_debug : ('a -> unit) -> 'a -> unit
val if_debug_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_debug_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

(*s Typing options *)

val parse_only : bool
val type_only : bool
val wp_only : bool

(*s Prover options *)

type prover = Coq | Pvs

val prover : prover

val valid : bool

val coq_tactic : string option

(*s Files given on the command line *)

val files : string list
