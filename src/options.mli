(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.mli,v 1.2 2002-02-07 15:11:51 filliatr Exp $ i*)

val verbose : bool ref

val verbosely : ('a -> unit) -> 'a -> unit

val debug : bool ref

val type_only : bool ref

type prover = Coq | Pvs

val prover : prover ref

