(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.mli,v 1.1 2002-01-24 15:59:30 filliatr Exp $ i*)

val verbose : bool ref

val verbosely : ('a -> unit) -> 'a -> unit

val debug : bool ref

type prover = Coq | Pvs

val prover : prover ref

