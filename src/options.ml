(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.ml,v 1.1 2002-01-24 15:59:30 filliatr Exp $ i*)

let verbose = ref false

let verbosely f x = if !verbose then f x

let debug = ref false

type prover = Coq | Pvs

let prover = ref Coq

