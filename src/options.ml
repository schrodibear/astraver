(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.ml,v 1.2 2002-02-07 15:11:51 filliatr Exp $ i*)

let verbose = ref false

let verbosely f x = if !verbose then f x

let debug = ref false

let type_only = ref false

type prover = Coq | Pvs

let prover = ref Coq

