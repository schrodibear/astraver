(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: red.mli,v 1.4 2002-09-06 11:56:52 filliatr Exp $ i*)

open Cc
open Logic 

(* reduction on intermediate programs 
 * get rid of redexes of the kind let (x1,...,xn) = e in (x1,...,xn) *)

val red : predicate cc_term -> predicate cc_term

