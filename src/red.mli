(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: red.mli,v 1.3 2002-03-20 16:01:44 filliatr Exp $ i*)

open Ast
open Logic 

(* reduction on intermediate programs 
 * get rid of redexes of the kind let (x1,...,xn) = e in (x1,...,xn) *)

val red : predicate cc_term -> predicate cc_term

