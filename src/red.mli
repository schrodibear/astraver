(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: red.mli,v 1.2 2001-08-24 19:07:17 filliatr Exp $ i*)

open Ast

(* reduction on intermediate programs 
 * get rid of redexes of the kind let (x1,...,xn) = e in (x1,...,xn) *)

val red : cc_term -> cc_term

