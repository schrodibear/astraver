
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: red.mli,v 1.1 2001-08-17 00:52:39 filliatr Exp $ *)

open Ast

(* reduction on intermediate programs 
 * get rid of redexes of the kind let (x1,...,xn) = e in (x1,...,xn) *)

val red : cc_term -> cc_term

