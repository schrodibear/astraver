(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: wp.mli,v 1.6 2002-09-12 11:31:25 filliatr Exp $ i*)

open Types
open Env

val propagate : typed_program -> typed_program * postcondition option



