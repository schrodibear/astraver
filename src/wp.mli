(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: wp.mli,v 1.7 2002-10-01 13:12:05 filliatr Exp $ i*)

open Types
open Env

val propagate : typed_program -> typed_program * assertion option



