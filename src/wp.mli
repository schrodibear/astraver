(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: wp.mli,v 1.5 2002-03-06 16:04:52 filliatr Exp $ i*)

open Types
open Env

val propagate : typed_program -> typed_program * assertion option



