(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: wp.mli,v 1.8 2002-10-15 09:05:53 filliatr Exp $ i*)

open Types
open Env

val wp : typed_program -> typed_program * assertion option



