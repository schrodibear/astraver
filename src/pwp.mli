(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: pwp.mli,v 1.1 2001-08-15 21:08:54 filliatr Exp $ *)

open Term
open Env

val update_post : local_env -> string -> Effect.t -> constr -> constr

val propagate : Rename.t -> typed_program -> typed_program
