(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: pmlize.mli,v 1.1 2001-08-15 21:08:53 filliatr Exp $ *)

open Ast
open Env
open Names

(* translation of imperative programs into intermediate functional programs *)

val trans : Rename.t -> typed_program -> cc_term

