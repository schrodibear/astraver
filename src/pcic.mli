(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: pcic.mli,v 1.1 2001-08-15 21:08:52 filliatr Exp $ i*)

open Ast
open Rawterm


(* transforms intermediate functional programs into (raw) CIC terms *)

val rawconstr_of_prog : cc_term -> rawconstr

