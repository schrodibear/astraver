(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

val compute_logic_calls :
  Fenv.logic_info -> Fenv.term_or_assertion -> unit
(** (compute_logic_calls f t) adds to the set of known calls of logic function
    f the logic calls that occur in t
*)

val compute_calls :
  Fenv.fun_info -> Fenv.fun_spec -> Constructors.expr -> unit
(** (compute_calls f spec body) adds to the set of known calls of
     program f the logic calls that occur in spec and the program
     calls that occur in body
*)

val compute_logic_components :
  (Fenv.logic_info * Fenv.term_or_assertion)
  Common.IntHashtblIter.t
  -> Fenv.logic_info list array

val compute_components :
  (Fenv.fun_info * Why_loc.position * Fenv.fun_spec * Fenv.expr option)
  Common.IntHashtblIter.t
  -> Fenv.fun_info list array
