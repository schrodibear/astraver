(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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
  Jc_fenv.logic_info -> Jc_fenv.term_or_assertion -> unit
(** (compute_logic_calls f t) adds to the set of known calls of logic function 
    f the logic calls that occur in t
*)

val compute_calls : 
  Jc_fenv.fun_info -> Jc_fenv.fun_spec -> Jc_constructors.expr -> unit
(** (compute_calls f spec body) adds to the set of known calls of
     program f the logic calls that occur in spec and the program
     calls that occur in body
*)

val compute_logic_components :   
  (Jc_fenv.logic_info * Jc_fenv.term_or_assertion)
  Jc_pervasives.IntHashtblIter.t 
  -> Jc_fenv.logic_info list array

val compute_components :   
  (Jc_fenv.fun_info * Loc.position * Jc_fenv.fun_spec * Jc_fenv.expr option) 
  Jc_pervasives.IntHashtblIter.t 
  -> Jc_fenv.fun_info list array
