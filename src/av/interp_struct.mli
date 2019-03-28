(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
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
(*  AstraVer fork:                                                        *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

open Env
open Fenv
open Output_ast

val struc : struct_info -> some_entry list

val root : root_info -> some_entry list

val alloc :
  arg:('a expr, check_size:bool -> unbounded integer number expr -> 'a expr,
       _, [ `Range_0_n | `Singleton ], _, 'r) arg ->
  alloc_class * region -> pointer_class -> 'r

val free : safe:bool -> alloc_class * region -> pointer_class -> 'a expr -> void expr

val valid_pre : in_param:bool -> effect -> var_info -> pred

val instanceof_pre : effect -> var_info -> pred

val valid : in_param:bool -> ?label:label -> equal:bool -> alloc_class * region -> pointer_class -> 'a term
  -> 'b term option -> 'c term option -> pred

val fresh: for_:[ `alloc_tables_in of [ `fresh of label ] ] -> in_param:bool -> alloc_class * region -> pointer_class
  -> 'b term -> 'c term -> pred
