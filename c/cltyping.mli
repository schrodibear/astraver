(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: cltyping.mli,v 1.34 2006-11-03 12:48:56 marche Exp $ i*)

(* Typing of C annotations *)

open Clogic
open Cast
open Cenv

(* logical environments *)
val type_term : Env.t -> parsed_term  -> tterm
val type_ghost_lvalue : Env.t -> parsed_term  -> tterm
val type_predicate : Env.t -> parsed_predicate -> Cast.predicate
val type_location : Env.t -> parsed_term location -> tterm location
val type_spec : tctype option -> Env.t -> parsed_spec -> Cast.spec
val type_loop_annot : Env.t -> parsed_loop_annot -> Cast.loop_annot
val type_logic_type : Loc.position -> Env.t -> parsed_logic_type -> tctype
val int_constant : string -> tterm
val zero : tterm
