(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: cltyping.mli,v 1.1 2004-01-14 16:33:28 filliatr Exp $ i*)

(* Typing of C annotations *)

open Clogic

val type_predicate : 'a -> parsed_predicate -> Cast.predicate
val type_spec : 'a -> parsed_spec -> Cast.predicate spec
val type_loop_annot : 'a -> parsed_loop_annot -> Cast.loop_annot

