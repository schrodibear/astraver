(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
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

(*i $Id: mlize.mli,v 1.7 2002-10-18 11:18:38 filliatr Exp $ i*)

(*s translation of imperative programs into intermediate functional programs *)

open Ast
open Cc
open Env
open Logic

val trans : typed_program -> Rename.t -> predicate cc_term

