(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: cprint.mli,v 1.2 2004-12-14 13:51:54 hubert Exp $ i*)

(* Pretty-printer for normalized AST *)

open Format
open Clogic
open Cast

val ctype : formatter -> Ctypes.ctype -> unit

val nexpr : formatter -> nexpr -> unit

val nstatement : formatter -> nstatement -> unit

val ndecl : formatter -> ndecl located -> unit

val nfile : formatter -> nfile -> unit

val npredicate :  formatter -> npredicate -> unit
