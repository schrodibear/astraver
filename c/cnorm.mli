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

(*i $Id: cnorm.mli,v 1.6 2005-04-22 08:56:23 hubert Exp $ i*)

open Cast

(*
val sizeof : Loc.t -> tctype -> int64

val eval_const_expr : Cast.texpr -> int64

*)

val int_nconstant : string -> nterm

val nzero : nterm

val valid_for_type : 
  ?fresh:bool -> Loc.t -> string -> 
    nterm -> npredicate

val separation :
    Loc.t -> Info.var_info -> Info.var_info -> Ctypes.ctype Clogic.npredicate

val local_separation :  
  Loc.t -> string -> Ctypes.ctype Clogic.nterm -> string -> 
  Ctypes.ctype Clogic.nterm -> Ctypes.ctype Clogic.npredicate
(*val separation_intern : 
  Loc.t -> Info.var_info ->Ctypes.ctype Clogic.npredicate

val separation : 
  Loc.t -> Info.var_info -> 
  ?allocs:(string -> nterm -> (string * npredicate) list) -> nterm -> 
    (string -> nterm -> (string * npredicate) list) * 
    (string * npredicate) list
*)
val make_and : npredicate -> npredicate -> npredicate

val file : tdecl located list -> ndecl located list

val in_struct :  nterm -> Info.var_info -> nterm 
