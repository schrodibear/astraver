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

(*i $Id: cnorm.mli,v 1.3 2004-12-15 16:03:46 hubert Exp $ i*)

open Cast

(*
val sizeof : Loc.t -> tctype -> int64

val eval_const_expr : Cast.texpr -> int64

*)
val valid_for_type : 
  ?fresh:bool -> Loc.t -> Info.var_info -> 
    nterm -> npredicate

val separation :
    Loc.t -> Info.var_info -> Info.var_info -> Ctypes.ctype Clogic.npredicate

val separation_intern : 
  Loc.t -> Info.var_info ->Ctypes.ctype Clogic.npredicate

(*val separation : 
  Loc.t -> Info.var_info -> 
  ?allocs:(string -> nterm -> (string * npredicate) list) -> nterm -> 
    (string -> nterm -> (string * npredicate) list) * 
    (string * npredicate) list
*)
val make_and : npredicate -> npredicate -> npredicate

val file : tdecl located list -> ndecl located list
