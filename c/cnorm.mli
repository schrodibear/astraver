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

(*i $Id: cnorm.mli,v 1.1 2004-11-30 14:31:23 hubert Exp $ i*)

open Cast

(*
val sizeof : Loc.t -> tctype -> int64

val eval_const_expr : Cast.texpr -> int64

*)
val valid_for_type : 
  ?fresh:bool -> Loc.t -> Info.var_info -> 
    nterm -> npredicate

val separation : 
  Loc.t -> Info.var_info -> 
  ?allocs:(nterm -> npredicate) -> nterm -> (nterm -> npredicate) * npredicate

val make_and : npredicate -> npredicate -> npredicate

val file : tdecl located list -> ndecl located list
