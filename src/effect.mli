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

(*i $Id: effect.mli,v 1.13 2002-10-17 15:01:53 filliatr Exp $ i*)

(*s The abstract type of effects. *)

type t

val bottom : t

val add_read  : Ident.t -> t -> t
val add_reads : Ident.set -> t -> t
val add_write : Ident.t -> t -> t
val add_writes : Ident.set -> t -> t
val add_exn : Ident.t -> t -> t
val add_exns : Ident.set -> t -> t

val get_reads : t -> Ident.t list
val get_writes : t -> Ident.t list
val get_exns : t -> Ident.t list
val get_repr : t -> Ident.t list * Ident.t list * Ident.t list

val is_read  : t -> Ident.t -> bool    (* read-only *)
val is_write : t -> Ident.t -> bool    (* read-write *)
val is_exn : t -> Ident.t -> bool

val union : t -> t -> t

val remove : Ident.t -> t -> t
val remove_exn : Ident.t -> t -> t

val keep_writes : t -> t
val erase_exns : t -> t

val occur : Ident.t -> t -> bool

val subst : Logic.var_substitution -> t -> t

open Format

val print : formatter -> t -> unit

