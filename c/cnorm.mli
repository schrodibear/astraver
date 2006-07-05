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

(*i $Id: cnorm.mli,v 1.13 2006-07-05 09:44:35 filliatr Exp $ i*)

open Cast

(*
val sizeof : Loc.t -> tctype -> int64

val eval_const_expr : Cast.texpr -> int64

*)

val int_nconstant : string -> nterm

val nzero : nterm

val file : tdecl located list -> ndecl located list

val make_field : Ctypes.ctype -> Info.var_info

val declare_arrow_var : Info.var_info -> Info.var_info

val type_why_table : 
  (Info.zone,(Info.var_info, Info.why_type) Hashtbl.t) Hashtbl.t  

val type_why_new_zone : Info.zone -> Info.var_info -> unit

val find_zone : nexpr -> Info.zone

val find_zone_for_term : nterm -> Info.zone

val type_why_for_term : nterm -> Info.why_type

val type_why : nexpr -> Info.why_type

val why_type_for_float_kind : Ctypes.cfloat -> string

(* smart constructors for predicates *)

val make_and : npredicate -> npredicate -> npredicate
val make_forall : nctype Clogic.typed_quantifiers -> npredicate -> npredicate
val make_implies : npredicate -> npredicate -> npredicate

val nptrue : npredicate
val npand : npredicate * npredicate -> npredicate
val nprel : nterm * Clogic.relation * nterm -> npredicate
val npvalid : nterm -> npredicate
val npvalid_range : nterm * nterm * nterm -> npredicate
val npapp : Info.logic_info * nterm list -> npredicate
val npfresh : nterm -> npredicate
val npiff : npredicate * npredicate -> npredicate



