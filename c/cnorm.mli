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

(*i $Id: cnorm.mli,v 1.9 2005-11-07 15:13:29 hubert Exp $ i*)

open Cast

(*
val sizeof : Loc.t -> tctype -> int64

val eval_const_expr : Cast.texpr -> int64

*)

val int_nconstant : string -> nterm

val nzero : nterm

val file : tdecl located list -> ndecl located list

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




