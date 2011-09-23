(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



(*s The abstract type of effects. *)

type t

val bottom : t

val add_read  : Ident.t -> t -> t
val add_reads : Ident.set -> t -> t
val add_write : Ident.t -> t -> t
val add_writes : Ident.set -> t -> t
val add_exn : Ident.t -> t -> t
val add_exns : Ident.set -> t -> t
val add_nontermination : t -> t

val get_reads : t -> Ident.t list
val get_writes : t -> Ident.t list
val get_exns : t -> Ident.t list
val get_repr : t -> Ident.t list * Ident.t list * Ident.t list * bool

val is_read  : t -> Ident.t -> bool    (* read-only *)
val is_write : t -> Ident.t -> bool    (* read-write *)
val is_exn : t -> Ident.t -> bool
val is_nonterminating : t -> bool

val union : t -> t -> t

val remove : Ident.t -> t -> t
val remove_exn : Ident.t -> t -> t
val remove_nontermination : t -> t

val keep_writes : t -> t
val erase_exns : t -> t

val occur : Ident.t -> t -> bool

val subst : Logic.var_substitution -> t -> t

open Format

val print : formatter -> t -> unit

