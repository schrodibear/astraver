(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

val add_read  : Why_ident.t -> t -> t
val add_reads : Why_ident.set -> t -> t
val add_write : Why_ident.t -> t -> t
val add_writes : Why_ident.set -> t -> t
val add_exn : Why_ident.t -> t -> t
val add_exns : Why_ident.set -> t -> t
val add_nontermination : t -> t

val get_reads : t -> Why_ident.t list
val get_writes : t -> Why_ident.t list
val get_exns : t -> Why_ident.t list
val get_repr : t -> Why_ident.t list * Why_ident.t list * Why_ident.t list * bool

val is_read  : t -> Why_ident.t -> bool    (* read-only *)
val is_write : t -> Why_ident.t -> bool    (* read-write *)
val is_exn : t -> Why_ident.t -> bool
val is_nonterminating : t -> bool

val union : t -> t -> t

val remove : Why_ident.t -> t -> t
val remove_exn : Why_ident.t -> t -> t
val remove_nontermination : t -> t

val keep_writes : t -> t
val erase_exns : t -> t

val occur : Why_ident.t -> t -> bool

val subst : Why_logic.var_substitution -> t -> t

open Format

val print : formatter -> t -> unit

