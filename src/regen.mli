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

(*i $Id: regen.mli,v 1.5 2004-01-29 09:15:00 filliatr Exp $ i*)

(* files partly edited and partly regenerated *)

open Format
open Cc
open Logic
open Vcg

type element_kind = 
  | Param
  | Oblig
  | Valid (* obsolete but helps porting from old versions *)
  | Ax

type element_id = element_kind * string

type element = 
  | Parameter of string * cc_type
  | Obligation of obligation
  | Axiom of string * predicate

module type S = sig
 
  (* how to print and reprint elements *)
  val print_element : formatter -> element -> unit
  val reprint_element : formatter -> element -> unit

  (* regexp to recognize obligations locations (as comments) *)
  val re_oblig_loc : Str.regexp

  (* what to print at the beginning of file when first created *)
  val first_time : formatter -> unit

  (* how to recognize the end of an element to erase / overwrite *)
  val not_end_of_element : element_id -> string -> bool

end

module Make(X : S) : sig 

  val add_elem : element_id -> element -> unit

  val add_regexp : string -> element_kind -> unit

  val reset : unit -> unit

  val regen : string -> formatter -> unit

  val first_time : formatter -> unit

  val output_file : int -> string -> unit

end

