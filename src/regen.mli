(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: regen.mli,v 1.21 2008-01-24 08:11:14 regisgia Exp $ i*)

(* files partly edited and partly regenerated *)

open Format
open Cc
open Logic
open Vcg

type element_kind = 
  | Param
  | Oblig
  | Prog
  | Valid (* obsolete but helps porting from old versions *)
  | Lg
  | Ax
  | Pr
  | Fun
  | Ty

type element_id = element_kind * string

type element = 
  | Parameter of string * cc_type
  | Program of string * cc_type * cc_functional_program
  | Obligation of Loc.floc * Logic_decl.expl_kind * string * sequent Env.scheme
  | Logic of string * logic_type Env.scheme
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme
  | Function of string * function_def Env.scheme
  | AbstractType of string * string list

module type S = sig
 
  (* how to print and reprint elements *)
  val print_element : formatter -> element -> unit
  val reprint_element : formatter -> element -> unit

  (* regexp to recognize obligations locations (as comments) *)
  val re_oblig_loc : Str.regexp

  (* what to print at the beginning of file when first created *)
  val first_time : formatter -> unit

  (* what to print at the end of file when first created *)
  val first_time_trailer : formatter -> unit

  (* how to recognize the end of an element to erase / overwrite *)
  val not_end_of_element : element_id -> string -> bool

end

module Make(X : S) : sig 

  val add_elem : element_id -> element -> unit

  val add_regexp : string -> element_kind -> unit

  val reset : unit -> unit

  val regen : string -> formatter -> unit

  val first_time : formatter -> unit

  val output_file : ?margin:int -> string -> unit

end

