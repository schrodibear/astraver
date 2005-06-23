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

(*i $Id: monomorph.mli,v 1.3 2005-06-23 12:52:04 filliatr Exp $ i*)

(* make a monorphic output for provers not supporting polymorphism
   (e.g. PVS or CVC Lite) *)

open Logic
open Cc
open Vcg
open Format

module type S = sig
  val declare_type : formatter -> pure_type -> unit

  val print_parameter : formatter -> string -> cc_type -> unit
  val print_logic_instance : 
    formatter -> string -> instance -> logic_type -> unit
  val print_predicate_def_instance : 
    formatter -> string -> instance -> predicate_def -> unit
  val print_function_def_instance : 
    formatter -> string -> instance -> function_def -> unit
  val print_axiom_instance :
    formatter -> string -> instance -> predicate -> unit
  val print_obligation : formatter -> obligation -> unit
end

module Make(X : S) : sig
  val print_obligation : formatter -> obligation -> unit
  val print_axiom : formatter -> string -> predicate Env.scheme -> unit
  val print_logic : formatter -> string -> logic_type Env.scheme -> unit
  val print_parameter : formatter -> string -> cc_type -> unit
  val print_predicate_def : 
    formatter -> string -> predicate_def Env.scheme -> unit
  val print_function_def : 
    formatter -> string -> function_def Env.scheme -> unit

  val reset : unit -> unit
end
