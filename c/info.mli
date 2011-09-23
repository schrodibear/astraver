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



type why_type = 
  | Memory of why_type * zone
  | Pointer of zone
  | Addr of zone
  | Int
  | Real
  | Unit 
  | Why_Logic of string 

and zone = 
    {
      zone_is_var : bool;
      number : int;
      mutable repr : zone option;
      name : string;
(*      mutable type_why_zone : why_type*)
    }

val same_zone : zone -> zone -> bool

val same_why_type : why_type -> why_type -> bool

val same_why_type_no_zone : why_type -> why_type -> bool


val repr : zone -> zone

val found_repr : ?quote_var:bool -> zone -> string


val output_why_type : ?quote_var:bool -> why_type -> Output.logic_type

val output_zone_name : ?quote_var:bool -> zone -> Output.logic_type

type var_info = private
    {
      var_name : string;
      var_uniq_tag : int;
      mutable var_unique_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_referenced : bool;
      mutable var_is_static : bool;
      mutable var_is_a_formal_param : bool;
      mutable enum_constant_value : int64;
      mutable var_type : Ctypes.ctype;
      mutable var_why_type : why_type;
    }

val default_var_info : string -> var_info

val set_assigned : var_info -> unit

val unset_assigned : var_info -> unit

val set_is_referenced : var_info -> unit

val without_dereference : var_info -> ('a -> 'b) -> 'a -> 'b

val set_static : var_info -> unit

val set_formal_param : var_info -> unit

val unset_formal_param : var_info -> unit

val set_const_value : var_info -> int64 -> unit

module HeapVarSet : Set.S with type elt = var_info

module HeapVarMap : Map.S with type key = var_info

module ZoneSet : Set.S with type elt = zone * string * why_type

val print_hvs : Format.formatter -> HeapVarSet.t -> unit

type label =
  | Label_current
  | Label_name of string

module LabelSet : Set.S with type elt = label

type logic_info =
    {
      logic_name : string;
      mutable logic_heap_zone : ZoneSet.t;
      mutable logic_heap_args : HeapVarSet.t;
(* see the .ml
      mutable logic_heap_args : LabelSet.t HeapVarMap.t;
*)
      mutable logic_args : var_info list;
      mutable logic_why_type : why_type;
      mutable logic_args_zones : zone list;
    }

val default_logic_info : string -> logic_info

type fun_info =
    {
      fun_tag : int;
      fun_name : string;
      mutable fun_unique_name : string;
      mutable function_reads : ZoneSet.t;
      mutable function_writes : ZoneSet.t;
      mutable function_reads_var : HeapVarSet.t;
      mutable function_writes_var : HeapVarSet.t;
      mutable has_assigns : bool;
      mutable fun_type : Ctypes.ctype;
      mutable args : var_info list;
      mutable args_zones : zone list;
      mutable graph : fun_info list;
      mutable type_why_fun : why_type;
      mutable has_body : bool;
    }

val default_fun_info : string -> fun_info

type env_info =
  | Var_info of var_info
  | Fun_info of fun_info

val env_name : env_info -> string

val set_unique_name : env_info -> string -> unit

val var_type : env_info -> Ctypes.ctype

val get_why_type : env_info -> why_type

val set_var_type : env_info -> Ctypes.ctype -> why_type -> unit

val set_var_type_why : env_info -> why_type -> unit



type label_info =
    { label_info_name : string;
      mutable times_used : int;
    }
