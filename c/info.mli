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

(*i $Id: info.mli,v 1.29 2006-06-22 13:07:17 hubert Exp $ i*)

type why_type = 
  | Memory of why_type * zone
  | Pointer of zone
  | Addr of zone
  | Int
  | Float of Ctypes.cfloat
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

val output_why_type : why_type -> string list * string

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

module ZoneSet : Set.S with type elt = zone * string * why_type

val print_hvs : Format.formatter -> HeapVarSet.t -> unit

type logic_info =
    {
      logic_name : string;
      mutable logic_heap_zone : ZoneSet.t;
      mutable logic_heap_args : HeapVarSet.t;
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

val set_var_type : env_info -> Ctypes.ctype -> why_type -> unit

val set_var_type_why : env_info -> why_type -> unit



