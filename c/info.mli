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

(*i $Id: info.mli,v 1.12 2004-10-21 14:52:45 hubert Exp $ i*)

type var_info = private 
    {
      var_name : string;
      var_uniq_tag : int;
      mutable var_unique_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_static : bool;
      mutable enum_constant_value : int64;
    }

val default_var_info : string -> var_info

val set_assigned : var_info -> unit

val set_static : var_info -> unit

val set_const_value : var_info -> int64 -> unit

module HeapVarSet : Set.S with type elt = var_info

type logic_info =
    {
      logic_name : string;
      mutable logic_args : HeapVarSet.t;
    }

val default_logic_info : string -> logic_info

(*
type field_info = { 
  field_name : string;
  field_tag : string;
  mutable field_heap_var_name : string;
}
*)

type fun_info =
    {
      fun_name : string;
      mutable fun_unique_name : string;
      mutable function_reads : HeapVarSet.t;
      mutable function_writes : HeapVarSet.t;
      mutable has_assigns : bool;
    }

val default_fun_info : string -> fun_info

type env_info =
  | Var_info of var_info
  | Fun_info of fun_info

val set_unique_name : env_info -> string -> unit


