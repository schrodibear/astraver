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

(*i $Id: info.ml,v 1.14 2004-11-22 16:14:27 filliatr Exp $ i*)

type var_info =
    {
      var_name : string;
      var_uniq_tag : int;
      mutable var_unique_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_referenced : bool;
      mutable var_is_static : bool;
      mutable var_is_a_formal_param : bool;
      mutable enum_constant_value : int64;
    }

let tag_counter = ref 0

let default_var_info x =
  incr tag_counter;
  { var_name = x; 
    var_uniq_tag = !tag_counter;
    var_unique_name = x;
    var_is_assigned = false;
    var_is_referenced = false;
    var_is_static = false;
    var_is_a_formal_param = false;
    enum_constant_value = Int64.zero;
  }

let set_assigned v = v.var_is_assigned <- true

let set_is_referenced v = v.var_is_referenced <- true

let set_static v = v.var_is_static <- true

let set_formal_param v = v.var_is_a_formal_param <- true

let unset_formal_param v = v.var_is_a_formal_param <- false

let set_const_value v n = v.enum_constant_value <- n

module HeapVarSet = 
  Set.Make(struct type t = var_info 
		  let compare i1 i2 = 
		      Pervasives.compare i1.var_uniq_tag i2.var_uniq_tag 
	   end)

type logic_info =
    {
      logic_name : string;
      mutable logic_args : HeapVarSet.t;
    }

let default_logic_info x =
  { logic_name = x;
    logic_args = HeapVarSet.empty }

type fun_info =
    {
      fun_name : string;
      mutable fun_unique_name : string;
      mutable function_reads : HeapVarSet.t;
      mutable function_writes : HeapVarSet.t;
      mutable has_assigns : bool;
    }

let default_fun_info x =
  { fun_name = x; 
    fun_unique_name = x;
    function_reads = HeapVarSet.empty;
    function_writes = HeapVarSet.empty; 
    has_assigns = false
  }


type env_info =
  | Var_info of var_info
  | Fun_info of fun_info

let set_unique_name e n =
  match e with
    | Var_info v -> v.var_unique_name <- n
    | Fun_info f -> f.fun_unique_name <- n
