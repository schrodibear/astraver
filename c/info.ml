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

(*i $Id: info.ml,v 1.10 2004-10-06 12:50:31 hubert Exp $ i*)

module HeapVarSet = Set.Make(String)

type var_info =
    {
      var_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_static : bool;
      mutable enum_constant_value : int64;
      mutable function_reads : HeapVarSet.t;
      mutable function_writes : HeapVarSet.t;
      mutable has_assigns : bool;
    }

let default_var_info x =
  { var_name = x; 
    var_is_assigned = false;
    var_is_static = false;
    enum_constant_value = Int64.zero;
    function_reads = HeapVarSet.empty;
    function_writes = HeapVarSet.empty; 
    has_assigns = false
  }

type logic_info =
    {
      logic_name : string;
      mutable logic_args : HeapVarSet.t;
    }

let default_logic_info x =
  { logic_name = x;
    logic_args = HeapVarSet.empty }

type field_info = { 
  field_name : string;
  field_tag : string;
  mutable field_heap_var_name : string;
}
