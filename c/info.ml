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

(*i $Id: info.ml,v 1.7 2004-03-24 08:22:03 filliatr Exp $ i*)

module HeapVarSet = Set.Make(String)

type var_info =
    {
      var_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_static : bool;
      mutable function_reads : HeapVarSet.t;
      mutable function_writes : HeapVarSet.t;
    }

let default_var_info x =
  { var_name = x; 
    var_is_assigned = false;
    var_is_static = false;
    function_reads = HeapVarSet.empty;
    function_writes = HeapVarSet.empty; 
  }

type logic_info =
    {
      logic_name : string;
      mutable logic_args : HeapVarSet.t;
    }

let default_logic_info x =
  { logic_name = x;
    logic_args = HeapVarSet.empty }

