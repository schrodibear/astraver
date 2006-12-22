(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
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

(* $Id: jc_envset.ml,v 1.5 2006-12-22 13:13:24 marche Exp $ *)

open Jc_env

module StringSet = Set.Make(String)

module StringMap = Map.Make(String)

module VarSet = 
  Set.Make(struct type t = var_info
		  let compare v1 v2 = 
		    Pervasives.compare 
		      v1.jc_var_info_tag v2.jc_var_info_tag
	   end)

module FieldOrd =
  struct type t = field_info
	 let compare f1 f2 = 
	   Pervasives.compare 
	     f1.jc_field_info_tag f2.jc_field_info_tag
  end

module FieldSet = Set.Make(FieldOrd)

module FieldMap = Map.Make(FieldOrd)

module ExceptionOrd =   
  struct type t = exception_info
	 let compare f1 f2 = 
	   Pervasives.compare 
	     f1.jc_exception_info_tag f2.jc_exception_info_tag
  end

module ExceptionSet = Set.Make(ExceptionOrd)

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
