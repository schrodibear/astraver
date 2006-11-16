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

(* $Id: jc_fenv.mli,v 1.3 2006-11-16 16:42:45 marche Exp $ *)

open Jc_env
open Jc_envset

type effects =
    {
      jc_writes_fields : FieldSet.t;
    }

type fun_info =
    {
      jc_fun_info_tag : int;
      jc_fun_info_name : string;
      jc_fun_info_return_type : jc_type;
      mutable jc_fun_info_parameters : var_info list;
      mutable jc_fun_info_calls : fun_info list;
      mutable jc_fun_info_logic_apps : logic_info list;
      mutable jc_fun_info_effects : effects;
    }


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
