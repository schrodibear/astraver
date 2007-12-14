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

(* $Id: jc_env.mli,v 1.37 2007-12-14 14:28:06 moy Exp $ *)

type native_type = Tunit | Tboolean | Tinteger | Treal

type inv_sem = InvNone | InvOwnership | InvArguments

type region = 
    {
      jc_reg_variable : bool;
      jc_reg_id : int;
      jc_reg_name : string;
    }

type jc_type =
  | JCTnative of native_type
  | JCTlogic of string
  | JCTenum of enum_info
  | JCTpointer of struct_info * Num.num option * Num.num option
  | JCTnull

and enum_info =
    { 
      jc_enum_info_name : string;
      jc_enum_info_min : Num.num;
      jc_enum_info_max : Num.num;
    }

and struct_info =
    { 
              jc_struct_info_name : string;
      mutable jc_struct_info_parent : struct_info option;
      mutable jc_struct_info_root : string;
      mutable jc_struct_info_fields : field_info list;
    }

and field_info =
    {
      jc_field_info_tag : int;
      jc_field_info_name : string;
      jc_field_info_final_name : string;
      jc_field_info_type : jc_type;
      jc_field_info_struct: struct_info; (* The structure in which the field is defined *)
      jc_field_info_root : string; (* The root of the structure in which the field is defined *)
      jc_field_info_rep : bool; (* "rep" flag *)
    }

type var_info = {
    jc_var_info_tag : int;
    jc_var_info_name : string;
    mutable jc_var_info_final_name : string;
    mutable jc_var_info_type : jc_type;
    mutable jc_var_info_region : region;
    mutable jc_var_info_formal : bool;
    mutable jc_var_info_assigned : bool;
    jc_var_info_static : bool;
  }

type exception_info =
    {
      jc_exception_info_tag : int;
      jc_exception_info_name : string;
      jc_exception_info_type : jc_type option;
    }


(*
Local Variables: 
compile-command: "unset LANG ; make -C .. bin/jessie.byte"
End: 
*)
