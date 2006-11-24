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


type native_type =
  [ `Tunit | `Tboolean | `Tinteger | `Treal ]

type jc_type =
  | JCTnative of native_type
  | JCTlogic of string
  | JCTpointer of struct_info * int * int

and struct_info =
    { 
      jc_struct_info_name : string;
      jc_struct_info_parent : struct_info option;
      jc_struct_info_root : string;
      jc_struct_info_fields : (string * field_info) list;
    }

and field_info =
    {
      jc_field_info_tag : int;
      jc_field_info_name : string;
      jc_field_info_type : jc_type;
    }


type var_info =
    {
      jc_var_info_name : string;
      jc_var_info_final_name : string;
      jc_var_info_type : jc_type;
      mutable jc_var_info_assigned : bool;
    }


type exception_info =
    {
      jc_exception_info_name : string;
      jc_exception_info_type : jc_type;
    }



(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
