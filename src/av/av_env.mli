(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

open Output_ast

type float_format = [ `Double | `Float | `Binary80 ]

type native_type = Tunit | Tboolean | Tinteger | Treal | Tgenfloat of float_format | Tstring

type float_model = FMmath | FMdefensive | FMfull | FMmultirounding

type float_rounding_mode = FRMDown | FRMNearestEven | FRMUp | FRMToZero | FRMNearestAway

type float_instruction_set = FISstrictIEEE754 | FISx87

type root_kind = Rvariant | RplainUnion | RdiscrUnion

type some_enum =
  | Int : 'a repr * 'b bit -> some_enum
  | Enum : (module Enum with type t = 'a) -> some_enum

type jc_type =
  | JCTnative of native_type
  | JCTlogic of (string * jc_type list)
  | JCTenum of enum_info
  | JCTpointer of pointer_class * Num.num option * Num.num option
  | JCTnull
  | JCTany (* used when typing (if ... then raise E else ...):
              raise E is any *)
  | JCTtype_var of type_var_info

and type_var_info = {
  tvi_name : string;
  tvi_tag  : int;
  tvi_univ : bool
}
(* The variable is universally quantified *)

and pointer_class =
  | JCtag of struct_info * jc_type list (* struct_info, type parameters *)
  | JCroot of root_info

and enum_info = {
  ei_type : some_enum;
  ei_min  : Num.num;
  ei_max  : Num.num
}

and struct_info = {
          si_params : type_var_info list;
          si_name   : string;
  mutable si_parent : (struct_info * jc_type list) option;
  mutable si_hroot  : struct_info;
  mutable si_fields : field_info list;
  mutable si_root   : root_info option; (* only valid for root structures *)
  mutable si_final  : bool;
}

and root_info = {
          ri_name   : string;
  mutable ri_hroots : struct_info list;
          ri_kind   : root_kind;
  mutable ri_union_size_in_bytes : int;
}

and field_info = {
  fi_tag        : int;
  fi_name       : string;
  fi_final_name : string;
  fi_type       : jc_type;
  fi_struct     : struct_info;
  (* The structure in which the field is defined *)
  fi_hroot      : struct_info;
  (* The root of the structure in which the field is defined *)
  fi_rep        : bool; (* "rep" flag *)
  fi_abstract   : bool; (* "abstract" flag *)
  fi_bitsize    : int; (* Size of the field in bits, optional *)
  fi_bitoffset  : int
}

type region = {
  mutable r_variable   : bool;
  mutable r_bitwise    : bool;
          r_id         : int;
          r_name       : string;
          r_final_name : string;
          r_type       : jc_type;
}

type var_info = {
          vi_tag        : int;
          vi_name       : string;
  mutable vi_final_name : string;
  mutable vi_type       : jc_type;
  mutable vi_region     : region;
  mutable vi_formal     : bool;
  mutable vi_assigned   : bool;
          vi_static     : bool;
          vi_bound      : bool;
}

type exception_info = {
  exi_tag  : int;
  exi_name : string;
  exi_type : jc_type option;
}

type label_info = {
          lab_name       : string;
          lab_final_name : string;
  mutable lab_times_used : int;
}

type label =
  | LabelName of label_info
  | LabelHere
  | LabelPost
  | LabelPre
  | LabelOld

type alloc_class =
  | JCalloc_root of root_info
  | JCalloc_bitvector

type mem_class =
  | JCmem_field of field_info
  | JCmem_plain_union of root_info
  | JCmem_bitvector

type (_, _, _, 'a, _, _) arg =
  | Singleton : ('result, _, _, [<`Singleton | `Range_0_n | `Range_l_r], [`Singleton], 'result) arg
  | Range_0_n : (_, 'result, _, [`Range_0_n | `Singleton], [`Range_0_n], 'result) arg
  | Range_l_r : (_, _, 'result, [`Range_l_r | `Singleton], [`Range_l_r], 'result) arg


(*
Local Variables:
compile-command: "unset LANG ; make -C .. byte"
End:
*)
