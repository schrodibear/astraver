(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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


type termination_policy = TPalways | TPnever | TPuser

type float_format = [ `Double | `Float | `Binary80 ]

type native_type = 
    Tunit | Tboolean | Tinteger | Treal | Tgenfloat of float_format | Tstring

type inv_sem = InvNone | InvOwnership | InvArguments

type separation_sem = SepNone | SepRegions

type annotation_sem = 
    AnnotNone | AnnotInvariants | AnnotElimPre | AnnotStrongPre | AnnotWeakPre

type abstract_domain = AbsNone | AbsBox | AbsOct | AbsPol

type int_model = IMbounded | IMmodulo

type float_model = FMmath | FMdefensive | FMfull | FMmultirounding

type float_rounding_mode = 
    FRMDown | FRMNearestEven | FRMUp | FRMToZero | FRMNearestAway

type float_instruction_set = FISstrictIEEE754 | FISx87

type root_kind = Rvariant | RplainUnion | RdiscrUnion

type jc_type =
  | JCTnative of native_type
  | JCTlogic of (string * jc_type list)
  | JCTenum of enum_info
  | JCTpointer of pointer_class * Num.num option * Num.num option
  | JCTnull
  | JCTany (* used when typing (if ... then raise E else ...): 
              raise E is any *)
  | JCTtype_var of type_var_info

and type_var_info =  { jc_type_var_info_name : string;
                       jc_type_var_info_tag : int;
                       jc_type_var_info_univ : bool} 
(* The variable is universally quantified *)

and pointer_class =
  | JCtag of struct_info * jc_type list (* struct_info, type parameters *)
  | JCroot of root_info

and enum_info =
    { 
      jc_enum_info_name : string;
      jc_enum_info_min : Num.num;
      jc_enum_info_max : Num.num;
    }

and struct_info =
    { 
              jc_struct_info_params : type_var_info list;
              jc_struct_info_name : string;
      mutable jc_struct_info_parent : (struct_info * jc_type list) option;
      mutable jc_struct_info_hroot : struct_info;
      mutable jc_struct_info_fields : field_info list;
      mutable jc_struct_info_root : root_info option;
        (* only valid for root structures *)
    }

and root_info =
    {
      jc_root_info_name : string;
(*      mutable jc_root_info_tags : struct_info list;*)
      mutable jc_root_info_hroots : struct_info list;
(*      jc_root_info_open : bool;*)
      jc_root_info_kind : root_kind;
      mutable jc_root_info_union_size_in_bytes: int;
    }

and field_info =
    {
      jc_field_info_tag : int;
      jc_field_info_name : string;
      jc_field_info_final_name : string;
      jc_field_info_type : jc_type;
      jc_field_info_struct: struct_info;
        (* The structure in which the field is defined *)
      jc_field_info_hroot : struct_info;
        (* The root of the structure in which the field is defined *)
      jc_field_info_rep : bool; (* "rep" flag *)
      jc_field_info_abstract : bool; (* "abstract" flag *)
      jc_field_info_bitsize : int option;
        (* Size of the field in bits, optional *)
    }

type region = 
    {
      mutable jc_reg_variable : bool;
      mutable jc_reg_bitwise : bool;
      jc_reg_id : int;
      jc_reg_name : string;
      jc_reg_final_name : string;
      jc_reg_type : jc_type;
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

type label_info =
    { 
      label_info_name : string;
      label_info_final_name : string;
      mutable times_used : int;
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

(*
Local Variables: 
compile-command: "unset LANG ; make -C .. byte"
End: 
*)
