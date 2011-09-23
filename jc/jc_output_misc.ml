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

open Jc_pervasives
open Jc_env
open Jc_ast
open Format
open Pp

let string_of_termination_policy p =
  match p with
    | Jc_env.TPalways -> "always"
    | Jc_env.TPuser -> "user"
    | Jc_env.TPnever -> "never"

let string_of_invariant_policy p =
  match p with
    | InvNone -> "None"
    | InvArguments -> "Arguments"
    | InvOwnership -> "Ownership"

let string_of_separation_policy p =
  match p with
    | SepNone -> "None"
    | SepRegions -> "Regions"

let string_of_annotation_policy p =
  match p with
    | AnnotNone -> "None"
    | AnnotInvariants -> "Invariants"
    | AnnotElimPre -> "ElimPre"
    | AnnotStrongPre -> "StrongPre"
    | AnnotWeakPre -> "WeakPre"
 
let string_of_abstract_domain p =
  match p with
    | AbsNone -> "None"
    | AbsBox -> "Box"
    | AbsOct -> "Oct"
    | AbsPol -> "Pol"

let string_of_int_model p =
  match p with
    | IMbounded -> "bounded"
    | IMmodulo -> "modulo"

let float_suffix fmt = function
  | `Single -> fprintf fmt "f"
  | `Double -> fprintf fmt "d"
  | `Real -> fprintf fmt ""

let const fmt c =
  match c with
    | JCCinteger s -> fprintf fmt "%s" s
    | JCCreal s -> fprintf fmt "%s" s 
    | JCCboolean b -> fprintf fmt "%B" b
    | JCCnull -> fprintf fmt "null"
    | JCCvoid -> fprintf fmt "()"
    | JCCstring s -> fprintf fmt "\"%s\"" s

let label fmt l =
  match l with
    | LabelName s -> fprintf fmt "%s" s.label_info_name
    | LabelHere -> fprintf fmt "Here" 
    | LabelPre -> fprintf fmt "Pre" 
    | LabelOld -> fprintf fmt "Old" 
    | LabelPost -> fprintf fmt "Post" 

let rec ptype fmt t =
  match t#node with
    | JCPTnative n -> fprintf fmt "%s" (string_of_native n)
    | JCPTidentifier (s,args) -> fprintf fmt "%s%a" s (print_list_delim lchevron rchevron comma ptype) args
    | JCPTpointer (name,params,ao, bo) ->
	begin match ao, bo with
	  | None, None ->
	      fprintf fmt "%s%a[..]" name ptype_params params
	  | Some a, None ->
	      fprintf fmt "%s%a[%s..]" name ptype_params params
                (Num.string_of_num a)
	  | None, Some b ->
	      fprintf fmt "%s%a[..%s]" name ptype_params params
                (Num.string_of_num b)
	  | Some a, Some b ->
	      if Num.eq_num a b then
		fprintf fmt "%s%a[%s]" name ptype_params params
                  (Num.string_of_num a)
	      else
		fprintf fmt "%s%a[%s..%s]" name ptype_params params
		  (Num.string_of_num a) (Num.string_of_num b)
	end

and ptype_params fmt l = print_list_delim lchevron rchevron comma ptype fmt l

let offset_kind fmt k =
  match k with
    | Offset_max -> fprintf fmt "ax"
    | Offset_min -> fprintf fmt "in"

and asrt_kind fmt = function
  | Aassert -> fprintf fmt "assert"
  | Ahint -> fprintf fmt "hint"
  | Aassume -> fprintf fmt "assume"
  | Acheck -> fprintf fmt "check"

and address_kind fmt = function
  | Addr_absolute -> fprintf fmt "absolute_"
  | Addr_pointer -> fprintf fmt ""

let alloc_class fmt = function
  | JCalloc_root vi -> fprintf fmt "alloc-root(%s)" vi.jc_root_info_name
  | JCalloc_bitvector -> fprintf fmt "alloc-bitvector"

let memory_class fmt = function
  | JCmem_field fi -> fprintf fmt "mem-field(%s)" fi.jc_field_info_name
  | JCmem_plain_union vi -> 
      fprintf fmt "mem-plain-union(%s)" vi.jc_root_info_name
  | JCmem_bitvector -> fprintf fmt "mem-bitvector"

let pointer_class = function
  | JCtag(st, _) -> "tag "^st.jc_struct_info_name
  | JCroot vi -> "root "^vi.jc_root_info_name

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
