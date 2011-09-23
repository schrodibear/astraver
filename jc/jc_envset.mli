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



module type OrderedType =
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module type OrderedHashedType =
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
end

open Jc_env
open Jc_stdlib

module StringSet : Set.S with type elt = string

module StringMap : Map.S with type key = string 

val get_unique_name : ?local_names:StringSet.t -> string -> string

val is_pointer_type : Jc_env.jc_type -> bool
val is_nonnull_pointer_type : Jc_env.jc_type -> bool
val is_integral_type: jc_type -> bool

val is_embedded_field : Jc_env.field_info -> bool

module VarOrd : OrderedHashedType with type t = var_info

module VarSet : Set.S with type elt = var_info

module VarMap : Map.S with type key = var_info

module StructSet : Set.S with type elt = struct_info

module StructMap : Map.S with type key = struct_info

module VariantSet : Set.S with type elt = root_info

module VariantMap : Map.S with type key = root_info

module ExceptionSet : Set.S with type elt = exception_info

module ExceptionMap : Map.S with type key = exception_info

module StructOrd : OrderedHashedType with type t = struct_info

module VariantOrd : OrderedHashedType with type t = root_info

module FieldOrd : OrderedHashedType with type t = field_info

module FieldSet : Set.S with type elt = field_info

module FieldMap : Map.S with type key = field_info

module FieldTable : Hashtbl.S with type key = field_info

module MemClass : OrderedHashedType with type t = mem_class

module MemClassSet : Set.S with type elt = mem_class

module AllocClass : OrderedHashedType with type t = alloc_class

module PointerClass : OrderedHashedType with type t = pointer_class

module LogicLabelSet : Set.S with type elt = label

module TypeVarOrd : OrderedHashedType with type t = type_var_info
module TypeVarMap : Map.S with type key = type_var_info

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)

