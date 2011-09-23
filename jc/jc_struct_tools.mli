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

open Jc_env

(** Convert class or memory to class of allocation. *)
val alloc_class_of_mem_class: mem_class -> alloc_class

(** Convert class or pointer to class of allocation. *)
val alloc_class_of_pointer_class: pointer_class -> alloc_class

(** Convert a class of allocation into the corresponding variant. *)
val variant_of_alloc_class: alloc_class -> root_info

val variant_of_mem_class: mem_class -> root_info

(** Return whether a field is embedded or not. *)
val embedded_field: field_info -> bool

(** Return the bit offset of a field. *)
val field_offset: field_info -> int

(** Return the byte offset of a field, if any. *)
val field_offset_in_bytes: field_info -> int option

val field_type_has_bitvector_representation: field_info -> bool

(** Return the size in bytes of a structure. *)
val struct_size_in_bytes: struct_info -> int

(** Return whether the structure has a size. *)
val struct_has_size: struct_info -> bool

(** Return all the fields of a structure or a variant.
A variant has no field.
A structure has its fields and the fields of its ancestors. *)
val all_fields: pointer_class -> field_info list

(** Selects fully allocated fields. *)
val fully_allocated: field_info -> bool

(** Return all the memories used by a structure, i.e.: its fields,
the fields of its ancestors, and recursively the fields of its fields.
The "select" argument can be used to ignore specific fields. *)
val all_memories: 
  ?select:(field_info -> bool) -> pointer_class -> mem_class list

(** Return all the variants used by a structure, i.e.: the type of all
pointers returned by all_memories. *)
val all_types: ?select:(field_info -> bool) -> pointer_class ->
  root_info list

(** Return all the classes of allocation used by a structure *)
val all_allocs: 
  ?select:(field_info -> bool) -> pointer_class -> alloc_class list

(** Return all the variant info used by a structure *)
val all_tags: 
  ?select:(field_info -> bool) -> pointer_class -> root_info list


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
