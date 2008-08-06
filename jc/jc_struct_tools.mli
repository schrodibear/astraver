(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
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

open Jc_env

(** Convert class or memory to class of allocation. *)
val alloc_class_of_mem_class: mem_class -> alloc_class

(** Convert class or pointer to class of allocation. *)
val alloc_class_of_pointer_class: pointer_class -> alloc_class

(** Convert a class of allocation into the corresponding variant. *)
val variant_of_alloc_class: alloc_class -> variant_info

(** Return whether a field is embedded or not. *)
val embedded_field: field_info -> bool

(** Return the bit offset of a field. *)
val field_offset: field_info -> int

(** Return the byte offset of a field, if any. *)
val field_offset_in_bytes: field_info -> int option

(** Return the size in bytes of a structure. *)
val struct_size_in_bytes: struct_info -> int

(** Return all the fields of a structure or a variant.
A variant has no field.
A structure has its fields and the fields of its ancestors. *)
val all_fields: pointer_class -> field_info list

(** Selects fully allocated fields. *)
val fully_allocated: field_info -> bool

(** Return all the memories used by a structure, i.e.: its fields,
the fields of its ancestors, and recursively the fields of its fields.
The "select" argument can be used to ignore specific fields. *)
val all_memories: ?select:(field_info -> bool) -> pointer_class ->
  field_info list

(** Return all the variants used by a structure, i.e.: the type of all
pointers returned by all_memories. *)
val all_types: ?select:(field_info -> bool) -> pointer_class ->
  variant_info list

(** Return all the classes of allocation used by a structure *)
val all_allocs: 
  ?select:(field_info -> bool) -> pointer_class -> alloc_class list

(** Return all the variant info used by a structure *)
val all_tags: 
  ?select:(field_info -> bool) -> pointer_class -> variant_info list


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
