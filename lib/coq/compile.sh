#!/bin/bash

if [ ! -f ${1}o ]; then
  WHY3LIBDIR=$(why3 --print-libdir)
  declare -A PID

  for p in ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pointer.v&
  PID["Jessie_pointer"]=$!
  for p in ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_zwf.v&
  PID["Jessie_zwf"]=$!
  for p in Jessie_pointer ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_alloc_table.v&
  PID["Jessie_alloc_table"]=$!
  for p in Jessie_pointer ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_memory.v&
  PID["Jessie_memory"]=$!
  for p in Jessie_pointer ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset.v&
  PID["Jessie_pset"]=$!
  for p in Jessie_pointer Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_range.v&
  PID["Jessie_pset_range"]=$!
  for p in Jessie_pointer Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_range_left.v&
  PID["Jessie_pset_range_left"]=$!
  for p in Jessie_pointer Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_range_right.v&
  PID["Jessie_pset_range_right"]=$!
  for p in Jessie_pointer Jessie_memory Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_deref.v&
  PID["Jessie_pset_deref"]=$!
  for p in Jessie_pointer Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_union.v&
  PID["Jessie_pset_union"]=$!
  for p in Jessie_pointer Jessie_pset Jessie_pset_union ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_all.v&
  PID["Jessie_pset_all"]=$!
  for p in Jessie_pointer Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_disjoint.v&
  PID["Jessie_pset_disjoint"]=$!
  for p in Jessie_pointer Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_included.v&
  PID["Jessie_pset_included"]=$!
  for p in Jessie_pointer Jessie_alloc_table Jessie_memory Jessie_pset ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_assigns.v&
  PID["Jessie_assigns"]=$!
  for p in Jessie_pointer Jessie_alloc_table Jessie_memory Jessie_pset Jessie_assigns ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_assigns_strong.v&
  PID["Jessie_assigns_strong"]=$!
  for p in ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag_id.v&
  PID["Jessie_tag_id"]=$!
  for p in Jessie_tag_id ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag.v&
  PID["Jessie_tag"]=$!
  for p in Jessie_pointer Jessie_tag_id ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag_table_type.v&
  PID["Jessie_tag_table_type"]=$!
  for p in Jessie_pointer Jessie_tag_id Jessie_tag Jessie_tag_table_type ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag_table.v&
  PID["Jessie_tag_table"]=$!
  for p in Jessie_pointer Jessie_tag_id Jessie_tag Jessie_tag_table_type Jessie_tag_table ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_reinterpret.v&
  PID["Jessie_reinterpret"]=$!
  for p in Jessie_pointer Jessie_alloc_table Jessie_tag_id Jessie_tag Jessie_tag_table_type Jessie_tag_table ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_reinterpret_cast.v&
  PID["Jessie_reinterpret_cast"]=$!
  for p in Jessie_pointer Jessie_alloc_table Jessie_tag_id Jessie_tag Jessie_tag_table_type Jessie_tag_table ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_allocable.v&
  PID["Jessie_allocable"]=$!
  for p in Jessie_pointer Jessie_alloc_table Jessie_pset Jessie_tag_id Jessie_tag Jessie_tag_table_type Jessie_tag_table Jessie_allocable ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_alloc.v&
  PID["Jessie_alloc"]=$!
  for p in Jessie_pointer Jessie_alloc_table Jessie_pset Jessie_tag_id Jessie_tag Jessie_tag_table_type Jessie_tag_table ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_same_except.v&
  PID["Jessie_same_except"]=$!
  for p in Jessie_pointer Jessie_alloc_table Jessie_memory Jessie_pset Jessie_pset_range Jessie_pset_union Jessie_assigns ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_rmem.v&
  PID["Jessie_rmem"]=$!
  for p in ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Enum_intf.v&
  PID["Enum_intf"]=$!
  for p in Enum_intf ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Enum.v&
  PID["Enum"]=$!
  for p in ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Powers_of_2.v&
  PID["Powers_of_2"]=$!
  for p in Enum_intf ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_enum_intf.v&
  PID["Bit_enum_intf"]=$!
  for p in Enum_intf Bit_enum_intf ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_enum_intf2.v&
  PID["Bit_enum_intf2"]=$!
  for p in Enum_intf Powers_of_2 Bit_enum_intf ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_enum.v&
  PID["Bit_enum"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int8.v&
  PID["Int8"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint8.v&
  PID["Uint8"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int16.v&
  PID["Int16"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint16.v&
  PID["Uint16"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int32.v&
  PID["Int32"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint32.v&
  PID["Uint32"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int64.v&
  PID["Int64"]=$!
  for p in Enum_intf Enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint64.v&
  PID["Uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8.v&
  PID["Bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8.v&
  PID["Bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16.v&
  PID["Bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16.v&
  PID["Bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32.v&
  PID["Bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32.v&
  PID["Bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64.v&
  PID["Bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64.v&
  PID["Bit_uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_int8 Bit_uint8 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int8.v&
  PID["Bit_uint8_of_bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int8 Bit_int16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_int8.v&
  PID["Bit_int16_of_bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_int8 Bit_uint16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int8.v&
  PID["Bit_uint16_of_bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int8 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_int8.v&
  PID["Bit_int32_of_bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_int8 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int8.v&
  PID["Bit_uint32_of_bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int8 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_int8.v&
  PID["Bit_int64_of_bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int8 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int8.v&
  PID["Bit_uint64_of_bit_int8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_int8 Bit_uint8 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint8.v&
  PID["Bit_int8_of_bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_uint8 Bit_int16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint8.v&
  PID["Bit_int16_of_bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Uint16 Bit_uint8 Bit_uint16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_uint8.v&
  PID["Bit_uint16_of_bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_uint8 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint8.v&
  PID["Bit_int32_of_bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Uint32 Bit_uint8 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_uint8.v&
  PID["Bit_uint32_of_bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_uint8 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint8.v&
  PID["Bit_int64_of_bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Uint64 Bit_uint8 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_uint8.v&
  PID["Bit_uint64_of_bit_uint8"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int8 Bit_int16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_int16.v&
  PID["Bit_int8_of_bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_uint8 Bit_int16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int16.v&
  PID["Bit_uint8_of_bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_int16 Bit_uint16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int16.v&
  PID["Bit_uint16_of_bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int16 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_int16.v&
  PID["Bit_int32_of_bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_int16 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int16.v&
  PID["Bit_uint32_of_bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int16 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_int16.v&
  PID["Bit_int64_of_bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int16 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int16.v&
  PID["Bit_uint64_of_bit_int16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_int8 Bit_uint16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint16.v&
  PID["Bit_int8_of_bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Uint16 Bit_uint8 Bit_uint16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_uint16.v&
  PID["Bit_uint8_of_bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_int16 Bit_uint16 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint16.v&
  PID["Bit_int16_of_bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_uint16 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint16.v&
  PID["Bit_int32_of_bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Uint32 Bit_uint16 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_uint16.v&
  PID["Bit_uint32_of_bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_uint16 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint16.v&
  PID["Bit_int64_of_bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Uint64 Bit_uint16 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_uint16.v&
  PID["Bit_uint64_of_bit_uint16"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int8 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_int32.v&
  PID["Bit_int8_of_bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_uint8 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int32.v&
  PID["Bit_uint8_of_bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int16 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_int32.v&
  PID["Bit_int16_of_bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_uint16 Bit_int32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int32.v&
  PID["Bit_uint16_of_bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_int32 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int32.v&
  PID["Bit_uint32_of_bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int32 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_int32.v&
  PID["Bit_int64_of_bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int32 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int32.v&
  PID["Bit_uint64_of_bit_int32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_int8 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint32.v&
  PID["Bit_int8_of_bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Uint32 Bit_uint8 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_uint32.v&
  PID["Bit_uint8_of_bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_int16 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint32.v&
  PID["Bit_int16_of_bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Uint32 Bit_uint16 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_uint32.v&
  PID["Bit_uint16_of_bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_int32 Bit_uint32 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint32.v&
  PID["Bit_int32_of_bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_uint32 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint32.v&
  PID["Bit_int64_of_bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Uint64 Bit_uint32 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_uint32.v&
  PID["Bit_uint64_of_bit_uint32"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int8 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_int64.v&
  PID["Bit_int8_of_bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Bit_uint8 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int64.v&
  PID["Bit_uint8_of_bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int16 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_int64.v&
  PID["Bit_int16_of_bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Bit_uint16 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int64.v&
  PID["Bit_uint16_of_bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Bit_int32 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_int64.v&
  PID["Bit_int32_of_bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Bit_uint32 Bit_int64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int64.v&
  PID["Bit_uint32_of_bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int64 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int64.v&
  PID["Bit_uint64_of_bit_int64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int8 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint64.v&
  PID["Bit_int8_of_bit_uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint8 Uint64 Bit_uint8 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_uint64.v&
  PID["Bit_uint8_of_bit_uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int16 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint64.v&
  PID["Bit_int16_of_bit_uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint16 Uint64 Bit_uint16 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_uint64.v&
  PID["Bit_uint16_of_bit_uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int32 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint64.v&
  PID["Bit_int32_of_bit_uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint32 Uint64 Bit_uint32 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_uint64.v&
  PID["Bit_uint32_of_bit_uint64"]=$!
  for p in Enum_intf Enum Powers_of_2 Bit_enum_intf Bit_enum Uint64 Bit_int64 Bit_uint64 ; do wait ${PID["$p"]}; done 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint64.v&
  PID["Bit_int64_of_bit_uint64"]=$!
  wait
fi
