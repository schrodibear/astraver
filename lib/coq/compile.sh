
#!/bin/bash

if [ ! -f ${1}o ]; then
  WHY3LIBDIR=$(why3 --print-libdir)

  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pointer.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_zwf.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_alloc_table.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_memory.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_range.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_range_left.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_range_right.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_deref.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_union.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_all.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_disjoint.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_pset_included.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_assigns.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_assigns_strong.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag_id.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag_table_type.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_tag_table.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_reinterpret.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_reinterpret_cast.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_allocable.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_alloc.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_same_except.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Jessie_rmem.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Enum_intf.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Enum.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Powers_of_2.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_enum_intf.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_enum_intf2.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_enum.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int8.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint8.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int16.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint16.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int32.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint32.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Int64.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Uint64.v 
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_uint8.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_uint16.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_uint32.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint64_of_bit_int64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int8_of_bit_uint64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint8_of_bit_uint64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int16_of_bit_uint64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint16_of_bit_uint64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int32_of_bit_uint64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_uint32_of_bit_uint64.v &
  coqc -R ${WHY3LIBDIR}/coq Why3 -R lib/coq Jessie lib/coq/Bit_int64_of_bit_uint64.v &
  wait
fi
