
all:  Jessie_pointer.vo Jessie_zwf.vo Jessie_alloc_table.vo Jessie_memory.vo Jessie_pset.vo Jessie_pset_range.vo Jessie_pset_range_left.vo Jessie_pset_range_right.vo Jessie_pset_deref.vo Jessie_pset_union.vo Jessie_pset_all.vo Jessie_pset_disjoint.vo Jessie_pset_included.vo Jessie_assigns.vo Jessie_assigns_strong.vo Jessie_tag_id.vo Jessie_charp_tag_id.vo Jessie_tag.vo Jessie_tag_table.vo Jessie_cast.vo Jessie_reinterpret.vo Jessie_reinterpret_cast.vo Jessie_allocable.vo Jessie_alloc.vo Jessie_same_except.vo Jessie_rmem.vo Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum_intf2.vo Bit_enum.vo Int8.vo Uint8.vo Int16.vo Uint16.vo Int32.vo Uint32.vo Int64.vo Uint64.vo Bit_int8.vo Bit_uint8.vo Bit_int16.vo Bit_uint16.vo Bit_int32.vo Bit_uint32.vo Bit_int64.vo Bit_uint64.vo Bit_uint8_of_bit_int8.vo Bit_int16_of_bit_int8.vo Bit_uint16_of_bit_int8.vo Bit_int32_of_bit_int8.vo Bit_uint32_of_bit_int8.vo Bit_int64_of_bit_int8.vo Bit_uint64_of_bit_int8.vo Bit_int8_of_bit_uint8.vo Bit_int16_of_bit_uint8.vo Bit_uint16_of_bit_uint8.vo Bit_int32_of_bit_uint8.vo Bit_uint32_of_bit_uint8.vo Bit_int64_of_bit_uint8.vo Bit_uint64_of_bit_uint8.vo Bit_int8_of_bit_int16.vo Bit_uint8_of_bit_int16.vo Bit_uint16_of_bit_int16.vo Bit_int32_of_bit_int16.vo Bit_uint32_of_bit_int16.vo Bit_int64_of_bit_int16.vo Bit_uint64_of_bit_int16.vo Bit_int8_of_bit_uint16.vo Bit_uint8_of_bit_uint16.vo Bit_int16_of_bit_uint16.vo Bit_int32_of_bit_uint16.vo Bit_uint32_of_bit_uint16.vo Bit_int64_of_bit_uint16.vo Bit_uint64_of_bit_uint16.vo Bit_int8_of_bit_int32.vo Bit_uint8_of_bit_int32.vo Bit_int16_of_bit_int32.vo Bit_uint16_of_bit_int32.vo Bit_uint32_of_bit_int32.vo Bit_int64_of_bit_int32.vo Bit_uint64_of_bit_int32.vo Bit_int8_of_bit_uint32.vo Bit_uint8_of_bit_uint32.vo Bit_int16_of_bit_uint32.vo Bit_uint16_of_bit_uint32.vo Bit_int32_of_bit_uint32.vo Bit_int64_of_bit_uint32.vo Bit_uint64_of_bit_uint32.vo Bit_int8_of_bit_int64.vo Bit_uint8_of_bit_int64.vo Bit_int16_of_bit_int64.vo Bit_uint16_of_bit_int64.vo Bit_int32_of_bit_int64.vo Bit_uint32_of_bit_int64.vo Bit_uint64_of_bit_int64.vo Bit_int8_of_bit_uint64.vo Bit_uint8_of_bit_uint64.vo Bit_int16_of_bit_uint64.vo Bit_uint16_of_bit_uint64.vo Bit_int32_of_bit_uint64.vo Bit_uint32_of_bit_uint64.vo Bit_int64_of_bit_uint64.vo

WHY3LIBDIR=$(shell why3 --print-libdir)

Jessie_pointer.vo: Jessie_pointer.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_zwf.vo: Jessie_zwf.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_alloc_table.vo: Jessie_alloc_table.v  Jessie_pointer.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_memory.vo: Jessie_memory.v  Jessie_pointer.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset.vo: Jessie_pset.v  Jessie_pointer.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_range.vo: Jessie_pset_range.v  Jessie_pointer.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_range_left.vo: Jessie_pset_range_left.v  Jessie_pointer.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_range_right.vo: Jessie_pset_range_right.v  Jessie_pointer.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_deref.vo: Jessie_pset_deref.v  Jessie_pointer.vo Jessie_memory.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_union.vo: Jessie_pset_union.v  Jessie_pointer.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_all.vo: Jessie_pset_all.v  Jessie_pointer.vo Jessie_pset.vo Jessie_pset_union.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_disjoint.vo: Jessie_pset_disjoint.v  Jessie_pointer.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_pset_included.vo: Jessie_pset_included.v  Jessie_pointer.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_assigns.vo: Jessie_assigns.v  Jessie_pointer.vo Jessie_alloc_table.vo Jessie_memory.vo Jessie_pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_assigns_strong.vo: Jessie_assigns_strong.v  Jessie_pointer.vo Jessie_alloc_table.vo Jessie_memory.vo Jessie_pset.vo Jessie_assigns.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_tag_id.vo: Jessie_tag_id.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_charp_tag_id.vo: Jessie_charp_tag_id.v  Jessie_tag_id.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_tag.vo: Jessie_tag.v  Jessie_tag_id.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_tag_table.vo: Jessie_tag_table.v  Jessie_pointer.vo Jessie_tag_id.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_cast.vo: Jessie_cast.v  Jessie_pointer.vo Jessie_tag_id.vo Jessie_tag.vo Jessie_tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_reinterpret.vo: Jessie_reinterpret.v  Jessie_pointer.vo Jessie_tag_id.vo Jessie_tag.vo Jessie_tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_reinterpret_cast.vo: Jessie_reinterpret_cast.v  Jessie_pointer.vo Jessie_alloc_table.vo Jessie_tag_id.vo Jessie_tag.vo Jessie_tag_table.vo Jessie_cast.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_allocable.vo: Jessie_allocable.v  Jessie_pointer.vo Jessie_alloc_table.vo Jessie_tag_id.vo Jessie_tag.vo Jessie_tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_alloc.vo: Jessie_alloc.v  Jessie_pointer.vo Jessie_alloc_table.vo Jessie_pset.vo Jessie_tag_id.vo Jessie_tag.vo Jessie_tag_table.vo Jessie_allocable.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_same_except.vo: Jessie_same_except.v  Jessie_pointer.vo Jessie_alloc_table.vo Jessie_pset.vo Jessie_tag_id.vo Jessie_tag.vo Jessie_tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Jessie_rmem.vo: Jessie_rmem.v  Jessie_pointer.vo Jessie_alloc_table.vo Jessie_memory.vo Jessie_pset.vo Jessie_pset_range.vo Jessie_pset_union.vo Jessie_assigns.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Enum_intf.vo: Enum_intf.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Enum.vo: Enum.v  Enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Powers_of_2.vo: Powers_of_2.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_enum_intf.vo: Bit_enum_intf.v  Enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_enum_intf2.vo: Bit_enum_intf2.v  Enum_intf.vo Bit_enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_enum.vo: Bit_enum.v  Enum_intf.vo Powers_of_2.vo Bit_enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Int8.vo: Int8.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Uint8.vo: Uint8.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Int16.vo: Int16.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Uint16.vo: Uint16.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Int32.vo: Int32.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Uint32.vo: Uint32.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Int64.vo: Int64.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Uint64.vo: Uint64.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8.vo: Bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8.vo: Bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16.vo: Bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16.vo: Bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32.vo: Bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32.vo: Bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64.vo: Bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64.vo: Bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8_of_bit_int8.vo: Bit_uint8_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_int8.vo Bit_uint8.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16_of_bit_int8.vo: Bit_int16_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16_of_bit_int8.vo: Bit_uint16_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_int8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32_of_bit_int8.vo: Bit_int32_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32_of_bit_int8.vo: Bit_uint32_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_int8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64_of_bit_int8.vo: Bit_int64_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64_of_bit_int8.vo: Bit_uint64_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8_of_bit_uint8.vo: Bit_int8_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_int8.vo Bit_uint8.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16_of_bit_uint8.vo: Bit_int16_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_uint8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16_of_bit_uint8.vo: Bit_uint16_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint16.vo Bit_uint8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32_of_bit_uint8.vo: Bit_int32_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_uint8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32_of_bit_uint8.vo: Bit_uint32_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint32.vo Bit_uint8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64_of_bit_uint8.vo: Bit_int64_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_uint8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64_of_bit_uint8.vo: Bit_uint64_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint64.vo Bit_uint8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8_of_bit_int16.vo: Bit_int8_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8_of_bit_int16.vo: Bit_uint8_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_uint8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16_of_bit_int16.vo: Bit_uint16_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_int16.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32_of_bit_int16.vo: Bit_int32_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32_of_bit_int16.vo: Bit_uint32_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_int16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64_of_bit_int16.vo: Bit_int64_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64_of_bit_int16.vo: Bit_uint64_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8_of_bit_uint16.vo: Bit_int8_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_int8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8_of_bit_uint16.vo: Bit_uint8_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint16.vo Bit_uint8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16_of_bit_uint16.vo: Bit_int16_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_int16.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32_of_bit_uint16.vo: Bit_int32_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_uint16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32_of_bit_uint16.vo: Bit_uint32_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint32.vo Bit_uint16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64_of_bit_uint16.vo: Bit_int64_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_uint16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64_of_bit_uint16.vo: Bit_uint64_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint64.vo Bit_uint16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8_of_bit_int32.vo: Bit_int8_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8_of_bit_int32.vo: Bit_uint8_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_uint8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16_of_bit_int32.vo: Bit_int16_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16_of_bit_int32.vo: Bit_uint16_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_uint16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32_of_bit_int32.vo: Bit_uint32_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_int32.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64_of_bit_int32.vo: Bit_int64_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64_of_bit_int32.vo: Bit_uint64_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8_of_bit_uint32.vo: Bit_int8_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_int8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8_of_bit_uint32.vo: Bit_uint8_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint32.vo Bit_uint8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16_of_bit_uint32.vo: Bit_int16_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_int16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16_of_bit_uint32.vo: Bit_uint16_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint32.vo Bit_uint16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32_of_bit_uint32.vo: Bit_int32_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_int32.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64_of_bit_uint32.vo: Bit_int64_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_uint32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64_of_bit_uint32.vo: Bit_uint64_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Uint64.vo Bit_uint32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8_of_bit_int64.vo: Bit_int8_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8_of_bit_int64.vo: Bit_uint8_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Bit_uint8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16_of_bit_int64.vo: Bit_int16_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16_of_bit_int64.vo: Bit_uint16_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Bit_uint16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32_of_bit_int64.vo: Bit_int32_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Bit_int32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32_of_bit_int64.vo: Bit_uint32_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Bit_uint32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint64_of_bit_int64.vo: Bit_uint64_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int64.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int8_of_bit_uint64.vo: Bit_int8_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint8_of_bit_uint64.vo: Bit_uint8_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint64.vo Bit_uint8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int16_of_bit_uint64.vo: Bit_int16_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint16_of_bit_uint64.vo: Bit_uint16_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint64.vo Bit_uint16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int32_of_bit_uint64.vo: Bit_int32_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_uint32_of_bit_uint64.vo: Bit_uint32_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Uint64.vo Bit_uint32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

Bit_int64_of_bit_uint64.vo: Bit_int64_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo Bit_int64.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Jessie $<

