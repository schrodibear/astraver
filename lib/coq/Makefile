
all:  Pointer.vo Zwf.vo Alloc_table.vo Memory.vo Pset.vo Pset_range.vo Pset_range_left.vo Pset_range_right.vo Pset_deref.vo Pset_union.vo Pset_all.vo Pset_disjoint.vo Pset_included.vo Assigns.vo Assigns_strong.vo Tag_id.vo Tag.vo Tag_table_type.vo Voidp.vo Voidp_tag_id.vo Tag_table.vo Charp_tag_id.vo Sidecast.vo Reinterpret.vo Reinterpret_cast.vo Allocable.vo Alloc.vo Same_except.vo Rmem.vo Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum_intf2.vo Bit_enum.vo Int8.vo Uint8.vo Int16.vo Uint16.vo Int32.vo Uint32.vo Int64.vo Uint64.vo Bit_int8.vo Bit_uint8.vo Bit_int16.vo Bit_uint16.vo Bit_int32.vo Bit_uint32.vo Bit_int64.vo Bit_uint64.vo Bit_uint8_of_bit_int8.vo Bit_int16_of_bit_int8.vo Bit_uint16_of_bit_int8.vo Bit_int32_of_bit_int8.vo Bit_uint32_of_bit_int8.vo Bit_int64_of_bit_int8.vo Bit_uint64_of_bit_int8.vo Bit_int8_of_bit_uint8.vo Bit_int16_of_bit_uint8.vo Bit_uint16_of_bit_uint8.vo Bit_int32_of_bit_uint8.vo Bit_uint32_of_bit_uint8.vo Bit_int64_of_bit_uint8.vo Bit_uint64_of_bit_uint8.vo Bit_int8_of_bit_int16.vo Bit_uint8_of_bit_int16.vo Bit_uint16_of_bit_int16.vo Bit_int32_of_bit_int16.vo Bit_uint32_of_bit_int16.vo Bit_int64_of_bit_int16.vo Bit_uint64_of_bit_int16.vo Bit_int8_of_bit_uint16.vo Bit_uint8_of_bit_uint16.vo Bit_int16_of_bit_uint16.vo Bit_int32_of_bit_uint16.vo Bit_uint32_of_bit_uint16.vo Bit_int64_of_bit_uint16.vo Bit_uint64_of_bit_uint16.vo Bit_int8_of_bit_int32.vo Bit_uint8_of_bit_int32.vo Bit_int16_of_bit_int32.vo Bit_uint16_of_bit_int32.vo Bit_uint32_of_bit_int32.vo Bit_int64_of_bit_int32.vo Bit_uint64_of_bit_int32.vo Bit_int8_of_bit_uint32.vo Bit_uint8_of_bit_uint32.vo Bit_int16_of_bit_uint32.vo Bit_uint16_of_bit_uint32.vo Bit_int32_of_bit_uint32.vo Bit_int64_of_bit_uint32.vo Bit_uint64_of_bit_uint32.vo Bit_int8_of_bit_int64.vo Bit_uint8_of_bit_int64.vo Bit_int16_of_bit_int64.vo Bit_uint16_of_bit_int64.vo Bit_int32_of_bit_int64.vo Bit_uint32_of_bit_int64.vo Bit_uint64_of_bit_int64.vo Bit_int8_of_bit_uint64.vo Bit_uint8_of_bit_uint64.vo Bit_int16_of_bit_uint64.vo Bit_uint16_of_bit_uint64.vo Bit_int32_of_bit_uint64.vo Bit_uint32_of_bit_uint64.vo Bit_int64_of_bit_uint64.vo

WHY3LIBDIR=$(shell why3 --print-libdir)

Pointer.vo: Pointer.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Zwf.vo: Zwf.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Alloc_table.vo: Alloc_table.v  Pointer.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Memory.vo: Memory.v  Pointer.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset.vo: Pset.v  Pointer.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_range.vo: Pset_range.v  Pointer.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_range_left.vo: Pset_range_left.v  Pointer.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_range_right.vo: Pset_range_right.v  Pointer.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_deref.vo: Pset_deref.v  Pointer.vo Memory.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_union.vo: Pset_union.v  Pointer.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_all.vo: Pset_all.v  Pointer.vo Pset.vo Pset_union.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_disjoint.vo: Pset_disjoint.v  Pointer.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Pset_included.vo: Pset_included.v  Pointer.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Assigns.vo: Assigns.v  Pointer.vo Alloc_table.vo Memory.vo Pset.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Assigns_strong.vo: Assigns_strong.v  Pointer.vo Alloc_table.vo Memory.vo Pset.vo Assigns.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Tag_id.vo: Tag_id.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Tag.vo: Tag.v  Tag_id.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Tag_table_type.vo: Tag_table_type.v  Pointer.vo Tag_id.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Voidp.vo: Voidp.v  Pointer.vo Tag_id.vo Tag_table_type.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Voidp_tag_id.vo: Voidp_tag_id.v  Pointer.vo Tag_id.vo Tag.vo Tag_table_type.vo Voidp.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Tag_table.vo: Tag_table.v  Pointer.vo Tag_id.vo Tag.vo Tag_table_type.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Charp_tag_id.vo: Charp_tag_id.v  Pointer.vo Tag_id.vo Tag.vo Tag_table_type.vo Voidp.vo Voidp_tag_id.vo Tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Sidecast.vo: Sidecast.v  Pointer.vo Tag_id.vo Tag.vo Tag_table_type.vo Tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Reinterpret.vo: Reinterpret.v  Pointer.vo Tag_id.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Reinterpret_cast.vo: Reinterpret_cast.v  Pointer.vo Alloc_table.vo Tag_id.vo Tag.vo Tag_table_type.vo Tag_table.vo Sidecast.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Allocable.vo: Allocable.v  Pointer.vo Alloc_table.vo Tag_id.vo Tag.vo Tag_table_type.vo Tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Alloc.vo: Alloc.v  Pointer.vo Alloc_table.vo Pset.vo Tag_id.vo Tag.vo Tag_table_type.vo Tag_table.vo Allocable.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Same_except.vo: Same_except.v  Pointer.vo Alloc_table.vo Pset.vo Tag_id.vo Tag.vo Tag_table_type.vo Tag_table.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Rmem.vo: Rmem.v  Pointer.vo Alloc_table.vo Memory.vo Pset.vo Pset_range.vo Pset_union.vo Assigns.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Enum_intf.vo: Enum_intf.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Enum.vo: Enum.v  Enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Powers_of_2.vo: Powers_of_2.v 
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_enum_intf.vo: Bit_enum_intf.v  Enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_enum_intf2.vo: Bit_enum_intf2.v  Enum_intf.vo Bit_enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_enum.vo: Bit_enum.v  Enum_intf.vo Powers_of_2.vo Bit_enum_intf.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Int8.vo: Int8.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Uint8.vo: Uint8.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Int16.vo: Int16.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Uint16.vo: Uint16.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Int32.vo: Int32.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Uint32.vo: Uint32.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Int64.vo: Int64.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Uint64.vo: Uint64.v  Enum_intf.vo Enum.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8.vo: Bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8.vo: Bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16.vo: Bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16.vo: Bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32.vo: Bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32.vo: Bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64.vo: Bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64.vo: Bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8_of_bit_int8.vo: Bit_uint8_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint8.vo Bit_int8.vo Bit_uint8.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16_of_bit_int8.vo: Bit_int16_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Int16.vo Bit_int8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16_of_bit_int8.vo: Bit_uint16_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint16.vo Bit_int8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32_of_bit_int8.vo: Bit_int32_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Int32.vo Bit_int8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32_of_bit_int8.vo: Bit_uint32_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint32.vo Bit_int8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64_of_bit_int8.vo: Bit_int64_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Int64.vo Bit_int8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64_of_bit_int8.vo: Bit_uint64_of_bit_int8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint64.vo Bit_int8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8_of_bit_uint8.vo: Bit_int8_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint8.vo Bit_int8.vo Bit_uint8.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16_of_bit_uint8.vo: Bit_int16_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Int16.vo Bit_uint8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16_of_bit_uint8.vo: Bit_uint16_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint16.vo Bit_uint8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32_of_bit_uint8.vo: Bit_int32_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Int32.vo Bit_uint8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32_of_bit_uint8.vo: Bit_uint32_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint32.vo Bit_uint8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64_of_bit_uint8.vo: Bit_int64_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Int64.vo Bit_uint8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64_of_bit_uint8.vo: Bit_uint64_of_bit_uint8.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint64.vo Bit_uint8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8_of_bit_int16.vo: Bit_int8_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Int16.vo Bit_int8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8_of_bit_int16.vo: Bit_uint8_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Int16.vo Bit_uint8.vo Bit_int16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16_of_bit_int16.vo: Bit_uint16_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Uint16.vo Bit_int16.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32_of_bit_int16.vo: Bit_int32_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Int32.vo Bit_int16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32_of_bit_int16.vo: Bit_uint32_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Uint32.vo Bit_int16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64_of_bit_int16.vo: Bit_int64_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Int64.vo Bit_int16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64_of_bit_int16.vo: Bit_uint64_of_bit_int16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Uint64.vo Bit_int16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8_of_bit_uint16.vo: Bit_int8_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint16.vo Bit_int8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8_of_bit_uint16.vo: Bit_uint8_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint16.vo Bit_uint8.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16_of_bit_uint16.vo: Bit_int16_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Uint16.vo Bit_int16.vo Bit_uint16.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32_of_bit_uint16.vo: Bit_int32_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Int32.vo Bit_uint16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32_of_bit_uint16.vo: Bit_uint32_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint32.vo Bit_uint16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64_of_bit_uint16.vo: Bit_int64_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Int64.vo Bit_uint16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64_of_bit_uint16.vo: Bit_uint64_of_bit_uint16.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint64.vo Bit_uint16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8_of_bit_int32.vo: Bit_int8_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Int32.vo Bit_int8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8_of_bit_int32.vo: Bit_uint8_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Int32.vo Bit_uint8.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16_of_bit_int32.vo: Bit_int16_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Int32.vo Bit_int16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16_of_bit_int32.vo: Bit_uint16_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Int32.vo Bit_uint16.vo Bit_int32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32_of_bit_int32.vo: Bit_uint32_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int32.vo Uint32.vo Bit_int32.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64_of_bit_int32.vo: Bit_int64_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int32.vo Int64.vo Bit_int32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64_of_bit_int32.vo: Bit_uint64_of_bit_int32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int32.vo Uint64.vo Bit_int32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8_of_bit_uint32.vo: Bit_int8_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint32.vo Bit_int8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8_of_bit_uint32.vo: Bit_uint8_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint32.vo Bit_uint8.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16_of_bit_uint32.vo: Bit_int16_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Uint32.vo Bit_int16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16_of_bit_uint32.vo: Bit_uint16_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint32.vo Bit_uint16.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32_of_bit_uint32.vo: Bit_int32_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int32.vo Uint32.vo Bit_int32.vo Bit_uint32.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64_of_bit_uint32.vo: Bit_int64_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Int64.vo Bit_uint32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64_of_bit_uint32.vo: Bit_uint64_of_bit_uint32.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Uint64.vo Bit_uint32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8_of_bit_int64.vo: Bit_int8_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Int64.vo Bit_int8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8_of_bit_int64.vo: Bit_uint8_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Int64.vo Bit_uint8.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16_of_bit_int64.vo: Bit_int16_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Int64.vo Bit_int16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16_of_bit_int64.vo: Bit_uint16_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Int64.vo Bit_uint16.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32_of_bit_int64.vo: Bit_int32_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int32.vo Int64.vo Bit_int32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32_of_bit_int64.vo: Bit_uint32_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Int64.vo Bit_uint32.vo Bit_int64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint64_of_bit_int64.vo: Bit_uint64_of_bit_int64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int64.vo Uint64.vo Bit_int64.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int8_of_bit_uint64.vo: Bit_int8_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int8.vo Uint64.vo Bit_int8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint8_of_bit_uint64.vo: Bit_uint8_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint8.vo Uint64.vo Bit_uint8.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int16_of_bit_uint64.vo: Bit_int16_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int16.vo Uint64.vo Bit_int16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint16_of_bit_uint64.vo: Bit_uint16_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint16.vo Uint64.vo Bit_uint16.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int32_of_bit_uint64.vo: Bit_int32_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int32.vo Uint64.vo Bit_int32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_uint32_of_bit_uint64.vo: Bit_uint32_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Uint32.vo Uint64.vo Bit_uint32.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

Bit_int64_of_bit_uint64.vo: Bit_int64_of_bit_uint64.v  Enum_intf.vo Enum.vo Powers_of_2.vo Bit_enum_intf.vo Bit_enum.vo Int64.vo Uint64.vo Bit_int64.vo Bit_uint64.vo
	coqc -R $(WHY3LIBDIR)/coq Why3 -R . Astraver $<

