
all: Partition.vo Quicksort.vo partition_valid.vo quicksort_valid.vo

include ../Makefile.common

partition_valid.v quicksort_valid.v: partition.mlw quicksort.mlw $(WHY)
	$(WHY) $(WHYOPTIONS) partition.mlw quicksort.mlw

