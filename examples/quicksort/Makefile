
all: Partition.vo Quicksort.vo partition_why.vo quicksort_why.vo

include ../Makefile.common

partition_why.v quicksort_why.v: partition.mlw quicksort.mlw $(WHY)
	$(WHY) $(WHYOPTIONS) partition.mlw quicksort.mlw

