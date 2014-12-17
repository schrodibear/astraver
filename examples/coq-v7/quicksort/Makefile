
all: Partition.vo Quicksort.vo partition_valid.vo quicksort_valid.vo

partition_why.v partition_valid.v quicksort_why.v quicksort_valid.v: partition.mlw quicksort.mlw $(WHY)
	$(WHY) $(WHYOPTIONS) partition.mlw quicksort.mlw

include ../Makefile.common



