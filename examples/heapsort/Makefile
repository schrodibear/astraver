
all: Partition.vo Quicksort.vo partition_why.vo quicksort_why.vo

include ../Makefile.common

ML=swap.ml downheap.ml heapsort.ml 
WH=$(ML:.ml=_why.v)

$(WH): $(ML) $(WHY)
	$(WHY) $(ML)

