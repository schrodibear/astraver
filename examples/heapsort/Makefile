
ML=swap.ml downheap.ml heapsort.ml 
WH=$(ML:.ml=_why.v)
VO=$(ML:.ml=_why.vo)

all: Heap.vo Inftree.vo $(VO)

include ../Makefile.common

$(WH): $(ML) $(WHY)
	$(WHY) $(WHYOPTIONS) $(ML)

