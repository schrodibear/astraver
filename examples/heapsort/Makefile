
ML=swap.mlw downheap.mlw heapsort.mlw
WH=$(ML:.mlw=_valid.v)
VO=$(ML:.mlw=_valid.vo)

all: heap.vo Inftree.vo $(VO)

include ../Makefile.common

$(WH): $(ML) $(WHY)
	$(WHY) $(WHYOPTIONS) $(ML)

