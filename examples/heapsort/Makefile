
ML=swap.mlw downheap.mlw heapsort.mlw
WH=$(ML:.mlw=_why.v)
VO=$(ML:.mlw=_why.vo)

all: heap.vo Inftree.vo $(VO)

include ../Makefile.common

$(WH): $(ML) $(WHY)
	$(WHY) $(WHYOPTIONS) $(ML)

