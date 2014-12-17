
ML=swap.mlw downheap.mlw heapsort.mlw
V=$(ML:.mlw=_why.v) $(ML:.mlw=_valid.v)
VO=$(V:.v=.vo)

all: heap.vo Inftree.vo $(VO)

$(V): $(ML) $(WHY)
	$(WHY) $(WHYOPTIONS) $(ML)

include ../Makefile.common


