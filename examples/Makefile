
DIRS = misc binary-search bresenham quicksort edit-distance heapsort sqrt kmp

all: 
	for d in $(DIRS); do make -C $$d; done

clean::
	rm -f */*~ */*.vo

depend::
	for d in $(DIRS); do make -C $$d depend; done
