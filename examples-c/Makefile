
DIRS = tutorial sorting linked-lists

all: 
	for d in $(DIRS); do \
		if make -C $$d coq; then \
			echo "Coq proofs OK in $$d" ; \
		else \
			echo "Coq proofs FAILED in $$d" ; \
			exit 1 ;\
		fi ; \
	done

clean:
	for d in $(DIRS); do make -C $$d clean; done
