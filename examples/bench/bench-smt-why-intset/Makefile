
all:
	rm -rf why smt
	why --dir why --multi-why -split-user-conj IntSet.why
	mkdir -p smt
	for f in why/*_po*.why; do \
	  echo $$f; \
	  why --no-prelude why/*_ctx.why $$f --smtlib --encoding sstrat --dir smt; \
	done
