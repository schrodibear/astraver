
all:
	unset LANG; make -C .. bin/demixify.opt
	../bin/demixify.opt test.mix -entry init -show-graph
	dot -Tps cfg.dot | gv -
	gwhy -lib-file mix.why test.why

compile:
	unset LANG; make -C .. bin/demixify.opt
