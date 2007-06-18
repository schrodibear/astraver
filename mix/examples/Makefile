
CFG=dot -Tps cfg.dot | gv -

%: %.mix
	../../bin/demixify.opt -show-graph -gwhy -entry init $^ || $(CFG)

