
VO=swap0_valid.vo loop0_valid.vo peano_valid.vo power_valid.vo \
     arith_valid.vo mac_carthy_valid.vo fib_valid.vo gcd_valid.vo \
     flag_valid.vo search_valid.vo sqrt_dicho_valid.vo csearch_valid.vo \
     copy_valid.vo max_valid.vo

all: $(VO)

sx: $(VO:_valid.vo=_why.sx)
	for f in $^; do Simplify $$f; done

include ../Makefile.common
