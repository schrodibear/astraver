
# VO=swap0_valid.vo loop0_valid.vo peano_valid.vo power_valid.vo \
#      arith_valid.vo mac_carthy_valid.vo fib_valid.vo gcd_valid.vo \
#      flag_valid.vo search_valid.vo sqrt_dicho_valid.vo \
#      max_valid.vo
VO=swap0_why.vo loop0_why.vo peano_why.vo power_why.vo \
     arith_why.vo mac_carthy_why.vo fib_why.vo gcd_why.vo \
     flag_why.vo search_why.vo sqrt_dicho_why.vo \
     max_why.vo

# csearch_valid.vo copy_valid.vo 

all: $(VO)

sx: $(VO:_why.vo=_why.sx)
	for f in $^; do echo $$f; Simplify $$f; done

cvc: $(VO:_why.vo=_why.cvc)
	for f in $^; do echo $$f; cvcl < $$f; done

include ../Makefile.common
