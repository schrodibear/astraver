parameter gen_float_of_real :
f:float_format -> m:mode -> x:real ->
{ }
gen_float
{ 
no_overflow(f,m,x) -> is_finite(result) and 
           float_value(result) = round_float(f,m,x)
           and sign_zero_result(m,result)
and 
not no_overflow(f,m,x) -> same_sign_real(result,x) 
           and overflow_value(f,m,result)
and 
exact_value(result) = x and
model_value(result) = x
}
