parameter gen_float_of_real :
f:float_format -> m:mode -> x:real ->
{ no_overflow(f,m,x) 
}
gen_float
{ 
float_value(result) = round_float(f,m,x)
and 
exact_value(result) = x 
and
model_value(result) = x
}
