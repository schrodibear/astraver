parameter div_gen_float : 
f:float_format -> m:mode -> 
x:gen_float -> y:gen_float -> 
{ float_value(y) <> 0.0 
  and 
  no_overflow(f,m,float_value(x)/float_value(y)) }
gen_float
{float_value(result) = 
      round_float(f,m,float_value(x)/float_value(y))
 and 
 exact_value(result) = exact_value(x)/exact_value(y)
 and 
 model_value(result) = model_value(x)/model_value(y)
}
