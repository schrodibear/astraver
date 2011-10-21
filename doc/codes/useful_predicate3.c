predicate 
overflow_value(f:float_format,m:mode,x:gen_float)= 
m = down -> 
   float_sign(x) = Negative -> is_infinite(x)
   and
   float_sign(x) = Positive -> is_finite(x) and
                   float_value(x) = max_gen_float(f) 
and
m = up -> 
   float_sign(x) = Negative -> is_finite(x) and 
                   float_value(x) = - max_gen_float(f) 
   and
   float_sign(x) = Positive -> is_infinite(x)  


