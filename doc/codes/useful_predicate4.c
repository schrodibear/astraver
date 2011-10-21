
and 
m = to_zero -> is_finite(x) and 
    float_sign(x) = Negative ->
          float_value(x) = - max_gen_float(f) 
    and 
    float_sign(x) = Positive ->
          float_value(x) = max_gen_float(f)  
and 
m = nearest_away or m = nearest_even -> 
    is_infinite(x) 
