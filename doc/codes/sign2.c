
predicate sign_zero_result(m:mode,x:gen_float) = 
      float_value(x) = 0.0 -> 
      (m = down -> float_sign(x) = Negative) 
       and 
      (m <> down -> float_sign(x) = Positive) 

axiom finite_sign : forall x:gen_float.
      is_finite(x) and float_value(x) <> 0.0 -> 
      same_sign_real(x,float_value(x))
