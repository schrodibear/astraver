and 
is_finite(x) and is_finite(y) 
and no_overflow(f,m,float_value(x)+float_value(y)) ->
    is_finite(result) and
    float_value(result) = 
    round_float(f,m,float_value(x)+float_value(y))
    and sign_zero_result(m,result)
and 
is_finite(x) and is_finite(y) 
and not no_overflow(f,m,float_value(x)+float_value(y)) 
-> same_sign_real(result,float_value(x)+float_value(y)) 
   and overflow_value(f,m,result)
  }
