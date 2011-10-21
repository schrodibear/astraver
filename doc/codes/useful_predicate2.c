// infinis signés : +/- infini 
predicate is_minus_infinity(x:gen_float) = 
   is_infinite(x) and float_sign(x) = Negative
predicate is_plus_infinity(x:gen_float) = 
   is_infinite(x) and float_sign(x) = Positive

// zéros signés : -0 et +0
predicate is_gen_zero(x:gen_float) = 
   is_finite(x) and float_value(x) = 0.0

predicate is_gen_zero_plus(x:gen_float) = 
   is_gen_zero(x) and float_sign(x) = Positive

predicate is_gen_zero_minus(x:gen_float) = 
   is_gen_zero(x) and float_sign(x) = Negative
