parameter lt_gen_float :
x:gen_float -> y:gen_float -> 
{ }
bool
{ 
is_nan(x) or is_nan(y) -> result = false
and
is_finite(x) and is_infinite(y) -> 
  if result then float_sign(y) = Positive
  else float_sign(y) = Negative
and 
is_infinite(x) and is_finite(y) -> 
  if result then float_sign(x) = Negative
  else float_sign(x) = Positive
