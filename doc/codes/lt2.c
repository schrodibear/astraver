and
is_infinite(x) and is_infinite(y) -> 
  if result then 
            float_sign(x) = Negative and 
            float_sign(y) = Positive
  else float_sign(x) = Positive or 
       float_sign(y) = Negative 
and
is_finite(x) and is_finite(y) -> 
  if result then 
            float_value(x) < float_value(y)
  else float_value(x) >= float_value(y)
