and
is_finite(x) and is_infinite(y) -> 
   is_infinite(result) and same_sign(result,y)
and                    
is_infinite(x) and is_finite(y) ->
   is_infinite(result) and same_sign(result,x)
and
is_infinite(x) and is_infinite(y) 
               and same_sign(x,y) ->
   is_infinite(result) and same_sign(result,x)
and
is_infinite(x) and is_infinite(y) 
               and diff_sign(x,y) -> is_nan(result)


