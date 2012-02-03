parameter add_gen_float : 
f:float_format -> m:mode -> 
x:gen_float -> y:gen_float -> 
{ }
gen_float
{
exact_value(result)=exact_value(x)+exact_value(y) 
and
model_value(result)=model_value(x)+model_value(y)
and
is_nan(x) or is_nan(y) -> is_nan(result)



