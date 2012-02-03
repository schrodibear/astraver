
function gen_round_error(x:gen_float) : real = 
         abs_real(float_value(x) - exact_value(x))

function gen_relative_error(x:gen_float) : real =
         abs_real(float_value(x) - exact_value(x))
         /exact_value(x)

function gen_total_error(x:gen_float) : real =
         abs_real(float_value(x)-model_value(x))
