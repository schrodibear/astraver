
predicate is_finite(x:gen_float) = 
          float_class(x) = Finite

predicate is_infinite(x:gen_float) = 
          float_class(x) = Infinite

predicate is_nan(x:gen_float) = 
          float_class(x) = Nan





