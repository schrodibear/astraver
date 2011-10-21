// fonction signe
logic float_sign : gen_float -> sign

predicate same_sign_real_bool (s:sign,x:real) =
          (x < 0.0 <-> s = Negative) and 
          (x > 0.0 <-> s = Positive)

predicate same_sign_real (x:gen_float,y:real) =
          same_sign_real_bool(float_sign(x),y)

predicate same_sign(x:gen_float,y:gen_float) = 
          float_sign(x) = float_sign(y)

predicate diff_sign(x:gen_float,y:gen_float) = 
          float_sign(x) <> float_sign(y)
