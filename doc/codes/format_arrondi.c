// 3 formats possibles
type float_format = Single | Double | Quad

// 5 modes d'arrondi (norme IEEE-754)
type mode = nearest_even | to_zero 
            | up | down | nearest_away

// arrondi avec exposant non borné
round_float : float_format, mode, real -> real

// test de non-débordement 
max_gen_float : float_format -> real
predicate 
   no_overflow(f:float_format,m:mode,x:real) = 
   abs_real(round_float(f,m,x)) <= max_gen_float(f)
