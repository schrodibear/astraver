
Definition round_float (f : float_format) 
                       (m : mode) (x:R) :=
match f with
| Single => gappa_rounding 
       (rounding_float (round_mode m) 24 149) x
| Double => gappa_rounding 
       (rounding_float (round_mode m) 53 1074) x
end.
