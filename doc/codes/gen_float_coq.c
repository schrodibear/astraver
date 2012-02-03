
Record gen_float : Set := mk_gen_float {
   genf : float2;
   float_class : Float_class;
   float_sign : sign;
   sign_invariant: float_class = Finite -> 
      (float2R genf <> 0)%R ->
       same_sign_real_bool float_sign (float2R genf);
   float_value := float2R genf;
   exact_value : R;
   model_value : R
}.
