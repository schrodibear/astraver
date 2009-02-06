
(* Why model for floating-point numbers
   Implements the file lib/why/floats_full.why *)

Require Export WhyFloats.


Inductive float_format : Set :=  Single | Double.

Definition bfloat_format (f : float_format) :=
match f with 
| Single => bsingle
| Double => bdouble
end.

Definition precision (f : float_format) :=
match f with 
| Single => 24%nat
| Double => 53%nat
end.

Definition max_gen_float (f : float_format) :=
match f with 
| Single => ((2-powerRZ radix (-23))*powerRZ radix 127)%R
| Double => ((2-powerRZ radix (-52))*powerRZ radix 1023)%R
end.

(*
Definition plus_infinity_gen_float (f : float_format) :=
match f with 
| Single => (powerRZ radix 128)%R
| Double => (powerRZ radix 1024)%R
end.
*)


(* generic floats*)

Record gen_float : Set := mk_gen_float {
   genf         : float;
   exact_value : R;
   model_value : R
 }.


Definition float_value (x:gen_float) := FtoRradix (genf x).

Definition gen_round_error (x:gen_float) := 
    (Rabs ((exact_value x) - (float_value x))).

Definition gen_total_error (x:gen_float):= 
    (Rabs ((model_value x) - (float_value x))).

Definition gen_set_model (x:gen_float) (r:R) :=
      mk_gen_float (genf x) (exact_value x) r.


Definition  gen_float_of_real_logic_aux (f:float_format) (m:mode) (r r1 r2:R) := 
match m with
  |  nearest_even => mk_gen_float (RND_EvenClosest (bfloat_format f) radix (precision f) r) 
                                 r1 r2
  |  to_zero          => mk_gen_float (RND_Zero (bfloat_format f) radix (precision f) r) 
                                 r1 r2
  |  up                  => mk_gen_float (RND_Max (bfloat_format f) radix (precision f) r) 
                                 r1 r2
  |  down             => mk_gen_float (RND_Min (bfloat_format f) radix (precision f) r) 
				r1 r2
  |  nearest_away => mk_gen_float (RND_ClosestUp (bfloat_format f) radix (precision f) r) 
				r1 r2
  end.

   
Definition gen_float_of_real_logic (f:float_format) (m:mode) (r:R) := gen_float_of_real_logic_aux f m r r r.
   

Definition round_float (f:float_format) (m:mode) (r:R) := FtoRradix (genf (gen_float_of_real_logic f m r)).

Definition no_overflow (f : float_format) (m : mode) (x:R) :=
(Rabs (round_float f m x) <= max_gen_float f)%R.





(* formalization of the full model *)

Inductive Float_class  : Set :=  
Finite
| Infinite 
| Nan.

Inductive sign : Set := 
Negative 
| Positive.

Parameter float_class : gen_float -> Float_class.

Parameter float_sign : gen_float -> sign.
(*
Definition float_sign (x : gen_float) :=
match (Fnum x >=0)%Z with
| false => Negative
| true=> Positive
end.
*)


Parameter real_sign : R -> sign.
(*
Definition real_sign (x : R) :=
match (x >=0)%R with
| false => Negative
| true=> Positive
end.
*)

Definition int_of_float_sign (x : gen_float) :=
match (float_sign x) with
| Negative => (-1)%Z
| Positive => 1%Z
end.



