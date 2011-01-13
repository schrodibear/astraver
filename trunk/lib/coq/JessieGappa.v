(* minimal set of defs for using gappa *)
(* formalization of the full model *)

Require Export WhyFloats.

Inductive float_format : Set :=  Single | Double.

Definition max_float2 (f : float_format) :=
match f with 
| Single => max_single
| Double => max_double
end.

Definition max_gen_float (f : float_format) := max_float2 f.

Definition min_float2 (f : float_format) :=
match f with 
| Single => bpow radix2 (-149) 
| Double => bpow radix2 (-1074)
end.

Definition min_gen_float (f:float_format) := min_float2 f.

(* generic floats*)

Inductive Float_class  : Set :=  
  Finite
| Infinite 
| NaN.

Inductive sign : Set := 
  Negative 
| Positive.

Definition same_sign_real_bool (b:sign) (x:R) :=
   match b with
     | Negative => (x < 0)%R
     | Positive => (x > 0)%R
  end.

Lemma same_sign_real_bool_zero1: forall b:sign,
            ~ same_sign_real_bool b 0.
Proof.
intros; destruct b; unfold same_sign_real_bool; apply Rge_not_lt;
auto with real.
Save.

Lemma same_sign_real_bool_zero2: forall x:R, 
          same_sign_real_bool Negative x /\  same_sign_real_bool Positive x
          -> False (* in particular x=0%R*).
Proof.
intros;unfold same_sign_real_bool in H;destruct H.
generalize ((Rlt_not_ge x 0) H);intro;destruct H1;left;trivial.
Save.

Lemma same_sign_real_bool_zero3: forall b:sign, forall x:R, 
            same_sign_real_bool b x -> x <> 0%R.
Proof.
intros b x;case b;intro;unfold same_sign_real_bool in *;auto with real.
Save.

Lemma  same_sign_real_bool_correct1: forall b:sign, forall x:R,
              ((x < 0)%R <-> same_sign_real_bool Negative x) /\
              ((x > 0)%R <-> same_sign_real_bool Positive x).
Proof.
intros;repeat split;intro;unfold same_sign_real_bool in *;trivial.
Save.

Lemma  same_sign_real_bool_correct2: forall b:sign, forall x:R,
             same_sign_real_bool b x -> ((x < 0)%R <-> b = Negative).
Proof.
intros;split;intro;destruct b;trivial.
unfold same_sign_real_bool in H;
absurd (x > 0)%R; [apply Rle_not_gt; apply Rlt_le;auto | trivial].
discriminate H0.
Save.

Lemma  same_sign_real_bool_correct3: forall b:sign, forall x:R,
             same_sign_real_bool b x -> ((x > 0)%R <-> b = Positive).
Proof.
intros;split;intro;destruct b;trivial.
unfold same_sign_real_bool in H;
absurd (x > 0)%R; [apply Rle_not_gt; apply Rlt_le;auto | trivial].
discriminate H0.
Save.




Record gen_float : Set := mk_gen_float {
   float_class : Float_class;
   float_sign : sign;
   float_value : R;
   exact_value : R;
   model_value : R;
   sign_invariant: float_class = Finite -> (float_value <> 0)%R -> 
                          same_sign_real_bool float_sign float_value
}.


Lemma sign_dec: forall x, 
             float_sign x =Negative \/ float_sign x = Positive.
Proof.
intros;destruct (float_sign x); auto.
Save.  

Lemma sign_not_pos_neg: forall x:gen_float,
            float_sign x <> Positive -> float_sign x =Negative.
Proof.
intros;case (sign_dec x); [auto | 
intro;absurd (float_sign x = Positive);auto].
Save.

Lemma sign_not_neg_pos: forall x:gen_float,
            float_sign x <> Negative -> float_sign x = Positive.
Proof.
intros;case (sign_dec x);[intro;absurd (float_sign x = Negative);auto | 
auto].
Save.

Lemma class_dec: forall x:gen_float, 
float_class x = Finite \/ float_class x = Infinite \/ float_class x = NaN.
Proof.
intros;destruct (float_class x);intuition.
Save.


Definition same_sign_real (x:gen_float) (y:R) :=
                      same_sign_real_bool (float_sign x) y.

Definition same_sign (x y : gen_float) := 
                      float_sign x = float_sign y .

Definition diff_sign (x y : gen_float) := 
                      float_sign x <> float_sign y.

Definition product_sign (z x y : gen_float) :=
                     (same_sign x y -> float_sign z = Positive) /\
                     (diff_sign x y  -> float_sign z = Negative).

Definition same_class (x:gen_float) (y:gen_float):= 
                     float_class x = float_class y.
 
Definition diff_class  (x:gen_float) (y:gen_float) := 
               float_class x <> float_class y.

Lemma same_sign_dec: forall x y, same_sign x y \/ diff_sign x y.
Proof.
intros;unfold same_sign, diff_sign.
destruct (float_sign x); destruct (float_sign y); 
[auto | right;discriminate | right;discriminate | auto].
Save.

Lemma same_class_dec: forall x y, same_class x y \/ diff_class x y.
Proof.
intros;unfold same_class, diff_class.
destruct (float_class x); destruct (float_class y);
[auto | right;discriminate | right;discriminate | right;discriminate | 
auto | right;discriminate | right;discriminate | right;discriminate | 
auto].
Save.

Lemma diff_sign_trans: forall x y z, 
      diff_sign x y /\ diff_sign y z -> same_sign x z.
Proof.
unfold diff_sign,same_sign.
intros.
destruct H.
destruct (float_sign y).
generalize ((sign_not_neg_pos x) H);intro;rewrite H1;symmetry;
apply (sign_not_neg_pos z);auto.
generalize ((sign_not_pos_neg x) H);intro;rewrite H1;symmetry;
apply (sign_not_pos_neg z);auto.
Save.


Lemma exists_positive_float : Infinite = Finite ->  (F2R (Float radix2 2 3) <> 0)%R -> 
             same_sign_real_bool Positive (F2R (Float radix2 2 3)).
Proof.
intros;discriminate H.
Save.
Lemma exists_negative_float: Infinite = Finite ->  (F2R (Float radix2 2 3) <> 0)%R -> 
             same_sign_real_bool Negative (F2R (Float radix2 2 3)).
Proof.
intros; discriminate H.
Save.

Lemma exists_product_sign: forall x y, exists z, product_sign z x y.
Proof.
intros; unfold product_sign.
case (same_sign_dec x y); intro.
exists (mk_gen_float Infinite Positive _ R1 R1 exists_positive_float);split;
intro;[auto | unfold same_sign, diff_sign in *;rewrite H in H0;
contradiction H0; trivial].
exists (mk_gen_float Infinite Negative _ R1 R1 exists_negative_float);split;
intro; [unfold same_sign, diff_sign in *;rewrite H0 in H;
contradiction H; trivial | auto].
Save.

Lemma finite_sign : forall x:gen_float,
            float_class x = Finite /\ (float_value x <> 0)%R -> 
            same_sign_real x (float_value x).
Proof.
intuition; unfold same_sign_real, float_value.
apply sign_invariant; trivial.
Qed.

Lemma finite_sign_neg1: forall x:gen_float,
            float_class x = Finite /\ (float_value x < 0)%R -> 
            float_sign x = Negative.
Proof.
intros;destruct H.
assert (float_value x <> 0)%R;auto with real.
generalize (sign_invariant x H H1);intro.
unfold float_value in *.
apply (same_sign_real_bool_correct2 (float_sign x) (float_value x) H2);trivial.
Save.


Lemma finite_sign_neg2: forall x:gen_float,
            float_class x = Finite /\ (float_value x <> 0)%R  /\ 
            float_sign x = Negative -> (float_value x < 0)%R.
Proof.
intros; destruct H;destruct H0.
generalize (sign_invariant x H H0);intro.
unfold float_value in *.
apply (same_sign_real_bool_correct2 (float_sign x) (float_value x) H2);trivial.
Save.

Lemma finite_sign_pos1: forall x:gen_float,
            float_class x = Finite /\ (float_value x > 0)%R -> 
            float_sign x = Positive.
Proof.
intros;destruct H.
assert (float_value x <> 0)%R;auto with real.
generalize (sign_invariant x H H1);intro.
unfold float_value in *.
apply (same_sign_real_bool_correct3 (float_sign x) (float_value x) H2);trivial.
Save.

Lemma finite_sign_pos2: forall x:gen_float,
            float_class x = Finite /\ (float_value x <> 0)%R  /\ 
            float_sign x = Positive -> (float_value x > 0)%R.
Proof.
intros; destruct H;destruct H0.
generalize (sign_invariant x H H0);intro.
unfold float_value in *.
apply (same_sign_real_bool_correct3 (float_sign x) (float_value x) H2);trivial.
Save.


Lemma same_sign_product: forall x y,
      float_class x = Finite /\ float_class y = Finite /\ 
      same_sign x y -> (float_value x * float_value y >= 0)%R.
Proof.
intros.
destruct H.
Admitted.
(*todo*)

Lemma diff_sign_product: forall x y,
      float_class x = Finite /\ float_class y = Finite /\
      (float_value x * float_value y < 0)%R -> diff_sign x y.
Proof.
Admitted.
(*todo*)

Definition is_finite  (x:gen_float) := float_class x = Finite.

Lemma is_finite_dec: forall x, is_finite x \/ ~ is_finite x.
Proof.
intro; unfold is_finite; destruct (float_class x); 
[auto | right;discriminate | right;discriminate].
Save.

Definition is_infinite  (x:gen_float) := float_class x = Infinite.

Lemma is_infinite_dec: forall x, is_infinite x \/ ~ is_infinite x.
Proof.
intro; unfold is_infinite; destruct (float_class x);
[right; discriminate | auto | right; discriminate]. 
Save.

Definition is_NaN  (x:gen_float) := float_class x = NaN.

Lemma is_NaN_dec: forall x, is_NaN x \/ ~ is_NaN x.
Proof.
intro; unfold is_NaN;destruct (float_class x); 
[right; discriminate | right; discriminate | auto].
Save.

Definition is_not_NaN  (x:gen_float) := 
               float_class x = Finite \/ float_class x = Infinite.

Lemma is_not_NaN_correct1: forall x,
            is_not_NaN x -> ~ is_NaN x.
Proof.
intuition; unfold is_not_NaN,is_NaN in *.
rewrite H0 in H;destruct H;discriminate.
Save.

Lemma is_not_NaN_correct2: forall x,
            ~ is_NaN x -> is_not_NaN x.
Proof.
intuition;unfold is_not_NaN,is_NaN in *.
destruct (float_class x);auto.
contradiction H;trivial.
Save.

Definition is_minus_infinity  (x:gen_float) := 
               float_class x = Infinite /\ float_sign x = Negative.

Lemma is_minus_infinity_dec: forall x, 
            is_minus_infinity x \/ ~ is_minus_infinity x.
Proof.
intro; unfold is_minus_infinity;
destruct (float_class x); destruct (float_sign x);intuition;
right; intro; destruct H; discriminate.
Save.

Definition is_plus_infinity  (x:gen_float) := 
               float_class x = Infinite /\ float_sign x = Positive.

Lemma is_plus_infinity_dec: forall x, 
            is_plus_infinity x \/ ~ is_plus_infinity x.
Proof.
intro; unfold is_plus_infinity;
destruct (float_class x); destruct (float_sign x);intuition;
right; intro; destruct H; discriminate.
Save.


Definition gen_round_error (x:gen_float) := 
               (Rabs ((exact_value x) - (float_value x))).
Definition gen_relative_error (x:gen_float) := 
               Rdiv (Rabs ((exact_value x) - (float_value x))) (exact_value x).
Definition gen_total_error (x:gen_float):= 
               (Rabs ((model_value x) - (float_value x))).
(*
Definition gen_set_model (x:gen_float) (r:R) :=
    model_value x = r.
*)


Definition round_float (f : float_format) (m : mode) (x:R) :=
match f with
| Single => round_single m x
| Double => round_double m x
end.

Definition no_overflow (f : float_format) (m : mode) (x:R) :=
(Rabs (round_float f m x) <= max_gen_float f)%R.

Lemma overflow_dec : forall f m x, 
             no_overflow f m x \/ not (no_overflow f m x).
Proof.
intros; unfold no_overflow.
case (Rtotal_order (Rabs (round_float f m x)) (max_gen_float f));
auto with real; intros; elim H; auto with real.
Save.

Definition overflow_value  (f:float_format) (m:mode) (x:gen_float) := 
(m = down -> (float_sign x = Negative -> is_infinite x) /\
                       (float_sign x = Positive -> is_finite x /\
                                                   float_value x = max_gen_float f))
/\
(m = up -> (float_sign x = Negative -> is_finite x /\
                                       float_value x = Ropp (max_gen_float f)) /\
           (float_sign x = Positive -> is_infinite x)) 
/\
(m = to_zero -> is_finite x /\
               (float_sign x = Negative -> 
                float_value x = Ropp (max_gen_float f)) /\
               (float_sign x = Positive -> 
                float_value x = max_gen_float f)) 
/\
(m = nearest_away \/ m = nearest_even -> is_infinite x).

Definition overflow_value_ (f:float_format) (m:mode) (x:gen_float) :=
match m, float_sign x with 
   | down, Negative => is_infinite x 
   | down, Positive => is_finite x /\
                       float_value x = max_gen_float f
   | up, Negative => is_finite x /\
                     float_value x = (- max_gen_float f)%R
   | up, Positive => is_infinite x 
   | to_zero, Negative => is_finite x /\
                          float_value x = (- max_gen_float f)%R
   | to_zero, Positive => is_finite x /\
                          float_value x = max_gen_float f
   | _ , _ => is_infinite x
end.


Definition underflow_value (f:float_format) (m:mode) (x:gen_float) :=
is_finite x /\ 
(float_sign x = Positive -> (m <> up -> float_value x = 0%R) /\
                            (m=up -> float_value x =  min_gen_float f))
/\
(float_sign x = Negative -> (m <> down -> float_value x = 0%R) /\
                            (m = down -> float_value x = Ropp (min_gen_float f))).


(*Why predicate*) Definition gen_float_of_real_post  (f:float_format) (m:mode) (x:R) (res:gen_float)
  := (eq (float_value res) (round_float f m x)) /\
     (eq (exact_value res) x) /\ (eq (model_value res) x).

(*Why predicate*) Definition add_gen_float_post  (f:float_format) (m:mode) (x:gen_float) (y:gen_float) (res:gen_float)
  := (eq (float_value res) (round_float
                            f m (Rplus (float_value x) (float_value y)))) /\
     (eq (exact_value res) (Rplus (exact_value x) (exact_value y))) /\
     (eq (model_value res) (Rplus (model_value x) (model_value y))).

(*Why predicate*) Definition sub_gen_float_post  (f:float_format) (m:mode) (x:gen_float) (y:gen_float) (res:gen_float)
  := (eq (float_value res) (round_float
                            f m (Rminus (float_value x) (float_value y)))) /\
     (eq (exact_value res) (Rminus (exact_value x) (exact_value y))) /\
     (eq (model_value res) (Rminus (model_value x) (model_value y))).

(*Why predicate*) Definition neg_gen_float_post  (f:float_format) (m:mode) (x:gen_float) (res:gen_float)
  := (eq (float_value res) (round_float f m (Ropp (float_value x)))) /\
     (eq (exact_value res) (Ropp (exact_value x))) /\
     (eq (model_value res) (Ropp (model_value x))).

(*Why predicate*) Definition mul_gen_float_post  (f:float_format) (m:mode) (x:gen_float) (y:gen_float) (res:gen_float)
  := (eq (float_value res) (round_float
                            f m (Rmult (float_value x) (float_value y)))) /\
     (eq (exact_value res) (Rmult (exact_value x) (exact_value y))) /\
     (eq (model_value res) (Rmult (model_value x) (model_value y))).

(*Why predicate*) Definition div_gen_float_post  (f:float_format) (m:mode) (x:gen_float) (y:gen_float) (res:gen_float)
  := (eq (float_value res) (round_float
                            f m (Rdiv (float_value x) (float_value y)))) /\
     (eq (exact_value res) (Rdiv (exact_value x) (exact_value y))) /\
     (eq (model_value res) (Rdiv (model_value x) (model_value y))).

(*Why predicate*) Definition cast_gen_float_post  (f:float_format) (m:mode) (x:gen_float) (res:gen_float)
  := (eq (float_value res) (round_float f m (float_value x))) /\
     (eq (exact_value res) (exact_value x)) /\
     (eq (model_value res) (model_value x)).


Definition sign_zero_result (m:mode) (x:gen_float) := 
float_value x = 0%R -> (m = down -> float_sign x = Negative) 
                       /\ 
                       (m <> down -> float_sign x = Positive).

Definition float_le_float  (x:gen_float) (y:gen_float) := 
               (is_finite x /\ is_finite y /\ (float_value x <= float_value y)%R)
               \/ (is_minus_infinity x /\ is_not_NaN y) 
               \/ (is_not_NaN x /\ is_plus_infinity y).

Definition float_lt_float (x:gen_float) (y:gen_float) := 
               (is_finite x /\ is_finite y /\ (float_value x < float_value y)%R) 
               \/ (is_minus_infinity x /\ is_not_NaN y /\ ~ is_minus_infinity y) 
               \/ (is_not_NaN x /\ ~ is_plus_infinity x /\ is_plus_infinity y).

Definition float_ge_float  (x:gen_float) (y:gen_float) := 
               float_le_float y x.

Definition float_gt_float  (x:gen_float) (y:gen_float) := 
               float_lt_float y x.

Definition float_eq_float  (x:gen_float) (y:gen_float) := 
               is_not_NaN x /\ is_not_NaN y /\
               (is_finite x /\ is_finite y /\ float_value x = float_value y) 
               \/ (is_infinite x /\ is_infinite y /\ same_sign x y).

Definition float_ne_float  (x:gen_float) (y:gen_float) := 
                ~ float_eq_float x y.


Lemma round_of_zero: forall f m,
            (round_float f m 0 = 0)%R.
Proof.
intros f m.
case f ; apply round_0.
Save.

Lemma round_of_max_gen: forall f m,
            round_float f m (max_gen_float f) = max_gen_float f.
Proof.
admit. (*gappa succeeds but not with nearest_away til today !! *)
Save.

Lemma round_of_opp_max_gen: forall f m,
            round_float f m (- max_gen_float f) = Ropp (max_gen_float f).
Proof.
admit. (*gappa succeeds but not with nearest_away *)
Save.

Lemma round_of_min_gen: forall f m,
            round_float f m (min_gen_float f) = min_gen_float f.
Proof.
admit. (*gappa succeeds but not with nearest_away *)
Save.


Lemma round_of_opp_min_gen: forall f m,
            round_float f m (- min_gen_float f) = Ropp (min_gen_float f).
Proof.
admit. (*gappa succeeds but not with nearest_away *)
Save.

(*
Lemma round_pow_constant: forall f m x n,
      round_float f m (powerRZ x n) = (powerRZ x n).
Lemma round_of_float_value: forall f m, forall x:gen_float, 
                            round_float f m x = x.
Lemma opp_of_float2: forall x:float2, exists y :float2, y = Ropp x.
*)

Lemma bounded_real_no_overflow : forall f m x, 
(Rabs x <= max_gen_float f)%R -> no_overflow f m x.
Proof.
intros [|].
apply bounded_real_no_overflow_single.
apply bounded_real_no_overflow_double.
Save.


(*
(* powerRZ 2 (max_exp f) is the next gen_float after max_gen_float f *)
Definition max_exp (f:float_format) :=
match f with 
 | Single => 128%Z 
 | Double => 1024%Z  
end.


(* just for m <> nearest_even *)
Lemma bounded_real_overflow_pos : forall f m x,
(x > max_gen_float f)%R 
(* (max_gen_float f < x < powerRZ 2 (max_exp f))%R *) -> 
(m = up \/ m = nearest_away -> ~ no_overflow f m x) 
/\
(m = down \/ m = to_zero -> round_float f m x = max_gen_float f).

(* just for m <> nearest_even *)
Lemma bounded_real_overflow_neg: forall f m x,
(x < - max_gen_float f)%R 
(* (- powerRZ 2 (max_exp f) < x < - max_gen_float f)%R *) -> 
(m = down \/ m = nearest_away -> ~ no_overflow f m x)
/\
(m = up \/ m = to_zero -> (round_float f m x = - max_gen_float f)%R).

(* and for m = nearest_even *)
Lemma bounded_real_overflow_nearest_even: forall f x, 
(Rabs x >= powerRZ 2 (max_exp f))%R -> ~ no_overflow f nearest_even x.

Lemma round_greater_max: forall f m x, 
      ~ no_overflow f m x -> (Rabs x > max_gen_float f)%R.
*)


Lemma positive_constant : forall f m x, 
            (min_gen_float f <= x <= max_gen_float f)%R -> 
            no_overflow f m x  /\ (round_float f m x > 0)%R.
Proof.
intros F m x (Bx1,Bx2).
split.
apply bounded_real_no_overflow.
rewrite Rabs_pos_eq.
exact Bx2.
apply Rle_trans with (2 := Bx1).
unfold min_gen_float, min_float2.
case F ; apply bpow_ge_0.
apply Rlt_gt.
apply Rlt_le_trans with (min_gen_float F).
unfold min_gen_float, min_float2.
case F ; apply bpow_gt_0.
rewrite <- round_of_min_gen with F m.
revert Bx1.
case F ; apply round_monotone ; now apply FLT_exp_correct.
Save.

Lemma negative_constant : forall f m x, 
            (Ropp (max_gen_float f) <= x <= Ropp (min_gen_float f))%R -> 
            no_overflow f m x  /\ (round_float f m x < 0)%R.
Proof.
intros F m x (Bx1,Bx2).
split.
apply bounded_real_no_overflow.
rewrite Rabs_left1.
apply Ropp_le_cancel.
now rewrite Ropp_involutive.
apply Rle_trans with (1 := Bx2).
apply Rge_le.
apply Ropp_0_le_ge_contravar.
unfold min_gen_float, min_float2.
case F ; apply bpow_ge_0.
apply Rle_lt_trans with (- min_gen_float F)%R.
rewrite <- round_of_opp_min_gen with F m.
revert Bx2.
case F ; apply round_monotone ; now apply FLT_exp_correct.
apply Ropp_lt_gt_0_contravar.
unfold min_gen_float, min_float2.
case F ; apply bpow_gt_0.
Save.

Lemma round_increasing: forall f m x y,
      (x <= y)%R -> (round_float f m x <= round_float f m y)%R.
Proof.
intros F m x y.
case F ; apply round_monotone ; now apply FLT_exp_correct.
Save.

Lemma round_greater_min: forall f m x, 
            (Rabs x >= min_gen_float f)%R ->
            (Rabs (round_float f m x) >= min_gen_float f)%R.
Proof.
intros F m x Bx.
apply Rle_ge.
unfold Rabs in Bx.
destruct (Rcase_abs x) as [Hx|Hx].
assert (min_gen_float F <= - round_float F m x)%R.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
rewrite <- round_of_opp_min_gen with F m.
apply round_increasing.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
now apply Rge_le.
rewrite Rabs_left1.
exact H.
apply Ropp_le_cancel.
rewrite Ropp_0.
apply Rle_trans with (2 := H).
unfold min_gen_float, min_float2.
case F ; apply bpow_ge_0.
assert (min_gen_float F <= round_float F m x)%R.
rewrite <- round_of_min_gen with F m.
apply round_increasing.
now apply Rge_le.
rewrite Rabs_pos_eq.
exact H.
apply Rle_trans with (2 := H).
unfold min_gen_float, min_float2.
case F ; apply bpow_ge_0.
Save.


(*
Lemma round_less_min_pos: forall f m x, 
            (0< x < min_gen_float f)%R -> 
            (round_float f m x = 0%R \/ round_float f m x = min_gen_float f).
Lemma round_less_min_neg: forall f m x, 
            (Ropp (min_gen_float f) < x < 0)%R -> 
            (round_float f m x = 0%R \/ round_float f m x = Ropp (min_gen_float f)). 

Lemma round_down_le: forall f x, (round_float f down x <= x)%R.
Lemma round_up_ge: forall f x, (round_float f up x >= x)%R.
Lemma round_down_neg: forall f x, 
             (round_float f down (-x) = - round_float f up x)%R.   
Lemma round_up_neg:  forall f x,  
             (round_float f up (-x) = - round_float f down x)%R.

Lemma no_overflow_neg: forall f x, 
no_overflow f down x -> no_overflow f up (-x).
Proof.
intros;unfold no_overflow;rewrite (round_up_neg f x);
rewrite Rabs_Ropp;trivial.
Save.
*)



(*
Definition gen_float_of_real_logic (f : float_format) (m : mode) (x :R) :=
 match f with
  | Single => (rounding_float (round_mode m) 24 149) x
  | Double => (rounding_float (round_mode m) 53 1074) x
 end.
*)

Parameter gen_float_of_real_logic: 
                 float_format -> mode -> R -> gen_float.

Axiom a1: forall f m x, no_overflow f m x ->
           is_finite (gen_float_of_real_logic f m x) /\
           float_value (gen_float_of_real_logic f m x) = round_float f m x.

Axiom a2: forall f m x, ~ no_overflow f m x -> 
                  same_sign_real (gen_float_of_real_logic f m x) x /\
                  overflow_value f m (gen_float_of_real_logic f m x).

Axiom a3: forall f m x,
            exact_value (gen_float_of_real_logic f m x) = x.

Axiom a4: forall f m x,
             model_value (gen_float_of_real_logic f m x) = x.

Axiom genf_of_real_single: forall m x,
                              float_value (gen_float_of_real_logic Single m x) =
                              round_single m x.

Axiom genf_of_real_double: forall m x,
                              float_value (gen_float_of_real_logic Double m x) =
                              round_double m x.

Lemma gen_float_of_zero: forall f m, 
             float_class  (gen_float_of_real_logic f m 0) = Finite /\         
             float_value (gen_float_of_real_logic f m 0)=0%R.
Proof.
intros F m.
rewrite <- (round_of_zero F m) at 3.
apply a1.
unfold no_overflow, max_gen_float, max_float2.
rewrite round_of_zero, Rabs_R0.
case F ; now apply F2R_ge_0_compat.
Save.

Lemma finite_gen_float_of_real_logic: forall f m x,
            float_class (gen_float_of_real_logic f m x) = Finite ->
            (Rabs (float_value (gen_float_of_real_logic f m x)) <= 
            max_gen_float f)%R.
Proof.
intros.
case (overflow_dec f m x);intro.
generalize (proj2 (a1 f m x H0));intro.
rewrite H1;auto.
generalize (a2 f m x H0);intros (H1,H2).
unfold overflow_value,same_sign_real in *.
decompose [and or] H2;clear H2.
destruct m.







Admitted.
(*
clear H3 H4 H5;rewrite H in H7;discriminate H7;auto.

clear H3 H5 H7.
case (Rtotal_order x 0);intro.
generalize ((proj1 (same_sign_real_bool_correct2 
(float_sign (gen_float_of_real_logic f to_zero x)) x H1)) H2);intro.
rewrite H3 in H4;intuition.
rewrite H6;rewrite Rabs_Ropp.
right;apply (Rabs_right (max_gen_float f));case f;unfold max_gen_float.
rewrite <- (Rmult_0_r 16777215);apply Rmult_ge_compat_l.
admit. (*(16777215 >=0)%R*)
apply Rle_ge;apply powerRZ_le;auto with real.
rewrite <- (Rmult_0_r 9007199254740991);apply Rmult_ge_compat_l.
admit. (*(9007199254740991>=0)%R*)
apply Rle_ge;apply powerRZ_le;auto with real.
destruct H2.
rewrite H2;rewrite (proj2 (gen_float_of_zero f to_zero));rewrite Rabs_R0.
case f;unfold max_gen_float.
rewrite <- (Rmult_0_r 16777215);apply Rmult_le_compat_l;auto with real.
admit. (*(0<=16777215)%R*)
rewrite <- (Rmult_0_r 9007199254740991);apply Rmult_le_compat_l.
admit. (*(0<=9007199254740991)%R*)
apply powerRZ_le;auto with real.
generalize ((proj1 (same_sign_real_bool_correct3 
(float_sign (gen_float_of_real_logic f to_zero x)) x H1)) H2);intro.
rewrite H3 in H4;intuition.
rewrite H6.
right;apply (Rabs_right (max_gen_float f)).
case f;unfold max_gen_float;admit. (*as above*)

clear H3 H4 H7.
rewrite H in H5;intuition.
case (Rtotal_order x 0);intro.
generalize ((proj1 (same_sign_real_bool_correct2 
(float_sign (gen_float_of_real_logic f up x)) x H1)) H2);intro.
rewrite H5 in H3;intuition.
rewrite H7;rewrite Rabs_Ropp.
right;apply (Rabs_right (max_gen_float f)).
case f;unfold max_gen_float;admit. (*as above*)
destruct H2.
rewrite H2;rewrite (proj2 (gen_float_of_zero f up)).
rewrite Rabs_R0.
case f;unfold max_gen_float;admit. (*as above*)
generalize ((proj1 (same_sign_real_bool_correct3 
(float_sign (gen_float_of_real_logic f up x)) x H1)) H2);intro.
rewrite H5 in H4;discriminate H4;trivial.

clear H4 H5 H7.
rewrite H in H3;intuition.
case (Rtotal_order x 0);intro.
generalize ((proj1 (same_sign_real_bool_correct2 
(float_sign (gen_float_of_real_logic f down x)) x H1)) H2);intro.
rewrite H5 in H3;discriminate H3;trivial.
destruct H2.
rewrite H2;rewrite (proj2 (gen_float_of_zero f down)).
rewrite Rabs_R0.
case f;unfold max_gen_float;admit. (*as above*)
generalize ((proj1 (same_sign_real_bool_correct3 
(float_sign (gen_float_of_real_logic f down x)) x H1)) H2);intro.
rewrite H5 in H4;intuition.
rewrite H7;right;apply (Rabs_right (max_gen_float f)).
case f;unfold max_gen_float;admit. (*as above*)

clear H3 H4 H5;rewrite H in H7;discriminate H7;auto.
Save.
*)

Lemma gen_bounded_real_no_overflow : forall f m x, 
            (Rabs x <= max_gen_float f)%R -> 
             float_class (gen_float_of_real_logic f m x) = Finite /\
             float_value (gen_float_of_real_logic f m x) = round_float f m x.
Proof.
intros;generalize (bounded_real_no_overflow f m x H);exact (a1 f m x).
Save.


(* just for m <> nearest_even and m <> nearest_away *)
(*Lemma gen_bounded_real_overflow : forall f m x,
((max_gen_float f < x < powerRZ 2 (max_exp f))%R ->  
is_plus_infinity (gen_float_of_real_logic f up x) /\
(m = down \/ m = to_zero -> 
         float_class (gen_float_of_real_logic f m x) = Finite /\
         float_value (gen_float_of_real_logic f m x) = max_gen_float f) /\
         float_sign (gen_float_of_real_logic f m x) = Positive)
/\
((- powerRZ 2 (max_exp f) < x < - max_gen_float f)%R -> 
is_minus_infinity (gen_float_of_real_logic f down x) /\
(m = up \/ m = to_zero -> 
         float_class (gen_float_of_real_logic f m x) = Finite /\
         float_value (gen_float_of_real_logic f m x) = max_gen_float f) /\
         float_sign (gen_float_of_real_logic f m x) = Negative)
/\
((x >= powerRZ 2 (max_exp f))%R -> 
is_plus_infinity (gen_float_of_real_logic f m x))
/\
((x <= - powerRZ 2 (max_exp f))%R -> 
is_minus_infinity (gen_float_of_real_logic f m x)).
Proof.
Admitted.
*)

Lemma gen_positive_constant : forall f m x,
                    (min_gen_float f <= x <= max_gen_float f)%R ->
            	    float_class (gen_float_of_real_logic f m x) = Finite /\
                    (float_value (gen_float_of_real_logic f m x) > 0)%R /\
             	    float_sign (gen_float_of_real_logic f m x) = Positive.
Proof.
intros;generalize (positive_constant f m x H);intros (H1,H2).
generalize (a1 f m x H1);intros (H3,H4).
repeat split;trivial.
rewrite H4;trivial.
apply finite_sign_pos1;split;[trivial | rewrite H4;trivial].
Save.

Lemma gen_negative_constant :forall f m x,
             (Ropp (max_gen_float f) <= x <= Ropp (min_gen_float f))%R ->
             float_class (gen_float_of_real_logic f m x) = Finite /\
     	     (float_value (gen_float_of_real_logic f m x) < 0)%R /\
     	     float_sign (gen_float_of_real_logic f m x) = Negative.
Proof.
intros;generalize (negative_constant f m x H);intros (H1,H2).
generalize (a1 f m x H1);intros (H3,H4).
repeat split;trivial.
rewrite H4;trivial.
apply finite_sign_neg1;split;[trivial | rewrite H4;trivial].
Save.

(*
(* just for m <> nearest_even and m <> nearest_away *) 
Lemma gen_float_of_pos_real_underflow: forall f m x, 
(0< x < min_gen_float f)%R -> 
float_class (gen_float_of_real_logic f m x) = Finite /\
float_value (gen_float_of_real_logic f up x) =  min_gen_float f /\
(m=down \/ m=to_zero) -> float_value (gen_float_of_real_logic f m x)=0%R.
Proof.
Admitted.


(* just for m <> nearest_even and m <> nearest_away *) 
Lemma gen_float_of_neg_real_underflow: forall f m x, 
(Ropp (min_gen_float f) < x < 0)%R -> 
float_class (gen_float_of_real_logic f m x) = Finite /\
float_value (gen_float_of_real_logic f down x) =  Ropp (min_gen_float f) /\
(m=up \/ m=to_zero) -> float_value (gen_float_of_real_logic f m x)=0%R.
Proof.
Admitted.


Lemma gen_float_of_real_not_NaN : forall f m x,
             is_not_NaN (gen_float_of_real_logic f m x).
Proof.
intros;unfold is_not_NaN.
case (Rle_dec (Rabs x) (max_gen_float f));intro.
left;exact (proj1 (gen_bounded_real_no_overflow f m x r)).
assert (Rabs x > max_gen_float f)%R by (apply Rnot_le_gt;trivial);clear n.
generalize (gen_bounded_real_overflow f m x H);intros (h1,h2).
decompose [or] (mode_dec m);unfold same_sign_real,overflow_value in *.
rewrite H0 in *;decompose [and or] h2;clear h2 H1 H2 H3;right;intuition.
rewrite H1 in *;decompose [and or] h2;clear h2 H0 H3 H5;left;intuition.
rewrite H0 in *;decompose [and or] h2;clear h2 H1 H2 H5.
case (Rtotal_order x 0);intro.
generalize ((proj1 (same_sign_real_bool_correct2 
(float_sign (gen_float_of_real_logic f up x)) x h1)) H1);intro.
rewrite H2 in H3;left;intuition.
destruct H1.
rewrite H1;left;exact (proj1 (gen_float_of_zero f up)).
generalize ((proj1 (same_sign_real_bool_correct3 
(float_sign (gen_float_of_real_logic f up x)) x h1)) H1);intro.
rewrite H2 in H3;right;intuition.
rewrite H0 in *;decompose [and or] h2;clear h2 H2 H3 H5.
case (Rtotal_order x 0);intro.
generalize ((proj1 (same_sign_real_bool_correct2 
(float_sign (gen_float_of_real_logic f down x)) x h1)) H2);intro.
rewrite H3 in H1;right;intuition.
destruct H2.
rewrite H2;left;exact (proj1 (gen_float_of_zero f down)).
generalize ((proj1 (same_sign_real_bool_correct3 
(float_sign (gen_float_of_real_logic f down x)) x h1)) H2);intro.
rewrite H3 in H1;left;intuition.
Save.
*)






Definition is_gen_zero (x:gen_float) := 
               float_class x =Finite /\ float_value x = R0.

Lemma is_gen_zero_dec: forall x:gen_float, 
            float_class x =Finite -> is_gen_zero x \/ ~ is_gen_zero x.
Proof.
intros x Hx.
unfold is_gen_zero.
destruct (Req_dec (float_value x) 0) as [Zx|Zx].
left. now split.
right.
intros (_,H).
now apply Zx.
Qed.

Lemma is_gen_zero_correct1: forall x:gen_float,
            is_gen_zero x -> float_value x =0%R.
Proof.
now intros x (_,H).
Save.


Lemma zero_Fexp1: forall x : float radix2,
  Fexp x = 0%Z -> F2R x = Z2R (Fnum x).
Proof.
intros x Ex.
unfold F2R.
rewrite Ex.
apply Rmult_1_r.
Save.

Lemma zero_Fexp2: forall z:Z, 
  F2R (Float radix2 z 0) = Z2R z.
Proof.
intros z.
now apply zero_Fexp1.
Save.

Lemma real_zero_integer: forall m:Z, 
            Z2R m=0%R -> m=0%Z.
Proof.
intros m Hm.
now apply eq_Z2R.
Save.

Lemma zero_Fnum_float2: forall x : float radix2,
  Fnum x = 0%Z <-> F2R x = 0%R.
Proof.
Admitted.

Lemma is_gen_zero_correct2: forall x:gen_float,
            float_class x =Finite -> float_value x =0%R -> is_gen_zero x.
Proof.
intros x Cx Vx.
now split.
Save.


Lemma is_gen_zero_comp1: forall x y : gen_float, 
             is_gen_zero x -> float_value x = float_value y -> 
             float_class y = Finite -> is_gen_zero y.
Proof.
intros;apply is_gen_zero_correct2;auto;rewrite <- H0;
apply is_gen_zero_correct1; trivial.
Qed.
Lemma is_gen_zero_comp2: forall x y,float_class x = Finite -> 
            ~ is_gen_zero x -> float_value x = float_value y -> 
                                          ~ is_gen_zero y.
Proof.
intros; unfold not; intro; contradiction H0;
apply (is_gen_zero_comp1 y x);auto.
Save.


Lemma neg_Fnum_float2: forall x : float radix2,
  (Fnum x < 0)%Z <-> (F2R x < 0)%R.
Admitted.
Lemma pos_Fnum_float2: forall x : float radix2,
  (Fnum x > 0)%Z <-> (F2R x > 0)%R.
Admitted.

Lemma zero_is_gen_zero: forall f m,
is_gen_zero (gen_float_of_real_logic f m 0).
Proof.
intros;apply is_gen_zero_correct2.
apply (proj1 (gen_float_of_zero f m)).
apply (proj2 (gen_float_of_zero f m)).
Save.

Definition is_gen_zero_plus x := is_gen_zero x /\ float_sign x =Positive.
Definition is_gen_zero_minus x := is_gen_zero x /\ float_sign x =Negative.

Lemma is_gen_zero_plus_dec: forall x, float_class x =Finite -> 
            is_gen_zero_plus x \/ ~  is_gen_zero_plus x.
Proof.
intros; unfold is_gen_zero_plus. 
case (float_sign x); case (is_gen_zero_dec x);
[trivial | intro;right;intuition;discriminate | intro;right;intuition | trivial 
 | auto | intuition].
Save.


Lemma is_gen_zero_minus_dec: forall x, float_class x =Finite -> 
            is_gen_zero_minus x \/ ~  is_gen_zero_minus x.
Proof.
intros; unfold is_gen_zero_minus.
case (float_sign x); case (is_gen_zero_dec x);
[trivial | auto | intuition | trivial | intro;right;intuition;discriminate | 
intro;right;intuition].
Save.




