(* Why model for floating-point numbers
   Implements the file lib/why/floats_strict.why *)

Require Export WhyFloats.

Record single : Set := mk_single {
  single_datum :> WhyFloats.single;
  single_finite : is_finite 24 128 (single_float single_datum) = true
}.

Record double : Set := mk_double {
  double_datum :> WhyFloats.double;
  double_finite : is_finite 53 1024 (double_float double_datum) = true
}.

(* Double and Single precision: axioms *)

(*Why axiom*) Lemma single_value_is_bounded :
  (forall (x:single), (Rle (Rabs (single_value x)) max_single)).
Proof.
intros s.
apply value_is_bounded.
Qed.

(*Why axiom*) Lemma double_value_is_bounded :
  (forall (x:double), (Rle (Rabs (double_value x)) max_double)).
Proof.
intros s.
apply value_is_bounded.
Qed.

(* Various Why predicates. Only definitions are left. *)

(*Why predicate*) Definition single_of_real_post  (m:mode) (x:R) (res:single)
  := (eq (single_value res) (round_single m x)) /\
     (eq (single_exact res) x) /\ (eq (single_model res) x).

(*Why predicate*) Definition single_of_double_post  (m:mode) (x:double) (res:single)
  := (eq (single_value res) (round_single m (double_value x))) /\
     (eq (single_exact res) (double_exact x)) /\
     (eq (single_model res) (double_model x)).

(*Why predicate*) Definition add_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rplus (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rplus (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rplus (single_model x) (single_model y))).

(*Why predicate*) Definition sub_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rminus (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rminus (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rminus (single_model x) (single_model y))).

(*Why predicate*) Definition mul_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rmult (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rmult (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rmult (single_model x) (single_model y))).

(*Why predicate*) Definition div_single_post  (m:mode) (x:single) (y:single) (res:single)
  := (eq (single_value res) (round_single
                             m (Rdiv (single_value x) (single_value y)))) /\
     (eq (single_exact res) (Rdiv (single_exact x) (single_exact y))) /\
     (eq (single_model res) (Rdiv (single_model x) (single_model y))).

(*Why predicate*) Definition sqrt_single_post  (m:mode) (x:single) (res:single)
  := (eq (single_value res) (round_single m (sqrt (single_value x)))) /\
     (eq (single_exact res) (sqrt (single_exact x))) /\
     (eq (single_model res) (sqrt (single_model x))).

(*Why predicate*) Definition neg_single_post  (x:single) (res:single)
  := (eq (single_value res) (Ropp (single_value x))) /\
     (eq (single_exact res) (Ropp (single_exact x))) /\
     (eq (single_model res) (Ropp (single_model x))).

(*Why predicate*) Definition abs_single_post  (x:single) (res:single)
  := (eq (single_value res) (Rabs (single_value x))) /\
     (eq (single_exact res) (Rabs (single_exact x))) /\
     (eq (single_model res) (Rabs (single_model x))).

(*Why predicate*) Definition double_of_real_post  (m:mode) (x:R) (res:double)
  := (eq (double_value res) (round_double m x)) /\
     (eq (double_exact res) x) /\ (eq (double_model res) x).

(*Why predicate*) Definition double_of_single_post  (x:single) (res:double)
  := (eq (double_value res) (single_value x)) /\
     (eq (double_exact res) (single_exact x)) /\
     (eq (double_model res) (single_model x)).

(*Why predicate*) Definition add_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rplus (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rplus (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rplus (double_model x) (double_model y))).

(*Why predicate*) Definition sub_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rminus (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rminus (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rminus (double_model x) (double_model y))).

(*Why predicate*) Definition mul_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rmult (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rmult (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rmult (double_model x) (double_model y))).

(*Why predicate*) Definition div_double_post  (m:mode) (x:double) (y:double) (res:double)
  := (eq (double_value res) (round_double
                             m (Rdiv (double_value x) (double_value y)))) /\
     (eq (double_exact res) (Rdiv (double_exact x) (double_exact y))) /\
     (eq (double_model res) (Rdiv (double_model x) (double_model y))).

(*Why predicate*) Definition sqrt_double_post  (m:mode) (x:double) (res:double)
  := (eq (double_value res) (round_double m (sqrt (double_value x)))) /\
     (eq (double_exact res) (sqrt (double_exact x))) /\
     (eq (double_model res) (sqrt (double_model x))).

(*Why predicate*) Definition neg_double_post  (x:double) (res:double)
  := (eq (double_value res) (Ropp (double_value x))) /\
     (eq (double_exact res) (Ropp (double_exact x))) /\
     (eq (double_model res) (Ropp (double_model x))).

(*Why predicate*) Definition abs_double_post  (x:double) (res:double)
  := (eq (double_value res) (Rabs (double_value x))) /\
     (eq (double_exact res) (Rabs (double_exact x))) /\
     (eq (double_model res) (Rabs (double_model x))).

Lemma no_overflow_single_bounded :
  forall m x, no_overflow_single m x ->
  (Rabs (round_single m x) < bpow radix2 128)%R.
Proof.
intros m x Bx.
apply Rle_lt_trans with (1 := Bx).
change 128%Z with (24 + 104)%Z.
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
easy.
Qed.

Lemma single_of_real_specification :
  forall m x, no_overflow_single m x ->
  exists z, single_of_real_post m x z.
Proof.
intros m x Bx.
refine (_ (r_to_sd_correct 24 128 (refl_equal true) (refl_equal true) _ x (no_overflow_single_bounded _ x Bx))).
intros (H1, H2).
refine (let H := _ in ex_intro _ (mk_single (round_single_logic m x) H) _).
exact H1.
repeat split.
exact H2.
Qed.

Axiom Bplus_correct : (* the statement from Flocq 1.4 is not strong enough;
                         the axiom can be removed once the library is converted to Flocq 2.0 *)
  forall (prec emax : Z) (Hprec : (0 < prec)%Z) (Hmax : (prec < emax)%Z)
         (m : Fappli_IEEE.mode) (x y : binary_float prec emax),
  is_finite prec emax x = true ->
  is_finite prec emax y = true ->
  if Rlt_bool (Rabs (round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
       (B2R prec emax x + B2R prec emax y))) (bpow radix2 emax)
  then
    B2R prec emax (Bplus prec emax Hprec Hmax m x y) =
      round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (B2R prec emax x + B2R prec emax y) /\
    is_finite prec emax (Bplus prec emax Hprec Hmax m x y) = true
  else
    B2FF prec emax (Bplus prec emax Hprec Hmax m x y) =
      binary_overflow prec emax m (Bsign prec emax x) /\
    Bsign prec emax x = Bsign prec emax y.

Lemma add_single_specification :
  forall m (x y : single),
  no_overflow_single m (single_value x + single_value y) ->
  exists z, add_single_post m x y z.
Proof.
intros m x y Br.
refine (_ (Bplus_correct 24 128 (refl_equal Lt) (refl_equal Lt) (rnd_of_mode m) (single_float x) (single_float y)
  (single_finite x) (single_finite y))).
rewrite Rlt_bool_true.
2: now apply no_overflow_single_bounded.
fold b32_plus.
intros (H1, H2).
refine (ex_intro _ (mk_single (add_single m x y) H2) _).
repeat split.
exact H1.
Qed.

Axiom Bmult_correct : (* the statement from Flocq 1.4 is not strong enough;
                         the axiom can be removed once the library is converted to Flocq 2.0 *)
  forall (prec emax : Z) (Hprec : (0 < prec)%Z) (Hmax : (prec < emax)%Z)
         (m : Fappli_IEEE.mode) (x y : binary_float prec emax),
  if Rlt_bool (Rabs (round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
       (B2R prec emax x * B2R prec emax y))) (bpow radix2 emax)
  then
    B2R prec emax (Bmult prec emax Hprec Hmax m x y) =
      round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (B2R prec emax x * B2R prec emax y) /\
    is_finite prec emax (Bmult prec emax Hprec Hmax m x y) = andb (is_finite prec emax x) (is_finite prec emax y)
  else
    B2FF prec emax (Bmult prec emax Hprec Hmax m x y) =
      binary_overflow prec emax m (xorb (Bsign prec emax x) (Bsign prec emax y)).

Lemma mul_single_specification :
  forall m (x y : single),
  no_overflow_single m (single_value x * single_value y) ->
  exists z, mul_single_post m x y z.
Proof.
intros m x y Br.
refine (_ (Bmult_correct 24 128 (refl_equal Lt) (refl_equal Lt) (rnd_of_mode m) (single_float x) (single_float y))).
rewrite Rlt_bool_true.
2: now apply no_overflow_single_bounded.
fold b32_mult.
intros (H1, H2).
rewrite (single_finite x), (single_finite y) in H2.
refine (ex_intro _ (mk_single (mul_single m x y) H2) _).
repeat split.
exact H1.
Qed.

Axiom Bdiv_correct : (* the statement from Flocq 1.4 is not strong enough;
                        the axiom can be removed once the library is converted to Flocq 2.0 *)
  forall (prec emax : Z) (Hprec : (0 < prec)%Z) (Hmax : (prec < emax)%Z)
    (m : Fappli_IEEE.mode) (x y : binary_float prec emax),
  B2R prec emax y <> 0%R ->
  if Rlt_bool (Rabs (round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m)
       (B2R prec emax x / B2R prec emax y))) (bpow radix2 emax)
  then
    B2R prec emax (Bdiv prec emax Hprec Hmax m x y) =
      round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (B2R prec emax x / B2R prec emax y) /\
    is_finite prec emax (Bdiv prec emax Hprec Hmax m x y) = is_finite prec emax x
  else
    B2FF prec emax (Bdiv prec emax Hprec Hmax m x y) =
      binary_overflow prec emax m (xorb (Bsign prec emax x) (Bsign prec emax y)).

Lemma div_single_specification :
  forall m (x y : single), single_value y <> R0 ->
  no_overflow_single m (single_value x / single_value y) ->
  exists z, div_single_post m x y z.
Proof.
intros m x y Zy Br.
refine (_ (Bdiv_correct 24 128 (refl_equal Lt) (refl_equal Lt) (rnd_of_mode m) (single_float x) (single_float y) Zy)).
rewrite Rlt_bool_true.
2: now apply no_overflow_single_bounded.
fold b32_div.
intros (H1, H2).
rewrite (single_finite x) in H2.
refine (ex_intro _ (mk_single (div_single m x y) H2) _).
repeat split.
exact H1.
Qed.

Axiom Bsqrt_correct : (* the statement from Flocq 1.4 is not strong enough;
                         the axiom can be removed once the library is converted to Flocq 2.0 *)
  forall (prec emax : Z) (Hprec : (0 < prec)%Z) (Hmax : (prec < emax)%Z)
         (m : Fappli_IEEE.mode) (x : binary_float prec emax),
  B2R prec emax (Bsqrt prec emax Hprec Hmax m x) =
    round radix2 (FLT_exp (3 - emax - prec) prec) (round_mode m) (sqrt (B2R prec emax x)) /\
  is_finite prec emax (Bsqrt prec emax Hprec Hmax m x) = match x with B754_zero _ => true | B754_finite false _ _ _ => true | _ => false end.

Lemma sqrt_single_specification :
  forall m (x : single), Rle 0 (single_value x) ->
  exists z, sqrt_single_post m x z.
Proof.
intros m x Zx.
refine (_ (Bsqrt_correct 24 128 (refl_equal Lt) (refl_equal Lt) (rnd_of_mode m) (single_float x))).
fold b32_sqrt.
intros (H1, H2).
assert (is_finite 24 128 (b32_sqrt (rnd_of_mode m) (single_float x)) = true).
rewrite H2.
revert Zx.
clear.
case x ; simpl.
intros (a,_,b,c) ; unfold single_value ; simpl.
destruct a as [| | |s m e H] ; try easy.
intros _.
case s ; try easy.
unfold B2R_coercion, B2R, F2R. simpl.
clear. intros H.
elim Rle_not_lt with (1 := H).
rewrite Ropp_mult_distr_l_reverse.
apply Ropp_lt_gt_0_contravar.
apply Rmult_gt_0_compat.
now apply (Z2R_lt 0 (Zpos m)).
apply bpow_gt_0.
refine (ex_intro _ (mk_single (sqrt_single m x) H) _).
repeat split.
exact H1.
Qed.

Lemma no_overflow_double_bounded :
  forall m x, no_overflow_double m x ->
  (Rabs (round_double m x) < bpow radix2 1024)%R.
Proof.
intros m x Bx.
apply Rle_lt_trans with (1 := Bx).
change 1024%Z with (53 + 971)%Z.
rewrite bpow_plus.
apply Rmult_lt_compat_r.
apply bpow_gt_0.
rewrite <- Z2R_Zpower.
now apply Z2R_lt.
easy.
Qed.

Lemma double_of_real_specification :
  forall m x, no_overflow_double m x ->
  exists z, double_of_real_post m x z.
Proof.
intros m x Bx.
refine (_ (r_to_sd_correct 53 1024 (refl_equal true) (refl_equal true) _ x (no_overflow_double_bounded _ x Bx))).
intros (H1, H2).
refine (let H := _ in ex_intro _ (mk_double (round_double_logic m x) H) _).
exact H1.
repeat split.
exact H2.
Qed.
