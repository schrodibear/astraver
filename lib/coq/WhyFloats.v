
(* Why model for floating-point numbers
   Implements the file lib/why/floats_common.why *)

Require Export Reals.
Require Export Fcore.

Definition radix2 := Build_radix 2 (refl_equal _).

Inductive mode : Set := nearest_even | to_zero | up | down | nearest_away.

Lemma r_to_sd_aux :
  forall emin prec,
  Zlt_bool 0 prec = true ->
  forall rnd x,
  FLT_format radix2 emin prec (round radix2 (FLT_exp emin prec) rnd x).
Proof.
intros emin prec Hp rnd x.
apply <- FLT_format_generic.
apply generic_format_round.
apply FLT_exp_correct.
now apply <- Zlt_is_lt_bool.
now apply <- Zlt_is_lt_bool.
Qed.

Lemma neg_sd_aux :
  forall emin prec,
  Zlt_bool 0 prec = true ->
  forall x, FLT_format radix2 emin prec x ->
  FLT_format radix2 emin prec (-x)%R.
Proof.
intros emin prec Hp.
apply (FLT_format_satisfies_any radix2 emin prec).
now apply <- Zlt_is_lt_bool.
Qed.

Lemma abs_sd_aux :
  forall emin prec,
  Zlt_bool 0 prec = true ->
  forall x, FLT_format radix2 emin prec x ->
  FLT_format radix2 emin prec (Rabs x)%R.
Proof.
intros emin prec Hp x Hx.
apply <- FLT_format_generic.
apply generic_format_abs.
apply -> FLT_format_generic.
exact Hx.
now apply <- Zlt_is_lt_bool.
now apply <- Zlt_is_lt_bool.
Qed.

Definition rnd_of_mode (m:mode) :=
  match m with
  |  nearest_even => rndNE
  |  to_zero      => rndZR
  |  up           => rndUP
  |  down         => rndDN
  |  nearest_away => rndNA
  end.

(** Single precision *)

Record single : Set := mk_single {
  single_value : R;
  single_exact : R;
  single_model : R;
  single_value_in_format : FLT_format radix2 (-149) 24 single_value
}.

Definition single_round_error (f:single) :=
  Rabs (single_exact f - single_value f).

Definition single_total_error (f:single) :=
  Rabs (single_model f - single_value f).

Definition single_set_model (f:single) (r:R) :=
  mk_single (single_value f) (single_exact f) r (single_value_in_format f).

Definition r_to_s_aux (m:mode) (r r1 r2:R) :=
  mk_single _ r1 r2 (r_to_sd_aux (-149) 24 (refl_equal _) (rnd_of_mode m) r).

Definition round_single_logic (m:mode) (r:R) := r_to_s_aux m r r r.

Definition round_single (m:mode) (r:R) := round radix2 (FLT_exp (-149) 24) (rnd_of_mode m) r.

Definition add_single (m:mode) (f1 f2:single) :=
  r_to_s_aux m (single_value f1 + single_value f2)
    (single_exact f1 + single_exact f2) (single_model f1 + single_model f2).

Definition sub_single (m:mode) (f1 f2:single) :=
  r_to_s_aux m (single_value f1 - single_value f2)
    (single_exact f1 - single_exact f2) (single_model f1 - single_model f2).

Definition mul_single (m:mode) (f1 f2:single) :=
  r_to_s_aux m (single_value f1 * single_value f2)
    (single_exact f1 * single_exact f2) (single_model f1 * single_model f2).

Definition div_single (m:mode) (f1 f2:single) :=
  r_to_s_aux m (single_value f1 / single_value f2)
    (single_exact f1 / single_exact f2) (single_model f1 / single_model f2).

Definition sqrt_single (m:mode) (f:single) :=
  r_to_s_aux m (sqrt (single_value f)) (sqrt (single_exact f)) (sqrt (single_model f)).

Definition neg_single (m:mode) (f:single) :=
  mk_single _ (- single_exact f) (- single_model f)
    (neg_sd_aux (-149) 24 (refl_equal _) (single_value f) (single_value_in_format f)).

Definition abs_single (m:mode) (f:single) :=
  mk_single _ (Rabs (single_exact f)) (Rabs (single_model f))
    (abs_sd_aux (-149) 24 (refl_equal _) (single_value f) (single_value_in_format f)).

Definition any_single := round_single_logic nearest_even 0%R.

Definition max_single := F2R (Float radix2 16777215 104).

Definition no_overflow_single (m:mode) (x:R) := (Rabs (round_single m x) <= max_single)%R.

Theorem bounded_real_no_overflow_single :
  forall m x,
  (Rabs x <= max_single)%R ->
  no_overflow_single m x.
Proof.
intros m x Hx.
apply Rabs_le.
assert (generic_format radix2 (FLT_exp (-149) 24) max_single).
apply generic_format_canonic_exponent.
unfold canonic_exponent.
rewrite ln_beta_F2R. 2: easy.
rewrite (ln_beta_unique _ _ 24).
easy.
rewrite <- Z2R_abs, <- 2!Z2R_Zpower ; try easy.
split.
now apply Z2R_le.
now apply Z2R_lt.
generalize (Rabs_le_inv _ _ Hx).
split.
erewrite <- round_generic with (x := Ropp max_single).
apply round_monotone with (2 := proj1 H0).
now apply FLT_exp_correct.
now apply generic_format_opp.
rewrite <- round_generic with (rnd := rnd_of_mode m) (1 := H).
apply round_monotone with (2 := proj2 H0).
now apply FLT_exp_correct.
Qed.

Theorem round_single_monotonic :
  forall m x y, (x <= y)%R ->
  (round_single m x <= round_single m y)%R.
Proof.
intros m x y Hxy.
apply round_monotone with (2 := Hxy).
now apply FLT_exp_correct.
Qed.

Theorem round_single_idempotent :
  forall m1 m2 x,
  round_single m1 (round_single m2 x) = round_single m2 x.
Proof.
intros m1 m2 x.
apply round_generic.
apply generic_format_round.
now apply FLT_exp_correct.
Qed.

Theorem round_down_single_neg :
  forall x,
  round_single down (-x) = Ropp (round_single up x).
Proof.
intros x.
apply round_opp.
Qed.

Theorem round_up_single_neg :
  forall x,
  round_single up (-x) = Ropp (round_single down x).
Proof.
intros x.
pattern x at 2 ; rewrite <- Ropp_involutive.
rewrite round_down_single_neg.
now rewrite Ropp_involutive.
Qed.

Theorem round_single_down_le :
  forall x,
  (round_single down x <= x)%R.
Proof.
intros x.
eapply round_DN_pt.
now apply FLT_exp_correct.
Qed.

Theorem round_up_single_ge :
  forall x,
  (round_single up x >= x)%R.
Proof.
intros x.
apply Rle_ge.
eapply round_UP_pt.
now apply FLT_exp_correct.
Qed.

(** Double precision *)

Record double : Set := mk_double {
  double_value : R;
  double_exact : R;
  double_model : R;
  double_value_in_format : FLT_format radix2 (-1074) 53 double_value
}.

Definition double_round_error (f:double) :=
  Rabs (double_exact f - double_value f).

Definition double_total_error (f:double) :=
  Rabs (double_model f - double_value f).

Definition double_set_model (f:double) (r:R) :=
  mk_double (double_value f) (double_exact f) r (double_value_in_format f).

Definition r_to_d_aux (m:mode) (r r1 r2:R) :=
  mk_double _ r1 r2 (r_to_sd_aux (-1074) 53 (refl_equal _) (rnd_of_mode m) r).

Definition round_double_logic (m:mode) (r:R) := r_to_d_aux m r r r.

Definition round_double (m:mode) (r:R) := round radix2 (FLT_exp (-1074) 53) (rnd_of_mode m) r.

Definition add_double (m:mode) (f1 f2:double) :=
  r_to_d_aux m (double_value f1 + double_value f2)
    (double_exact f1 + double_exact f2) (double_model f1 + double_model f2).

Definition sub_double (m:mode) (f1 f2:double) :=
  r_to_d_aux m (double_value f1 - double_value f2)
    (double_exact f1 - double_exact f2) (double_model f1 - double_model f2).

Definition mul_double (m:mode) (f1 f2:double) :=
  r_to_d_aux m (double_value f1 * double_value f2)
    (double_exact f1 * double_exact f2) (double_model f1 * double_model f2).

Definition div_double (m:mode) (f1 f2:double) :=
  r_to_d_aux m (double_value f1 / double_value f2)
    (double_exact f1 / double_exact f2) (double_model f1 / double_model f2).

Definition sqrt_double (m:mode) (f:double) :=
  r_to_d_aux m (sqrt (double_value f)) (sqrt (double_exact f)) (sqrt (double_model f)).

Definition neg_double (m:mode) (f:double) :=
  mk_double _ (- double_exact f) (- double_model f)
    (neg_sd_aux (-1074) 53 (refl_equal _) (double_value f) (double_value_in_format f)).

Definition abs_double (m:mode) (f:double) :=
  mk_double _ (Rabs (double_exact f)) (Rabs (double_model f))
    (abs_sd_aux (-1074) 53 (refl_equal _) (double_value f) (double_value_in_format f)).

Definition any_double := round_double_logic nearest_even 0%R.

Definition max_double := F2R (Float radix2 9007199254740991 971).

Definition no_overflow_double (m:mode) (x:R) := (Rabs (round_double m x) <= max_double)%R.

Theorem bounded_real_no_overflow_double :
  forall m x,
  (Rabs x <= max_double)%R ->
  no_overflow_double m x.
Proof.
intros m x Hx.
apply Rabs_le.
assert (generic_format radix2 (FLT_exp (-1074) 53) max_double).
apply generic_format_canonic_exponent.
unfold canonic_exponent.
rewrite ln_beta_F2R. 2: easy.
rewrite (ln_beta_unique _ _ 53).
easy.
rewrite <- Z2R_abs, <- 2!Z2R_Zpower ; try easy.
split.
now apply Z2R_le.
now apply Z2R_lt.
generalize (Rabs_le_inv _ _ Hx).
split.
erewrite <- round_generic with (x := Ropp max_double).
apply round_monotone with (2 := proj1 H0).
now apply FLT_exp_correct.
now apply generic_format_opp.
rewrite <- round_generic with (rnd := rnd_of_mode m) (1 := H).
apply round_monotone with (2 := proj2 H0).
now apply FLT_exp_correct.
Qed.

Theorem round_double_monotonic :
  forall m x y, (x <= y)%R ->
  (round_double m x <= round_double m y)%R.
Proof.
intros m x y Hxy.
apply round_monotone with (2 := Hxy).
now apply FLT_exp_correct.
Qed.

Theorem round_double_idempotent :
  forall m1 m2 x,
  round_double m1 (round_double m2 x) = round_double m2 x.
Proof.
intros m1 m2 x.
apply round_generic.
apply generic_format_round.
now apply FLT_exp_correct.
Qed.

Theorem round_down_double_neg :
  forall x,
  round_double down (-x) = Ropp (round_double up x).
Proof.
intros x.
apply round_opp.
Qed.

Theorem round_up_double_neg :
  forall x,
  round_double up (-x) = Ropp (round_double down x).
Proof.
intros x.
pattern x at 2 ; rewrite <- Ropp_involutive.
rewrite round_down_double_neg.
now rewrite Ropp_involutive.
Qed.

Theorem round_double_down_le :
  forall x,
  (round_double down x <= x)%R.
Proof.
intros x.
eapply round_DN_pt.
now apply FLT_exp_correct.
Qed.

Theorem round_up_double_ge :
  forall x,
  (round_double up x >= x)%R.
Proof.
intros x.
apply Rle_ge.
eapply round_UP_pt.
now apply FLT_exp_correct.
Qed.

(** Quad precision *)

Definition quad: Set.
Admitted.

Definition add_quad : mode -> quad -> quad -> quad.
Admitted.

Definition sub_quad : mode -> quad -> quad -> quad.
Admitted.

Definition mul_quad : mode -> quad -> quad -> quad.
Admitted.

Definition div_quad : mode -> quad -> quad -> quad.
Admitted.

Definition neg_quad : mode -> quad -> quad.
Admitted.

Definition abs_quad : mode -> quad -> quad.
Admitted.

Definition sqrt_quad : mode -> quad -> quad.
Admitted.

Definition q_to_r : quad -> R.
Admitted.

Definition q_to_exact : quad -> R.
Admitted.

Definition q_to_model : quad -> R.
Admitted.

Definition r_to_q : mode -> R -> quad.
Admitted.

Definition quad_round_error : quad -> R.
Admitted.

Definition quad_total_error : quad -> R.
Admitted.

Definition quad_set_model : quad -> R -> quad.
Admitted.

Definition max_quad : R.
Admitted.


(** Jumping from one format to another *)

Lemma single_to_double_aux: forall f:single, 
  FLT_format radix2 (-1074) 53 (single_value f).
Proof.
intros (f,f1,f2,((m,e),(H1,(H2,H3)))). simpl.
eexists ; repeat split.
eexact H1.
apply Zlt_le_trans with (1 := H2).
apply le_Z2R.
rewrite 2!Z2R_Zpower ; try easy.
now apply bpow_le.
now apply Zle_trans with (2 := H3).
Qed.

Definition single_to_double (f:single) :=
  mk_double _ (single_exact f) (single_model f) (single_to_double_aux f).

Definition double_to_single (m:mode) (d:double) :=
 r_to_s_aux m (double_value d) (double_exact d) (double_model d).

Theorem single_to_double_val :
  forall f,
  double_value (single_to_double f) = single_value f.
Proof.
intros f.
apply refl_equal.
Qed.

Theorem double_to_single_val :
  forall m f,
  single_value (double_to_single m f) = round_single m (double_value f).
Proof.
intros m f.
apply refl_equal.
Qed.

Definition single_of_double (m:mode) (d:double) := round_single m (double_value d).

Definition quad_of_single : single -> quad.
Admitted.

Definition single_of_quad : mode -> quad -> single.
Admitted.

Definition quad_of_double : double -> quad.
Admitted.

Definition double_of_quad : mode -> quad -> double.
Admitted.


(** Small integers, like 1 or 2, do not suffer from rounding *)

Theorem small_int_no_round: forall (m:mode), forall (z:Z), 
  (Zabs z <= Zpower_nat 2 53)%Z -> (double_value (round_double_logic m (Z2R z))= Z2R z)%R.
Proof.
intros m z Hz.
simpl.
destruct (Z_eq_dec z 0) as [Zz|Zz].
rewrite Zz.
apply round_0.
apply round_generic.
destruct (Zle_lt_or_eq _ _ Hz) as [Bz|Bz].
rewrite <- (Rmult_1_r (Z2R z)).
change (Z2R z * 1)%R with (F2R (Float radix2 z 0)).
apply generic_format_canonic_exponent.
unfold F2R. simpl.
rewrite Rmult_1_r.
unfold canonic_exponent.
destruct (ln_beta radix2 (Z2R z)) as (ez,Ez). simpl.
specialize (Ez (Z2R_neq _ _ Zz)).
unfold FLT_exp.
generalize (Zmax_spec (ez - 53) (-1074)).
cut (1 <= ez <= 53)%Z. clear. omega.
split.
apply (bpow_lt_bpow radix2).
apply Rle_lt_trans with (2 := proj2 Ez).
rewrite <- Z2R_abs.
apply (Z2R_le 1).
clear -Zz.
generalize (Zabs_spec z). omega.
apply (bpow_lt_bpow radix2).
apply Rle_lt_trans with (1 := proj1 Ez).
change 53%Z with (Z_of_nat 53).
rewrite <- Z2R_Zpower_nat.
rewrite <- Z2R_abs.
now apply Z2R_lt.
destruct z.
now elim Zz.
simpl in Bz.
rewrite Bz.
rewrite (Z2R_Zpower_nat radix2).
now apply generic_format_bpow.
simpl in Bz.
change (Zneg p) with (Zopp (Zpos p)).
rewrite Bz.
rewrite Z2R_opp.
apply generic_format_opp.
rewrite (Z2R_Zpower_nat radix2).
now apply generic_format_bpow.
Qed.

Theorem zero_no_round: forall (m:mode), double_value (round_double_logic m (Z2R 0)) = 0%R.
intros.
now rewrite small_int_no_round.
Qed.

Theorem one_no_round: forall (m:mode), double_value (round_double_logic m (Z2R 1)) = 1%R.
intros.
now rewrite small_int_no_round.
Qed.

Theorem two_no_round: forall (m:mode), double_value (round_double_logic m (Z2R 2)) = 2%R.
intros.
now rewrite small_int_no_round.
Qed.

(*
Theorem max_single_pos: (0 < max_single)%R.
unfold max_single.
apply Rle_lt_trans with (0*powerRZ radix 127)%R;[right; ring|apply Rmult_lt_compat_r; auto with real zarith].
apply Rplus_lt_reg_r with (powerRZ radix (-23)); ring_simplify.
apply Rlt_le_trans with (powerRZ radix 1); auto with real zarith.
apply Rlt_powerRZ; unfold radix; simpl; auto with real zarith.
Qed.


Theorem max_double_pos: (0 < max_double)%R.
unfold max_double.
apply Rle_lt_trans with (0*powerRZ radix 1023)%R;[right; ring|apply Rmult_lt_compat_r; auto with real zarith].
apply Rplus_lt_reg_r with (powerRZ radix (-52)); ring_simplify.
apply Rlt_le_trans with (powerRZ radix 1); auto with real zarith.
apply Rlt_powerRZ; unfold radix; simpl; auto with real zarith.
Qed.
*)
