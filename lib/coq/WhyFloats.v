
(* Why model for floating-point numbers
   Implements the file lib/why/floats_common.why *)

Require Export Reals.
Require Export Fcore.
Require Export Fappli_IEEE.
Require Export Fappli_IEEE_bits.

Inductive mode : Set := nearest_even | to_zero | up | down | nearest_away.

Global Coercion B2R_coercion prec emax := @B2R prec emax.

Section r_to_sd.

Variable prec emax : Z.
Hypothesis Hprec : Zlt_bool 0 prec = true.
Hypothesis Hemax : Zlt_bool prec emax = true.
Let emin := (3 - emax - prec)%Z.
Notation fexp := (FLT_exp emin prec).

Lemma Hprec': (0 < prec)%Z. revert Hprec. now case Zlt_bool_spec. Qed.
Lemma Hemax': (prec < emax)%Z. revert Hemax. now case Zlt_bool_spec. Qed.

Instance Hprec'' : Prec_gt_0 prec := Hprec'.

Definition r_to_sd rnd x : binary_float prec emax :=
  let r := round radix2 fexp (round_mode rnd) x in
  let m := Ztrunc (scaled_mantissa radix2 fexp r) in
  let e := canonic_exp radix2 fexp r in
  binary_normalize prec emax Hprec' Hemax' rnd m e false.

Lemma is_finite_FF2B :
  forall f H,
  is_finite prec emax (FF2B prec emax f H) =
    match f with
    | F754_finite _ _ _ => true
    | F754_zero _ => true
    | _ => false
    end.
Proof.
now intros [| | |].
Qed.

Theorem r_to_sd_correct :
  forall rnd x,
  let r := round radix2 fexp (round_mode rnd) x in
  (Rabs r < bpow radix2 emax)%R ->
  is_finite prec emax (r_to_sd rnd x) = true /\
  r_to_sd rnd x = r :>R.
Proof with auto with typeclass_instances.
intros rnd x r Bx.
unfold r_to_sd. fold r.
generalize (binary_normalize_correct prec emax Hprec' Hemax' rnd (Ztrunc (scaled_mantissa radix2 fexp r)) (canonic_exp radix2 fexp r) false).
unfold r.
elim generic_format_round...
fold emin r.
rewrite round_generic...
rewrite Rlt_bool_true with (1 := Bx).
now split.
apply generic_format_round...
Qed.

Theorem r_to_sd_format :
  forall rnd x,
  FLT_format radix2 emin prec x ->
  (Rabs x < bpow radix2 emax)%R ->
  r_to_sd rnd x = x :>R.
Proof with auto with typeclass_instances.
intros rnd x Fx Bx.
assert (Gx: generic_format radix2 fexp x).
apply generic_format_FLT.
apply Fx.
pattern x at 2 ; rewrite <- round_generic with (rnd := round_mode rnd) (2 := Gx)...
refine (proj2 (r_to_sd_correct _ _ _)).
rewrite round_generic...
Qed.

End r_to_sd.

Theorem value_is_bounded :
  forall prec emax (v : binary_float (Zpos prec) emax),
  (Rabs v <= F2R (Float radix2 (Zpower_pos 2 prec - 1) (emax - Zpos  prec)))%R.
Proof.
intros prec emax v.
assert (Rabs 0 <= F2R (Float radix2 (Zpower_pos 2 prec - 1) (emax - Zpos prec)))%R.
rewrite Rabs_R0.
rewrite <- (F2R_0 radix2 (emax - Zpos prec)).
apply F2R_le_compat.
apply Zlt_succ_le.
change (0 < Zsucc (Zpred (Zpower_pos 2 prec)))%Z.
rewrite <- Zsucc_pred.
now apply Zpower_pos_gt_0.
destruct v ; try exact H.
clear H.
unfold B2R_coercion, B2R, F2R. simpl.
rewrite Rabs_mult, <- Z2R_abs, abs_cond_Zopp.
rewrite Rabs_pos_eq.
2: apply bpow_ge_0.
destruct (andb_prop _ _ e0) as (H1, H2).
apply Rmult_le_compat.
now apply (Z2R_le 0).
apply bpow_ge_0.
apply Z2R_le.
apply Zlt_succ_le.
change (Zpos m < Zsucc (Zpred (Zpower_pos 2 prec)))%Z.
rewrite <- Zsucc_pred.
generalize (Zeq_bool_eq _ _ H1). clear.
rewrite Fcalc_digits.Z_of_nat_S_digits2_Pnat.
intros H.
apply (Fcalc_digits.Zpower_gt_Zdigits Fcalc_digits.radix2 (Zpos prec) (Zpos m)).
revert H.
unfold FLT_exp.
generalize (Fcore_digits.Zdigits radix2 (Zpos m)).
intros ; zify ; omega.
apply bpow_le.
now apply Zle_bool_imp_le.
Qed.

Definition rnd_of_mode (m:mode) :=
  match m with
  |  nearest_even => mode_NE
  |  to_zero      => mode_ZR
  |  up           => mode_UP
  |  down         => mode_DN
  |  nearest_away => mode_NA
  end.

(** Single precision *)

Record single : Set := mk_single {
  single_float : binary32;
  single_value := (single_float : R);
  single_exact : R;
  single_model : R
}.

Definition single_round_error (f:single) :=
  Rabs (single_exact f - single_value f).

Definition single_total_error (f:single) :=
  Rabs (single_model f - single_value f).

Definition single_set_model (f:single) (r:R) :=
  mk_single (single_float f) (single_exact f) r.

Definition r_to_s_aux (m:mode) (r r1 r2:R) :=
  mk_single (r_to_sd 24 128 (refl_equal true) (refl_equal true) (rnd_of_mode m) r) r1 r2.

Definition round_single_logic (m:mode) (r:R) := r_to_s_aux m r r r.

Definition round_single (m:mode) (r:R) := round radix2 (FLT_exp (-149) 24) (round_mode (rnd_of_mode m)) r.

Definition add_single (m:mode) (f1 f2:single) :=
  mk_single (b32_plus (rnd_of_mode m) (single_float f1) (single_float f2))
    (single_exact f1 + single_exact f2) (single_model f1 + single_model f2).

Definition sub_single (m:mode) (f1 f2:single) :=
  mk_single (b32_minus (rnd_of_mode m) (single_float f1) (single_float f2))
    (single_exact f1 - single_exact f2) (single_model f1 - single_model f2).

Definition mul_single (m:mode) (f1 f2:single) :=
  mk_single (b32_mult (rnd_of_mode m) (single_float f1) (single_float f2))
    (single_exact f1 * single_exact f2) (single_model f1 * single_model f2).

Definition div_single (m:mode) (f1 f2:single) :=
  mk_single (b32_div (rnd_of_mode m) (single_float f1) (single_float f2))
    (single_exact f1 / single_exact f2) (single_model f1 / single_model f2).

Definition sqrt_single (m:mode) (f:single) :=
  mk_single (b32_sqrt (rnd_of_mode m) (single_float f))
    (sqrt (single_exact f)) (sqrt (single_model f)).

Definition neg_single (f:single) :=
  mk_single (b32_opp (single_float f))
    (- single_exact f) (- single_model f).

Definition any_single := round_single_logic nearest_even 0%R.

Definition max_single := F2R (Float radix2 16777215 104).

Definition no_overflow_single (m:mode) (x:R) := (Rabs (round_single m x) <= max_single)%R.

Instance single_prec_gt_0 : Prec_gt_0 24. easy. Qed.

Theorem bounded_real_no_overflow_single :
  forall m x,
  (Rabs x <= max_single)%R ->
  no_overflow_single m x.
Proof with auto with typeclass_instances.
intros m x Hx.
apply Rabs_le.
assert (generic_format radix2 (FLT_exp (-149) 24) max_single).
apply generic_format_F2R.
intros _.
unfold canonic_exp.
rewrite ln_beta_F2R. 2: easy.
rewrite (ln_beta_unique _ _ 24).
easy.
rewrite <- Z2R_abs, <- 2!Z2R_Zpower ; try easy.
split.
now apply Z2R_le.
now apply Z2R_lt.
generalize (Rabs_le_inv _ _ Hx).
split.
apply round_ge_generic...
now apply generic_format_opp.
apply H0.
apply round_le_generic...
apply H0.
Qed.

Theorem round_single_monotonic :
  forall m x y, (x <= y)%R ->
  (round_single m x <= round_single m y)%R.
Proof with auto with typeclass_instances.
intros m x y Hxy.
apply round_le...
Qed.

Theorem round_single_idempotent :
  forall m1 m2 x,
  round_single m1 (round_single m2 x) = round_single m2 x.
Proof with auto with typeclass_instances.
intros m1 m2 x.
apply round_generic...
apply generic_format_round...
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
Proof with auto with typeclass_instances.
intros x.
apply round_DN_pt...
Qed.

Theorem round_up_single_ge :
  forall x,
  (round_single up x >= x)%R.
Proof with auto with typeclass_instances.
intros x.
apply Rle_ge.
apply round_UP_pt...
Qed.

(** Double precision *)

Record double : Set := mk_double {
  double_float : binary64;
  double_value := (double_float : R);
  double_exact : R;
  double_model : R
}.

Definition double_round_error (f:double) :=
  Rabs (double_exact f - double_value f).

Definition double_total_error (f:double) :=
  Rabs (double_model f - double_value f).

Definition double_set_model (f:double) (r:R) :=
  mk_double (double_float f) (double_exact f) r.

Definition r_to_d_aux (m:mode) (r r1 r2:R) :=
  mk_double (r_to_sd 53 1024 (refl_equal true) (refl_equal true) (rnd_of_mode m) r) r1 r2.

Definition round_double_logic (m:mode) (r:R) := r_to_d_aux m r r r.

Definition round_double (m:mode) (r:R) := round radix2 (FLT_exp (-1074) 53) (round_mode (rnd_of_mode m)) r.

Definition add_double (m:mode) (f1 f2:double) :=
  mk_double (b64_plus (rnd_of_mode m) (double_float f1) (double_float f2))
    (double_exact f1 + double_exact f2) (double_model f1 + double_model f2).

Definition sub_double (m:mode) (f1 f2:double) :=
  mk_double (b64_minus (rnd_of_mode m) (double_float f1) (double_float f2))
    (double_exact f1 - double_exact f2) (double_model f1 - double_model f2).

Definition mul_double (m:mode) (f1 f2:double) :=
  mk_double (b64_mult (rnd_of_mode m) (double_float f1) (double_float f2))
    (double_exact f1 * double_exact f2) (double_model f1 * double_model f2).

Definition div_double (m:mode) (f1 f2:double) :=
  mk_double (b64_div (rnd_of_mode m) (double_float f1) (double_float f2))
    (double_exact f1 / double_exact f2) (double_model f1 / double_model f2).

Definition sqrt_double (m:mode) (f:double) :=
  mk_double (b64_sqrt (rnd_of_mode m) (double_float f))
    (sqrt (double_exact f)) (sqrt (double_model f)).

Definition neg_double (f:double) :=
  mk_double (b64_opp (double_float f))
    (- double_exact f) (- double_model f).

Definition any_double := round_double_logic nearest_even 0%R.

Definition max_double := F2R (Float radix2 9007199254740991 971).

Definition no_overflow_double (m:mode) (x:R) := (Rabs (round_double m x) <= max_double)%R.

Instance double_prec_gt_0 : Prec_gt_0 53. easy. Qed.

Theorem bounded_real_no_overflow_double :
  forall m x,
  (Rabs x <= max_double)%R ->
  no_overflow_double m x.
Proof with auto with typeclass_instances.
intros m x Hx.
apply Rabs_le.
assert (generic_format radix2 (FLT_exp (-1074) 53) max_double).
apply generic_format_F2R.
intros _.
unfold canonic_exp.
rewrite ln_beta_F2R. 2: easy.
rewrite (ln_beta_unique _ _ 53).
easy.
rewrite <- Z2R_abs, <- 2!Z2R_Zpower ; try easy.
split.
now apply Z2R_le.
now apply Z2R_lt.
generalize (Rabs_le_inv _ _ Hx).
split.
apply round_ge_generic...
now apply generic_format_opp.
apply H0.
apply round_le_generic...
apply H0.
Qed.

Theorem round_double_monotonic :
  forall m x y, (x <= y)%R ->
  (round_double m x <= round_double m y)%R.
Proof with auto with typeclass_instances.
intros m x y Hxy.
apply round_le...
Qed.

Theorem round_double_idempotent :
  forall m1 m2 x,
  round_double m1 (round_double m2 x) = round_double m2 x.
Proof with auto with typeclass_instances.
intros m1 m2 x.
apply round_generic...
apply generic_format_round...
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
Proof with auto with typeclass_instances.
intros x.
apply round_DN_pt...
Qed.

Theorem round_up_double_ge :
  forall x,
  (round_double up x >= x)%R.
Proof with auto with typeclass_instances.
intros x.
apply Rle_ge.
apply round_UP_pt...
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

(*
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
*)

(** Small integers, like 1 or 2, do not suffer from rounding *)

Theorem small_int_no_round: forall (m:mode), forall (z:Z), 
  (Zabs z <= Zpower_nat 2 53)%Z -> (double_value (round_double_logic m (Z2R z))= Z2R z)%R.
Proof with auto with typeclass_instances.
intros m z Hz.
unfold round_double_logic, r_to_d_aux, double_value.
apply r_to_sd_format.
destruct (Zle_lt_or_eq _ _ Hz) as [Bz|Bz] ; clear Hz.
exists (Float radix2 z 0).
unfold F2R. simpl.
split.
now rewrite Rmult_1_r.
now split.
apply FLT_format_generic...
apply generic_format_abs_inv.
rewrite <- Z2R_abs, Bz.
change (Zpower_nat 2 53) with (Zpower_nat radix2 (Zabs_nat 53)).
rewrite <- Zpower_Zpower_nat, Z2R_Zpower by easy.
now apply generic_format_bpow.
apply Rle_lt_trans with (bpow radix2 53).
rewrite <- Z2R_abs.
change 53%Z with (Z_of_nat 53).
rewrite <- Z2R_Zpower_nat.
now apply Z2R_le.
now apply bpow_lt.
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
