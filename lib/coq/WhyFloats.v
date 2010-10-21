
(* Why model for floating-point numbers
   Implements the file lib/why/floats.why *)

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
   sf         : R;
   Hcansf     : FLT_format radix2 (-149) 24 sf;
   s_to_exact : R;
   s_to_model : R
 }.

Definition s_to_r (f:single) := sf f.

Definition single_round_error (f:single):= 
    (Rabs ((s_to_exact f) - (s_to_r f))).

Definition single_total_error (f:single):= 
    (Rabs ((s_to_model f) - (s_to_r f))).

Definition single_set_model (f:single) (r:R) :=
      mk_single (sf f) (Hcansf f) (s_to_exact f) r.

Definition r_to_s_aux (m:mode) (r r1 r2:R) :=
  mk_single _ (r_to_sd_aux (-149) 24 (refl_equal _) (rnd_of_mode m) r) r1 r2.

Definition r_to_s (m:mode) (r:R) := r_to_s_aux m r r r.


Definition add_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (sf f1+sf f2) 
                  (s_to_exact f1+s_to_exact f2) (s_to_model f1+s_to_model f2).

Definition sub_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (sf f1-sf f2) 
                  (s_to_exact f1-s_to_exact f2) (s_to_model f1-s_to_model f2).

Definition mul_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (sf f1*sf f2) 
                  (s_to_exact f1*s_to_exact f2) (s_to_model f1*s_to_model f2).

Definition div_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (sf f1/sf f2) 
                  (s_to_exact f1/s_to_exact f2) (s_to_model f1/s_to_model f2).

Definition sqrt_single (m:mode) (f:single) :=
     r_to_s_aux m (sqrt (sf f))
                  (sqrt(s_to_exact f)) (sqrt(s_to_model f)).

Definition neg_single (m:mode) (f:single) :=
   mk_single _ (neg_sd_aux (-149) 24 (refl_equal _) (sf f) (Hcansf f))
         (-(s_to_exact f)) (-(s_to_model f)).

Definition abs_single (m:mode) (f:single) :=
   mk_single _ (abs_sd_aux (-149) 24 (refl_equal _) (sf f) (Hcansf f))
         (Rabs (s_to_exact f)) (Rabs (s_to_model f)).

(*
Definition max_single := ((2-powerRZ radix (-23))*powerRZ radix 127)%R.
*)

(** Double precision *)

Record double : Set := mk_double {
   df         : R;
   Hcandf     : FLT_format radix2 (-1074) 53 df;
   d_to_exact : R;
   d_to_model : R
 }.


Definition d_to_r (f:double) := df f.

Definition double_round_error (f:double):= 
    (Rabs ((d_to_exact f) - (d_to_r f))).

Definition double_total_error (f:double):= 
    (Rabs ((d_to_model f) - (d_to_r f))).

Definition double_set_model (f:double) (r:R) :=
      mk_double (df f) (Hcandf f) (d_to_exact f) r.

Definition r_to_d_aux (m:mode) (r r1 r2:R) :=
  mk_double _ (r_to_sd_aux (-1074) 53 (refl_equal _) (rnd_of_mode m) r) r1 r2.

Definition r_to_d (m:mode) (r:R) := r_to_d_aux m r r r.

Definition add_double (m:mode) (f1 f2:double) :=
     r_to_d_aux m (df f1+df f2) 
                  (d_to_exact f1+d_to_exact f2) (d_to_model f1+d_to_model f2).

Definition sub_double (m:mode) (f1 f2:double) :=
     r_to_d_aux m (df f1-df f2) 
                  (d_to_exact f1-d_to_exact f2) (d_to_model f1-d_to_model f2).

Definition mul_double (m:mode) (f1 f2:double) :=
     r_to_d_aux m (df f1*df f2) 
                  (d_to_exact f1*d_to_exact f2) (d_to_model f1*d_to_model f2).

Definition div_double (m:mode) (f1 f2:double) :=
     r_to_d_aux m (df f1/df f2) 
                  (d_to_exact f1/d_to_exact f2) (d_to_model f1/d_to_model f2).

Definition sqrt_double (m:mode) (f:double) :=
     r_to_d_aux m (sqrt (df f))
                  (sqrt(d_to_exact f)) (sqrt(d_to_model f)).

Definition neg_double (m:mode) (f:double) :=
   mk_double _ (neg_sd_aux (-1074) 53 (refl_equal _) (df f) (Hcandf f))
         (-(d_to_exact f)) (-(d_to_model f)).

Definition abs_double (m:mode) (f:double) :=
   mk_double _ (abs_sd_aux (-1074) 53 (refl_equal _) (df f) (Hcandf f))
         (Rabs (d_to_exact f)) (Rabs (d_to_model f)).

(*
Definition max_double := ((2-powerRZ radix (-52))*powerRZ radix 1023)%R.
*)

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

Lemma double_of_single_aux: forall f:single, 
  FLT_format radix2 (-1074) 53 (sf f).
Proof.
intros (f,((m,e),(H1,(H2,H3))),f1,f2). simpl.
unfold FLT_format.
eexists ; repeat split.
eexact H1.
apply Zlt_le_trans with (1 := H2).
apply le_Z2R.
rewrite 2!Z2R_Zpower ; try easy.
now apply bpow_le.
now apply Zle_trans with (2 := H3).
Qed.

Definition double_of_single (f:single) :=
   mk_double _ (double_of_single_aux f)
         (s_to_exact f) (s_to_model f).

Definition single_of_double (m:mode) (d:double) := r_to_s m (df d).

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
  (Zabs z <= Zpower_nat 2 53)%Z -> (d_to_r (r_to_d m (Z2R z))= Z2R z)%R.
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

Theorem zero_no_round: forall (m:mode), d_to_r (r_to_d m (Z2R 0)) = 0%R.
intros.
now rewrite small_int_no_round.
Qed.

Theorem one_no_round: forall (m:mode), d_to_r (r_to_d m (Z2R 1)) = 1%R.
intros.
now rewrite small_int_no_round.
Qed.

Theorem two_no_round: forall (m:mode), d_to_r (r_to_d m (Z2R 2)) = 2%R.
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
