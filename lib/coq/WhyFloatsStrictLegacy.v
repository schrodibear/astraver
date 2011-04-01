(* Why model for floating-point numbers
   Implements the file lib/why/floats_strict.why *)

Require Export Reals.
Require Export AllFloat.
Require Export RND.

Let radix := 2%Z.
Coercion Local FtoRradix := FtoR radix.

Section Z2R.

Fixpoint P2R (p : positive) :=
  match p with
  | xH => 1%R
  | xO xH => 2%R
  | xO t => (2 * P2R t)%R
  | xI xH => 3%R
  | xI t => (1 + 2 * P2R t)%R
  end.

Definition Z2R n :=
  match n with
  | Zpos p => P2R p
  | Zneg p => Ropp (P2R p)
  | Z0 => R0
  end.

Lemma P2R_INR :
  forall n, P2R n = INR (nat_of_P n).
Proof.
induction n ; simpl ; try (
  rewrite IHn ;
  rewrite <- (mult_INR 2) ;
  rewrite <- (nat_of_P_mult_morphism 2) ;
  change (2 * n)%positive with (xO n)).
(* xI *)
rewrite (Rplus_comm 1).
change (nat_of_P (xO n)) with (Pmult_nat n 2).
case n ; intros ; simpl ; try apply refl_equal.
case (Pmult_nat p 4) ; intros ; try apply refl_equal.
rewrite Rplus_0_l.
apply refl_equal.
apply Rplus_comm.
(* xO *)
case n ; intros ; apply refl_equal.
(* xH *)
apply refl_equal.
Qed.


Lemma Z2R_IZR :
  forall n, Z2R n = IZR n.
Proof.
intro.
case n ; intros ; simpl.
apply refl_equal.
apply P2R_INR.
apply Ropp_eq_compat.
apply P2R_INR.
Qed.

End Z2R.

Section Utiles.

Lemma radixGreaterOne: (1 < radix)%Z.
auto with zarith.
Qed.


Definition nat_to_N (n:nat) := match n with 
   |  0    => N0
   | (S m) => (Npos (P_of_succ_nat m))
   end.

Lemma nat_to_N_correct: forall n:nat, Z_of_N (nat_to_N n)=n.
intros.
intros; induction n; simpl; auto.
Qed.


Definition make_bound (p E:nat) := Bound 
      (P_of_succ_nat (pred (Zabs_nat (Zpower_nat radix p))))
      (nat_to_N E).

Lemma make_EGivesEmin: forall p E:nat, 
        (Z_of_N (dExp (make_bound p E)))=E.
intros; simpl; apply nat_to_N_correct.
Qed.

Lemma make_pGivesBound: forall p E:nat, 
        Zpos (vNum (make_bound p E))=(Zpower_nat radix p).
intros.
unfold make_bound, vNum.
apply
 trans_eq
  with
    (Z_of_nat
       (nat_of_P
          (P_of_succ_nat
             (pred (Zabs_nat (Zpower_nat radix p)))))).
unfold Z_of_nat in |- *; rewrite nat_of_P_o_P_of_succ_nat_eq_succ;
 auto with zarith.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith zarith.
cut (Zabs (Zpower_nat radix p) = Zpower_nat radix p).
intros H; pattern (Zpower_nat radix p) at 2 in |- *; rewrite <- H.
rewrite Zabs_absolu.
rewrite <- (S_pred (Zabs_nat (Zpower_nat radix p)) 0);
 auto with arith zarith.
apply lt_Zlt_inv; simpl in |- *; auto with zarith arith.
rewrite <- Zabs_absolu; rewrite H; auto with arith zarith.
apply Zabs_eq; auto with arith zarith.
Qed.


Lemma Rmult_eq_compat: forall p1 p2 q1 q2,
  p1=p2 -> q1 = q2 -> (p1*q1=p2*q2)%R.
intros; rewrite H; rewrite H0; trivial.
Qed.

End Utiles.

Inductive mode : Set :=
  | nearest_even : mode
  | to_zero : mode
  | up : mode
  | down : mode
  | nearest_away : mode.

(** Double precision: definitions *)

Let bdouble := make_bound 53 1074.

Lemma pdGreaterThanOne: 1 < 53.
auto with arith.
Qed.

Lemma pdGivesBound: Zpos (vNum bdouble) = Zpower_nat radix 53.
unfold bdouble; apply make_pGivesBound.
Qed.

Record double : Set := mk_double {
   df         : float;
   Hcandf       : Fcanonic radix bdouble df;
   double_exact : R;
   double_model : R
 }.

Definition double_value (f:double) := FtoRradix (df f).


Definition round_double_aux (m:mode) (r r1 r2:R) := match m with
  |  nearest_even => mk_double (RND_EvenClosest bdouble radix 53 r) 
                     (RND_EvenClosest_canonic bdouble radix 53 
                         radixGreaterOne pdGreaterThanOne pdGivesBound r)
                     r1 r2
  |  to_zero      => mk_double (RND_Zero bdouble radix 53 r) 
                     (RND_Zero_canonic bdouble radix 53 
                         radixGreaterOne pdGreaterThanOne pdGivesBound r)
                     r1 r2
  |  down           => mk_double (RND_Min bdouble radix 53 r) 
                     (RND_Min_canonic bdouble radix 53 
                         radixGreaterOne pdGreaterThanOne pdGivesBound r)
                     r1 r2
  |  up         => mk_double (RND_Max bdouble radix 53 r) 
                     (RND_Max_canonic bdouble radix 53 
                         radixGreaterOne pdGreaterThanOne pdGivesBound r)
                     r1 r2
  |  nearest_away => mk_double (RND_ClosestUp bdouble radix 53 r) 
                     (RND_ClosestUp_canonic bdouble radix 53 
                         radixGreaterOne pdGreaterThanOne pdGivesBound r)
                     r1 r2
  end.
   
Definition round_double_logic (m:mode) (r:R) :=  round_double_aux m r r r.
Definition round_double (m:mode) (r:R) := double_value (round_double_aux m r r r).

Definition double_round_error  (x:double)
  := (Rabs (Rminus (double_value x) (double_exact x))).

Definition double_total_error  (x:double)
  := (Rabs (Rminus (double_value x) (double_model x))).

Definition any_double := round_double_logic nearest_even 0%R.

Definition max_double  
  := (9007199254740991 * 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848)%R.

Definition no_overflow_double  (m:mode) (x:R)
  := (Rle (Rabs (round_double m x)) max_double).


(** Single precision: definitions *)

Let bsingle := make_bound 24 149.

Lemma psGreaterThanOne: 1 < 24.
auto with arith.
Qed.

Lemma psGivesBound: Zpos (vNum bsingle) = Zpower_nat radix 24.
unfold bsingle; apply make_pGivesBound.
Qed.

Record single : Set := mk_single {
   sf           : float;
   Hcansf         : Fcanonic radix bsingle sf;
   single_exact : R;
   single_model : R
 }.

Definition single_value (f:single) := FtoRradix (sf f).

Definition round_single_aux (m:mode) (r r1 r2:R) := match m with
  |  nearest_even => mk_single (RND_EvenClosest bsingle radix 24 r) 
                     (RND_EvenClosest_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  to_zero      => mk_single (RND_Zero bsingle radix 24 r) 
                     (RND_Zero_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  up           => mk_single (RND_Max bsingle radix 24 r) 
                     (RND_Max_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  down         => mk_single (RND_Min bsingle radix 24 r) 
                     (RND_Min_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  nearest_away => mk_single (RND_ClosestUp bsingle radix 24 r) 
                     (RND_ClosestUp_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  end.


Definition round_single_logic (m:mode) (r:R) :=  round_single_aux m r r r.
Definition round_single (m:mode) (r:R) := single_value (round_single_aux m r r r).


Definition single_round_error  (x:single)
  := (Rabs (Rminus (single_value x) (single_exact x))).

Definition single_total_error  (x:single)
  := (Rabs (Rminus (single_value x) (single_model x))).

Definition max_single  
  := (33554430 * 10141204801825835211973625643008)%R.

Definition any_single  := round_single_logic nearest_even 0%R.

Definition no_overflow_single  (m:mode) (x:R)
  := (Rle (Rabs (round_single m x)) max_single).


Definition single_to_double (m:mode) (s:single) :=
 round_double_aux m (single_value s) (single_exact s) (single_model s).

Definition double_to_single (m:mode) (d:double) :=
 round_single_aux m (double_value d) (double_exact d) (double_model d).

(* Double and Single precision: axioms *)

Axiom double_le_strict: forall (s:double), 
   (Rabs (double_value s) <= max_double)%R.

Axiom single_le_strict: forall (s:single), 
   (Rabs (single_value s) <= max_single)%R.

(* Double precision: lemmas *)

Lemma mode_double_RoundingMode: forall m, exists P, RoundedModeP bdouble radix P /\
  forall x y z, P x (df (round_double_aux m x y z)).
intros m; case m; simpl.
exists (EvenClosest bdouble radix 53); split.
apply EvenClosestRoundedModeP; try apply pdGivesBound; auto with zarith.
intros; apply RND_EvenClosest_correct; try apply pdGivesBound; auto with zarith.
exists (ToZeroP bdouble radix); split.
apply ToZeroRoundedModeP with 53; try apply pdGivesBound; auto with zarith.
intros; apply RND_Zero_correct; try apply pdGivesBound; auto with zarith.
exists (isMax bdouble radix); split.
apply MaxRoundedModeP with 53; try apply pdGivesBound; auto with zarith.
intros; apply RND_Max_correct; try apply pdGivesBound; auto with zarith.
exists (isMin bdouble radix); split.
apply MinRoundedModeP with 53; try apply pdGivesBound; auto with zarith.
intros; apply RND_Min_correct; try apply pdGivesBound; auto with zarith.
exists (Closest bdouble radix); split.
apply ClosestRoundedModeP with 53; try apply pdGivesBound; auto with zarith.
intros; apply RND_ClosestUp_correct; try apply pdGivesBound; auto with zarith.
Qed.


Lemma max_double_bounded:
  exists f:float, Fbounded bdouble f /\ FtoRradix f = max_double.
exists (Float 9007199254740991 971); split.
split.
rewrite pdGivesBound; simpl; auto with zarith.
simpl; auto with zarith.
unfold max_double.
unfold FtoRradix, FtoR.
simpl (Fnum (Float 9007199254740991 971)); simpl  (Fexp (Float 9007199254740991 971)).
apply Rmult_eq_compat.
rewrite <- Z2R_IZR.
reflexivity.
replace 971%Z with (Z_of_nat 971) by reflexivity.
rewrite <- Zpower_nat_Z_powerRZ.
unfold Zpower_nat.
simpl (iter_nat 971 Z (fun x : Z => (radix * x)%Z) 1%Z).
rewrite <- Z2R_IZR.
reflexivity.
Qed.


Lemma bounded_real_no_overflow_double :
  (forall (m:mode),
   (forall (x:R), ((Rle (Rabs x) max_double) -> (no_overflow_double m x)))).
unfold no_overflow_double; intros.
elim (mode_double_RoundingMode m); intros P (H1,H2).
elim max_double_bounded; intros f (H3,H4).
rewrite <- H4.
apply RoundAbsMonotoner with bdouble 53 P x; try apply pdGivesBound; auto with zarith.
fold FtoRradix; rewrite H4; trivial.
Qed.

Lemma round_double_down_le :
  (forall (x:R), (Rle (round_double down x) x)).
intros; apply isMin_inv1 with bdouble.
simpl; apply RND_Min_correct; try apply pdGivesBound; auto with zarith.
Qed.

Lemma round_up_double_ge :
  (forall (x:R), (Rge (round_double up x) x)).
intros; apply Rle_ge; apply isMax_inv1 with bdouble.
simpl; apply RND_Max_correct; try apply pdGivesBound; auto with zarith.
Qed.

Lemma round_down_double_neg :
  (forall (x:R), (eq (round_double down (Ropp x)) (Ropp (round_double up x)))).
intros.
unfold round_double, double_value, FtoRradix; simpl.
rewrite <- Fopp_correct.
generalize (MinUniqueP bdouble radix); unfold UniqueP.
intros T; apply T with (-x)%R.
apply RND_Min_correct; try apply pdGivesBound; auto with zarith.
apply MaxOppMin.
apply RND_Max_correct; try apply pdGivesBound; auto with zarith.
Qed.

Lemma round_up_double_neg :
  (forall (x:R), (eq (round_double up (Ropp x)) (Ropp (round_double down x)))).
intros.
unfold round_double, double_value, FtoRradix; simpl.
rewrite <- Fopp_correct.
generalize (MaxUniqueP bdouble radix); unfold UniqueP.
intros T; apply T with (-x)%R.
apply RND_Max_correct; try apply pdGivesBound; auto with zarith.
apply MinOppMax.
apply RND_Min_correct; try apply pdGivesBound; auto with zarith.
Qed.

Lemma round_double_idempotent :
  (forall (m1:mode),
   (forall (m2:mode),
    (forall (x:R),
     (eq (round_double m1 (round_double m2 x)) (round_double m2 x))))).
intros.
elim (mode_double_RoundingMode m1); intros P (H1,H2).
unfold round_double, double_value; simpl.
apply sym_eq.
apply RoundedModeProjectorIdemEq with bdouble 53 P; 
  try apply pdGivesBound; auto with zarith.
elim (mode_double_RoundingMode m2); intros P' (H1',H2').
apply RoundedModeBounded with radix P' x; trivial.
Qed.


(* Single precision: lemmas *)

Lemma mode_single_RoundingMode: forall m, exists P, RoundedModeP bsingle radix P /\
  forall x y z, P x (sf (round_single_aux m x y z)).
intros m; case m; simpl.
exists (EvenClosest bsingle radix 24); split.
apply EvenClosestRoundedModeP; try apply psGivesBound; auto with zarith.
intros; apply RND_EvenClosest_correct; try apply psGivesBound; auto with zarith.
exists (ToZeroP bsingle radix); split.
apply ToZeroRoundedModeP with 24; try apply psGivesBound; auto with zarith.
intros; apply RND_Zero_correct; try apply psGivesBound; auto with zarith.
exists (isMax bsingle radix); split.
apply MaxRoundedModeP with 24; try apply psGivesBound; auto with zarith.
intros; apply RND_Max_correct; try apply psGivesBound; auto with zarith.
exists (isMin bsingle radix); split.
apply MinRoundedModeP with 24; try apply psGivesBound; auto with zarith.
intros; apply RND_Min_correct; try apply psGivesBound; auto with zarith.
exists (Closest bsingle radix); split.
apply ClosestRoundedModeP with 24; try apply psGivesBound; auto with zarith.
intros; apply RND_ClosestUp_correct; try apply psGivesBound; auto with zarith.
Qed.


Lemma max_single_bounded:
  exists f:float, Fbounded bsingle f /\ FtoRradix f = max_single.
exists (Float 16777215 104); split.
split.
rewrite psGivesBound; simpl; auto with zarith.
simpl; auto with zarith.
unfold max_single.
rewrite Rmult_assoc; rewrite Rmult_comm; rewrite Rmult_assoc.
unfold FtoRradix, FtoR.
simpl (Fnum (Float 16777215 104)); simpl  (Fexp (Float 16777215 104)).
apply Rmult_eq_compat.
rewrite <- Z2R_IZR.
reflexivity.
simpl.
ring.
Qed.


Lemma bounded_real_no_overflow_single :
  (forall (m:mode),
   (forall (x:R), ((Rle (Rabs x) max_single) -> (no_overflow_single m x)))).
unfold no_overflow_single; intros.
elim (mode_single_RoundingMode m); intros P (H1,H2).
elim max_single_bounded; intros f (H3,H4).
rewrite <- H4.
apply RoundAbsMonotoner with bsingle 24 P x; try apply psGivesBound; auto with zarith.
fold FtoRradix; rewrite H4; trivial.
Qed.

Lemma round_single_down_le :
  (forall (x:R), (Rle (round_single down x) x)).
intros; apply isMin_inv1 with bsingle.
simpl; apply RND_Min_correct; try apply psGivesBound; auto with zarith.
Qed.

Lemma round_up_single_ge :
  (forall (x:R), (Rge (round_single up x) x)).
intros; apply Rle_ge; apply isMax_inv1 with bsingle.
simpl; apply RND_Max_correct; try apply psGivesBound; auto with zarith.
Qed.

Lemma round_down_single_neg :
  (forall (x:R), (eq (round_single down (Ropp x)) (Ropp (round_single up x)))).
intros.
unfold round_single, single_value, FtoRradix; simpl.
rewrite <- Fopp_correct.
generalize (MinUniqueP bsingle radix); unfold UniqueP.
intros T; apply T with (-x)%R.
apply RND_Min_correct; try apply psGivesBound; auto with zarith.
apply MaxOppMin.
apply RND_Max_correct; try apply psGivesBound; auto with zarith.
Qed.

Lemma round_up_single_neg :
  (forall (x:R), (eq (round_single up (Ropp x)) (Ropp (round_single down x)))).
intros.
unfold round_single, single_value, FtoRradix; simpl.
rewrite <- Fopp_correct.
generalize (MaxUniqueP bsingle radix); unfold UniqueP.
intros T; apply T with (-x)%R.
apply RND_Max_correct; try apply psGivesBound; auto with zarith.
apply MinOppMax.
apply RND_Min_correct; try apply psGivesBound; auto with zarith.
Qed.

Lemma round_single_idempotent :
  (forall (m1:mode),
   (forall (m2:mode),
    (forall (x:R),
     (eq (round_single m1 (round_single m2 x)) (round_single m2 x))))).
intros.
elim (mode_single_RoundingMode m1); intros P (H1,H2).
unfold round_single, single_value; simpl.
apply sym_eq.
apply RoundedModeProjectorIdemEq with bsingle 24 P; 
  try apply psGivesBound; auto with zarith.
elim (mode_single_RoundingMode m2); intros P' (H1',H2').
apply RoundedModeBounded with radix P' x; trivial.
Qed.


Lemma double_to_single_val :
  (forall (m:mode),
   (forall (s:single),
    (eq (double_value (single_to_double m s)) (single_value s)))).
intros.
elim (mode_double_RoundingMode m); intros P (H1,H2).
apply sym_eq; unfold single_to_double.
apply RoundedModeProjectorIdemEq with bdouble 53 P;
   try apply pdGivesBound; auto with zarith.
destruct s.
simpl (sf (mk_single sf0 Hcansf0 single_exact0 single_model0)).
assert (Fbounded bsingle sf0).
apply FcanonicBound with radix; exact Hcansf0.
elim H; intros H3 H4; split.
rewrite pdGivesBound.
apply Zlt_le_trans with (1:=H3).
rewrite psGivesBound; clear.
apply Zpower_nat_monotone_le;auto with zarith.
apply Zle_trans with (2:=H4).
clear; simpl; auto with zarith.
Qed.

Lemma single_to_double_val :
  (forall (m:mode),
   (forall (d:double),
    (eq (single_value (double_to_single m d)) (round_single
                                               m (double_value d))))).
intros; case m; reflexivity.
Qed.


(* Various Why predicates. Only definitions are left. *)

(*Why predicate*) Definition single_of_real_post  (m:mode) (x:R) (res:single)
  := (eq (single_value res) (round_single m x)) /\
     (eq (single_exact res) x) /\ (eq (single_model res) x).

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

