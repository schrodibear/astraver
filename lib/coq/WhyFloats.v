
(* Why model for floating-point numbers
   Implements the file lib/why/floats.why *)

Require Export Reals.
Add LoadPath "/users/demons/sboldo/Recherche/PFF/V8.0".
Require Export AllFloat.
Require Export "Others/RND".

Let radix := 2%Z.

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


End Utiles.



Inductive mode : Set := nearest_even | to_zero | up | down | nearest_away.

Coercion Local FtoRradix := FtoR radix.

(** Single precision *)

Let bsingle := make_bound 24 149.

Lemma psGreaterThanOne: 1 < 24.
auto with arith.
Qed.

Lemma psGivesBound: Zpos (vNum bsingle) = Zpower_nat radix 24.
unfold bsingle; apply make_pGivesBound.
Qed.

Record single : Set := mk_single {
   s_float    : float;
   s_canonic  : Fcanonic radix bsingle s_float;
   s_to_exact : R;
   s_to_model : R
 }.


Definition s_to_r (f:single) := FtoRradix (s_float f).

Definition single_round_error (f:single):= 
    (Rabs ((s_to_exact f) - (s_to_r f))).

Definition single_total_error (f:single):= 
    (Rabs ((s_to_model f) - (s_to_r f))).

Definition single_set_model (f:single) (r:R) :=
      mk_single (s_float f) (s_canonic f) (s_to_exact f) r.





Definition r_to_s_aux (m:mode) (r r1 r2:R) := match m with
  |  nearest_even => mk_single (RND_EvenClosest bsingle radix 24 r) 
                     (RND_EvenClosest_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  to_zero      => mk_single (RND_Zero bsingle radix 24 r) 
                     (RND_Zero_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  up           => mk_single (RND_Min bsingle radix 24 r) 
                     (RND_Min_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  down         => mk_single (RND_Max bsingle radix 24 r) 
                     (RND_Max_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  |  nearest_away => mk_single (RND_ClosestUp bsingle radix 24 r) 
                     (RND_ClosestUp_canonic bsingle radix 24 
                         radixGreaterOne psGreaterThanOne psGivesBound r)
                     r1 r2
  end.

   
Definition r_to_s (m:mode) (r:R) := r_to_s_aux m r r r.
   

Definition add_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (s_float f1+s_float f2) 
                  (s_to_exact f1+s_to_exact f2) (s_to_model f1+s_to_model f2).

Definition sub_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (s_float f1-s_float f2) 
                  (s_to_exact f1-s_to_exact f2) (s_to_model f1-s_to_model f2).

Definition mul_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (s_float f1*s_float f2) 
                  (s_to_exact f1*s_to_exact f2) (s_to_model f1*s_to_model f2).

Definition div_single (m:mode) (f1 f2:single) :=
     r_to_s_aux m (s_float f1/s_float f2) 
                  (s_to_exact f1/s_to_exact f2) (s_to_model f1/s_to_model f2).

Definition sqrt_single (m:mode) (f:single) :=
     r_to_s_aux m (sqrt (s_float f))
                  (sqrt(s_to_exact f)) (sqrt(s_to_model f)).

Definition neg_single (m:mode) (f:single) :=
   mk_single (Fopp (s_float f)) 
         (FcanonicFopp radix bsingle (s_float f) (s_canonic f))
         (-(s_to_exact f)) (-(s_to_model f)).

Definition abs_single (m:mode) (f:single) :=
   mk_single (Fabs (s_float f)) 
         (FcanonicFabs radix radixGreaterOne bsingle (s_float f) (s_canonic f))
         (Rabs (s_to_exact f)) (Rabs (s_to_model f)).

Definition max_single : R.
Admitted.

Let bdouble := make_bound 53 1074.


Definition double: Set.
Admitted.

Definition add_double : mode -> double -> double -> double.
Admitted.

Definition sub_double : mode -> double -> double -> double.
Admitted.

Definition mul_double : mode -> double -> double -> double.
Admitted.

Definition div_double : mode -> double -> double -> double.
Admitted.

Definition neg_double : mode -> double -> double.
Admitted.

Definition abs_double : mode -> double -> double.
Admitted.

Definition sqrt_double : mode -> double -> double.
Admitted.

Definition d_to_r : double -> R.
Admitted.

Definition d_to_exact : double -> R.
Admitted.

Definition d_to_model : double -> R.
Admitted.

Definition r_to_d : mode -> R -> double.
Admitted.

Definition double_round_error : double -> R.
Admitted.

Definition double_total_error : double -> R.
Admitted.

Definition double_set_model : double -> R -> double.
Admitted.

Definition max_double : R.
Admitted.

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

Definition double_of_single : single -> double.
Admitted.

Definition single_of_double : mode -> double -> single.
Admitted.

Definition quad_of_single : single -> quad.
Admitted.

Definition single_of_quad : mode -> quad -> single.
Admitted.

Definition quad_of_double : double -> quad.
Admitted.

Definition double_of_quad : mode -> quad -> double.
Admitted.

