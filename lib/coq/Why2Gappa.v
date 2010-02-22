
Require Export Gappa_tactic.
Require Export Gappa_round.
Require Export Veltkamp.
Require Export floats_strict.
Hint Resolve psGreaterThanOne psGivesBound pdGreaterThanOne pdGivesBound  EvenClosestRoundedModeP RND_EvenClosest_correct RND_EvenClosest_canonic  (FcanonicBound radix).

Section Equiv.
Variable b : Fbound.
Variable p : nat.
 
Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat radix p.
Hypothesis precisionNotZero : 1 < p.


Lemma EvenClosestOpp: forall (f : float) (r : R),
       EvenClosest b radix p r f -> EvenClosest b radix p (- r)%R (Fopp f).
intros.
elim H; intros; split.
apply ClosestOpp; auto.
case H1; intros.
left; apply FNevenFop; auto.
right; intros.
rewrite Fopp_correct.
rewrite <- H2 with (Fopp q).
rewrite Fopp_correct; auto with real.
replace r with (-(-r))%R by ring; apply ClosestOpp; auto.
Qed.


Lemma ImplyClosest2_S_aux: 
 forall (z : R) (f : float),
       (Fcanonic radix b f) ->
       (Rabs f  < powerRZ radix (p-dExp b))%R ->
       (Fexp f=-dExp b)%Z.
intros.
cut (Fexp f <= -dExp b)%Z.
intros; assert (K:(Fbounded b f));[idtac|elim K; intros]; auto with zarith float.
cut (Fexp f <= Fexp (FPred b radix p (Float (nNormMin radix p) (-dExp b+1))))%Z; auto with zarith.
rewrite FPredSimpl2; auto with zarith.
simpl; unfold Zpred; auto with zarith.
simpl; auto with zarith.
assert (Fcanonic radix b (Float (nNormMin radix p) (- dExp b + 1))).
left; repeat split; [simpl|simpl|idtac]; auto with zarith.
rewrite Zabs_eq; [apply ZltNormMinVnum |apply Zlt_le_weak; apply nNormPos]; auto with zarith float.
simpl (Fnum (Float (nNormMin radix p) (- dExp b + 1))).
rewrite <- PosNormMin with radix b p; auto with zarith.
apply Fcanonic_Rle_Zle with radix b p; auto with zarith.
apply FPredCanonic; auto with zarith.
fold FtoRradix; rewrite Rabs_right with (FPred b radix p (Float (nNormMin radix p) (- dExp b + 1))).
unfold FtoRradix; rewrite <- Fabs_correct; auto with zarith.
apply FPredProp; auto with zarith real.
apply FcanonicFabs; auto with zarith.
rewrite Fabs_correct; auto with zarith; fold FtoRradix.
apply Rlt_le_trans with (1:=H0).
right; unfold FtoRradix, FtoR; simpl.
unfold nNormMin; rewrite Zpower_nat_Z_powerRZ; rewrite <- powerRZ_add; auto with real zarith.
replace (pred p + (- dExp b + 1))%Z with (p-dExp b)%Z; auto.
rewrite inj_pred; auto with zarith; unfold Zpred; ring.
apply Rle_ge; apply R0RltRlePred; auto with zarith.
apply LtFnumZERO; simpl; unfold nNormMin; auto with zarith.
Qed.


Lemma ImplyClosest2_S: 
 forall (z : R) (f : float),
       (Fcanonic radix b f) ->
       (Rabs f  < powerRZ radix (p-dExp b))%R ->
       (Rabs (f-z) <= powerRZ radix (Fexp f) / 2)%R ->
       Closest b radix z f.
intros.
cut (Fexp f = (-dExp b))%Z;[intros E|apply ImplyClosest2_S_aux; auto].
apply ClosestSuccPred with p; auto with zarith.
fold FtoRradix; apply Rplus_le_reg_l with (Rabs (f-z)).
apply Rle_trans with (2* Rabs (f - z))%R.
right; replace (z-f)%R with (-(f-z))%R by ring; rewrite Rabs_Ropp; ring.
apply Rle_trans with (powerRZ radix (Fexp f)).
apply Rle_trans with (2*(powerRZ radix (Fexp f) / 2))%R;[idtac|right; field].
apply Rmult_le_compat_l; auto with real.
apply Rle_trans with (Rabs ((f-z)+(z - FSucc b radix p f)));[idtac|apply Rabs_triang].
replace (f - z + (z - FSucc b radix p f))%R with (-(FtoRradix ((Fminus radix (FSucc b radix p f) f))))%R.
rewrite Rabs_Ropp; unfold FtoRradix.
case (Z_eq_dec (Fnum f) (-nNormMin radix p)%Z); intros.
rewrite FSuccDiff2; auto with zarith.
rewrite Rabs_right.
unfold FtoR; simpl; right; ring.
apply Rle_ge; unfold FtoR; simpl; ring_simplify; auto with real zarith.
rewrite FSuccDiff1; auto with zarith.
rewrite Rabs_right.
unfold FtoR; simpl; right; ring.
apply Rle_ge; unfold FtoR; simpl; ring_simplify; auto with real zarith.
unfold FtoRradix; rewrite Fminus_correct; auto with zarith; ring.
fold FtoRradix; apply Rplus_le_reg_l with (Rabs (f-z)).
apply Rle_trans with (2* Rabs (f - z))%R.
right; replace (z-f)%R with (-(f-z))%R by ring; rewrite Rabs_Ropp; ring.
apply Rle_trans with (powerRZ radix (Fexp f)).
apply Rle_trans with (2*(powerRZ radix (Fexp f) / 2))%R;[idtac|right; field].
apply Rmult_le_compat_l; auto with real.
apply Rle_trans with (Rabs ((f-z)+(z - FPred b radix p f)));[idtac|apply Rabs_triang].
replace (f - z + (z - FPred b radix p f))%R with ((FtoRradix ((Fminus radix f (FPred b radix p f)))))%R.
case (Z_eq_dec (Fnum f) (nNormMin radix p)); intros.
unfold FtoRradix; rewrite FPredDiff2; auto with zarith.
rewrite Rabs_right.
unfold FtoR; simpl; right; ring.
apply Rle_ge; unfold FtoR; simpl; ring_simplify; auto with real zarith.
unfold FtoRradix; rewrite FPredDiff1; auto with zarith.
rewrite Rabs_right.
unfold FtoR; simpl; right; ring.
apply Rle_ge; unfold FtoR; simpl; ring_simplify; auto with real zarith.
unfold FtoRradix; rewrite Fminus_correct; auto with zarith; ring.
Qed.



Lemma equiv_RNDs_aux1: forall (r:R),
   exists f:float, 
   Fbounded b f /\ (FtoRradix f=gappa_rounding (rounding_float roundNE (P_of_succ_nat (p-1)) (dExp b)) r).
intros r; unfold gappa_rounding,  rounding_float.
elim Gappa_round.representable_round_extension with roundNE (float_shift (P_of_succ_nat (p-1)) (dExp b)) 
   (good_shift (P_of_succ_nat (p-1)) (dExp b)) r.
intros n (e, (H1,H2)).
case (Z_eq_dec n 0); intros L.
exists (Float 0 (-dExp b)); split.
split; simpl; auto with zarith float.
rewrite H1; rewrite L.
unfold float2R, FtoRradix, FtoR, Gappa_integer.F2R; simpl.
case e; try intros; try unfold Rdiv; try ring.
exists (Float n e); split.
unfold Gappa_round.rexp_representable in H2.
destruct n.
absurd (0 <> 0)%Z; auto with zarith.
unfold float_shift in H2.
split; simpl.
assert ((e + Zpos (Gappa_round_aux.digits p0) - Zpos (P_of_succ_nat (p - 1))) <= e)%Z.
apply Zle_trans with (2:=H2).
apply Zle_max_l.
assert ((Zpos (Gappa_round_aux.digits p0) <=  Zpos (P_of_succ_nat (p - 1))))%Z.
auto with zarith.
elim (Gappa_round_aux.digits_correct p0); intros.
apply Zlt_Rlt.
apply Rle_lt_trans with (Gappa_integer.Z2R (Zpos p0)).
rewrite Gappa_integer.Z2R_IZR; auto with real.
apply Rlt_le_trans with (1:=H4).
rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ.
unfold radix; apply Rle_powerRZ; auto with real zarith.
apply Zle_trans with (1:=H0).
rewrite Zpos_P_of_succ_nat; auto with zarith.
apply Zle_trans with (2:=H2).
apply Zle_max_r.
unfold float_shift in H2.
split; simpl.
assert ((e + Zpos (Gappa_round_aux.digits p0) - Zpos (P_of_succ_nat (p - 1))) <= e)%Z.
apply Zle_trans with (2:=H2).
apply Zle_max_l.
assert ((Zpos (Gappa_round_aux.digits p0) <=  Zpos (P_of_succ_nat (p - 1))))%Z.
auto with zarith.
elim (Gappa_round_aux.digits_correct p0); intros.
apply Zlt_Rlt.
apply Rle_lt_trans with (Gappa_integer.Z2R (Zpos p0)).
rewrite Gappa_integer.Z2R_IZR; auto with real.
apply Rlt_le_trans with (1:=H4).
rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ.
unfold radix; apply Rle_powerRZ; auto with real zarith.
apply Zle_trans with (1:=H0).
rewrite Zpos_P_of_succ_nat; auto with zarith.
apply Zle_trans with (2:=H2).
apply Zle_max_r.
rewrite H1.
unfold float2R, FtoRradix, FtoR, Gappa_integer.F2R; simpl.
case e.
rewrite Gappa_integer.Z2R_IZR; simpl; ring.
intros; rewrite Gappa_integer.mult_Z2R.
rewrite Gappa_integer.Zpower_pos_powerRZ; rewrite Gappa_integer.Z2R_IZR.
simpl; ring.
intros.
rewrite Gappa_integer.Zpower_pos_powerRZ; rewrite Gappa_integer.Z2R_IZR.
simpl; auto with real.
Qed.


Lemma equiv_RNDs_aux2: forall (r:R),
   exists f:float, 
   Fcanonic radix b f /\ (FtoRradix f=gappa_rounding (rounding_float roundNE (P_of_succ_nat (p-1)) (dExp b)) r).
intros; elim (equiv_RNDs_aux1 r).
intros f (H1,H2).
exists (Fnormalize radix b p f); split.
apply FnormalizeCanonic; auto with zarith.
unfold FtoRradix; rewrite FnormalizeCorrect; auto with real zarith.
Qed.



Lemma equiv_RNDs_aux3: forall (r:R),
  (0 < r)%R ->
    (exists f:float, 
      Fcanonic radix b f /\ (FtoRradix f=gappa_rounding (rounding_float roundNE (P_of_succ_nat (p-1)) (dExp b)) r) 
     /\  (Closest b radix r f)).
intros r T.
generalize (equiv_RNDs_aux2 r).
intros (f,(H1,H2)).
exists f; split; auto; split; auto.
cut (exists k:Z, (powerRZ radix (k-1) <= r < powerRZ radix k)%R).
intros (k,(H3,H4)).
case (Zle_or_lt (-dExp b) (k-p)); intros U.
(* normal and positive *)
apply ImplyClosest with p (k-p)%Z; auto with zarith.
replace (k - p + p - 1)%Z with (k-1)%Z by ring; auto.
replace (k - p + p - 1)%Z with (k-1)%Z by ring.
fold FtoRradix; rewrite H2.
unfold gappa_rounding.
unfold rounding_float.
apply Rle_trans with (round_extension roundNE (float_shift (P_of_succ_nat (p - 1)) (dExp b))
   (good_shift (P_of_succ_nat (p - 1)) (dExp b)) (powerRZ radix (k - 1))).
replace (powerRZ radix (k-1)) with (float2R (Float2 1 (k-1))).
right; apply sym_eq; apply round_extension_representable.
simpl.
unfold float_shift; apply Zmax_lub; auto with zarith.
rewrite Zpos_P_of_succ_nat; auto with zarith.
rewrite Gappa_round_aux.float2_pow2; auto.
apply round_extension_monotone; auto.
rewrite <- Rabs_Ropp; fold FtoRradix.
replace (-(r-f))%R with (f-r)%R by ring; rewrite H2.
apply Rle_trans with   (Float2 1 (float_shift (P_of_succ_nat (p - 1)) (dExp b)  k - 1))%R.
apply float_absolute_ne_binade.
split; rewrite Gappa_round_aux.float2_pow2; auto.
rewrite Gappa_round_aux.float2_pow2.
apply Rle_trans with (powerRZ radix (k - p-1)).
apply Rle_powerRZ; auto with zarith real.
apply Zplus_le_compat_r.
unfold float_shift; apply Zmax_lub; auto with zarith.
rewrite Zpos_P_of_succ_nat; auto with zarith.
unfold Zsucc; rewrite inj_minus1; simpl; auto with zarith.
unfold Zminus; rewrite powerRZ_add; auto with real zarith.
simpl; right; field.
(* Subnormal and positive *)
assert (Rabs f < powerRZ radix (p - dExp b))%R.
rewrite Rabs_right.
case (Zle_or_lt (-dExp b) k); intros.
apply Rle_lt_trans with (powerRZ radix k).
rewrite H2.
unfold gappa_rounding.
unfold rounding_float.
apply Rle_trans with (round_extension roundNE (float_shift (P_of_succ_nat (p - 1)) (dExp b))
   (good_shift (P_of_succ_nat (p - 1)) (dExp b)) (powerRZ radix (k))).
apply round_extension_monotone; auto with real.
replace (powerRZ radix k) with (float2R (Float2 1 (k))).
right; apply round_extension_representable.
simpl.
unfold float_shift; apply Zmax_lub; auto with zarith.
rewrite Zpos_P_of_succ_nat; auto with zarith.
rewrite Gappa_round_aux.float2_pow2; auto.
apply Rlt_powerRZ; auto with zarith real.
apply Rle_lt_trans with (powerRZ radix (-(dExp b))).
rewrite H2.
unfold gappa_rounding.
unfold rounding_float.
apply Rle_trans with (round_extension roundNE (float_shift (P_of_succ_nat (p - 1)) (dExp b))
   (good_shift (P_of_succ_nat (p - 1)) (dExp b)) (powerRZ radix (-(dExp b)))).
apply round_extension_monotone; auto with real.
apply Rle_trans with (powerRZ radix k); auto with real zarith.
replace (powerRZ radix (-dExp b)) with (float2R (Float2 1 (-dExp b))).
right; apply round_extension_representable.
simpl.
unfold float_shift; apply Zmax_lub; auto with zarith.
rewrite Zpos_P_of_succ_nat; auto with zarith.
rewrite Gappa_round_aux.float2_pow2; auto.
apply Rlt_powerRZ; auto with zarith real.
apply Rle_ge; rewrite H2.
apply round_extension_positive; auto.
apply ImplyClosest2_S; auto.
rewrite H2.
apply Rle_trans with   (Float2 1 (float_shift (P_of_succ_nat (p - 1)) (dExp b)  k - 1))%R.
apply float_absolute_ne_binade.
split; rewrite Gappa_round_aux.float2_pow2; auto.
rewrite Gappa_round_aux.float2_pow2.
apply Rle_trans with (powerRZ radix (-dExp b-1)).
apply Rle_powerRZ; auto with zarith real.
apply Zplus_le_compat_r.
unfold float_shift.
rewrite Zmax_right; auto with zarith.
rewrite Zpos_P_of_succ_nat; auto with zarith.
unfold Zsucc; rewrite inj_minus1; simpl; auto with zarith.
rewrite ImplyClosest2_S_aux; auto.
unfold Zminus; rewrite powerRZ_add; auto with real zarith.
simpl; right; field.
exists (IRNDD (ln r / ln radix)+1)%Z; split.
ring_simplify ( (IRNDD (ln r / ln radix) + 1 - 1))%Z.
rewrite <- exp_ln_powerRZ; auto with zarith.
apply Rle_trans with (exp ((ln radix *  (ln r / ln radix))))%R.
apply exp_monotone; auto with real.
apply Rmult_le_compat_l; auto with real.
unfold radix; simpl; auto with real.
rewrite <- ln_1; left; apply  ln_increasing; auto with real.
apply IRNDD_correct1.
replace ((ln radix * (ln r / ln radix)))%R with (ln r).
rewrite exp_ln; auto with real.
field.
assert (0 < ln radix)%R; auto with real.
simpl; rewrite <- ln_1; apply  ln_increasing; auto with real zarith.
apply radix.
rewrite <- exp_ln_powerRZ; auto with zarith.
apply Rle_lt_trans with (exp ((ln radix *  (ln r / ln radix))))%R.
replace ((ln radix * (ln r / ln radix)))%R with (ln r).
rewrite exp_ln; auto with real.
field.
assert (0 < ln radix)%R; auto with real.
simpl; rewrite <- ln_1; apply  ln_increasing; auto with real zarith.
apply exp_increasing; auto with real.
apply Rmult_lt_compat_l; auto with real.
unfold radix; simpl; auto with real.
rewrite <- ln_1; apply  ln_increasing; auto with real.
apply IRNDD_correct2.
apply radix.
Qed.


Lemma equiv_RNDs_aux4: forall (r:R),
    (exists f:float, 
      Fcanonic radix b f /\ (FtoRradix f=gappa_rounding (rounding_float roundNE (P_of_succ_nat (p-1)) (dExp b)) r) 
     /\  (Closest b radix r f)).
intros.
case (Rle_or_lt 0 r); intros I.
case I; clear I; intros I.
apply equiv_RNDs_aux3; auto.
exists (Float 0 (-dExp b)).
split;[right| split].
repeat split; simpl; auto with zarith.
rewrite <- I; unfold gappa_rounding, rounding_float.
rewrite round_extension_zero.
unfold FtoRradix, FtoR; simpl; ring.
replace r with (FtoR radix ((Float 0 (- dExp b)))).
apply RoundedModeProjectorIdem with b; auto with zarith.
apply ClosestRoundedModeP with p; auto with zarith.
repeat split; simpl; auto with zarith.
unfold FtoRradix, FtoR; simpl; rewrite <- I; ring.
elim (equiv_RNDs_aux3 (-r)); auto with real.
intros f (H1,(H2,H3)).
exists (Fopp f); split.
apply FcanonicFopp; auto.
split.
unfold FtoRradix; rewrite Fopp_correct; auto with zarith.
fold FtoRradix; rewrite H2.
unfold gappa_rounding, rounding_float.
rewrite round_extension_opp; auto with real.
replace r with (-(-r))%R by ring.
apply ClosestOpp; auto.
Qed.



Lemma equiv_RNDs_aux5: forall (rnd:R->R),
  (forall (r:R),
    (exists f:float, 
      Fcanonic radix b f /\ (FtoRradix f=rnd r) 
     /\  (Closest b radix r f))) ->
  (forall (f:float), Fcanonic radix b f -> (0 <= f)%R ->
           (exists g:float,  Fcanonic radix b g /\ (FtoRradix g=rnd (f+/2* Fulp b radix p f))%R 
     /\  (FNeven b radix p g))) ->
  (forall (r:R), (0 <= r)%R ->
    (exists f:float, 
      Fcanonic radix b f /\ (FtoRradix f=rnd r) 
     /\  (EvenClosest b radix p r f))).
intros.
elim (H r); intros f (H2,(H3,H4)).
exists f; split; auto; split; auto.
split; auto.
assert (T:(exists f1:float, Fcanonic radix b f1 /\ (f1 <= r)%R /\ (isMin b radix r f1))).
exists (RND_Min b radix p r); split.
apply RND_Min_canonic; auto with zarith.
assert  (isMin b radix r (RND_Min b radix p r)).
apply RND_Min_correct; auto with zarith.
split; auto.
elim H5; intros T1 (T2,T3); auto.
elim T; intros f1 (L1,(L2,L3)); clear T.
assert (T:(exists f2:float, Fcanonic radix b f2 /\ (r <= f2)%R /\ (isMax b radix r f2))).
exists (RND_Max b radix p r); split.
apply RND_Max_canonic; auto with zarith.
assert  (isMax b radix r (RND_Max b radix p r)).
apply RND_Max_correct; auto with zarith.
split; auto.
elim H5; intros T1 (T2,T3); auto.
elim T; intros f2 (L1',(L2',L3')); clear T.
case (Req_dec r (FtoR radix f1)).
intros; right; intros.
rewrite <- RoundedModeProjectorIdemEq with b radix p (Closest b radix) f1 f; auto with zarith.
rewrite <- RoundedModeProjectorIdemEq with b radix p (Closest b radix) f1 q; auto with zarith.
apply ClosestRoundedModeP with p; auto with zarith.
rewrite <- H5; auto.
apply ClosestRoundedModeP with p; auto with zarith.
rewrite <- H5; auto.
intros Q.
assert (FtoRradix f2 = f1 + Fulp b radix p f1)%R.
apply trans_eq with (FtoRradix (FNSucc b radix p f1)).
apply (MaxUniqueP b radix r); auto.
apply MinMax; auto with zarith.
unfold FNSucc; rewrite FcanonicFnormalizeEq; auto with zarith.
apply Rplus_eq_reg_l with (-f1)%R.
apply trans_eq with (FtoR radix (Fminus radix (FSucc b radix p f1) f1)).
unfold FtoRradix; rewrite Fminus_correct; auto with zarith; ring.
rewrite FSuccDiff1; auto with zarith.
rewrite CanonicFulp; auto with zarith real; ring.
assert (-nNormMin radix p < Fnum f1)%Z; auto with zarith.
apply Zlt_le_trans with (-0)%Z.
unfold nNormMin; auto with zarith arith.
simpl; apply LeR0Fnum with radix; auto with real zarith.
apply RleRoundedR0 with (5:=L3) (b:=b) (precision:=p); auto with zarith real.
apply MinRoundedModeP with p; auto with zarith.
case (Rle_or_lt r (f1+ /2 * Fulp b radix p f1)); intros Y.
case Y; clear Y; intros Y.
right; intros.
case (ClosestMinOrMax b radix r q); auto; intros Q1.
case (ClosestMinOrMax b radix r f); auto; intros Q2.
apply (MinUniqueP b radix r); auto.
elim H4; intros.
absurd (Rabs (f - r) <= Rabs (f1 - r))%R.
apply Rlt_not_le.
unfold FtoRradix; rewrite (MaxUniqueP b radix r f f2); auto.
fold FtoRradix; rewrite Rabs_left1.
rewrite Rabs_right.
rewrite H5.
apply Rplus_lt_reg_r with (r+f1)%R; apply Rmult_lt_reg_l with (/2)%R; auto with real.
apply Rle_lt_trans with r;[right; field|idtac].
apply Rlt_le_trans with (1:=Y); right; field.
apply Rle_ge; apply Rplus_le_reg_l with r; ring_simplify; auto.
apply Rplus_le_reg_l with r; ring_simplify; auto.
apply H8; elim L3; auto.
case (ClosestMinOrMax b radix r f); auto; intros Q2.
elim H6; intros.
absurd (Rabs (q - r) <= Rabs (f1 - r))%R.
apply Rlt_not_le.
unfold FtoRradix; rewrite (MaxUniqueP b radix r q f2); auto.
fold FtoRradix; rewrite Rabs_left1.
rewrite Rabs_right.
rewrite H5.
apply Rplus_lt_reg_r with (r+f1)%R; apply Rmult_lt_reg_l with (/2)%R; auto with real.
apply Rle_lt_trans with r;[right; field|idtac].
apply Rlt_le_trans with (1:=Y); right; field.
apply Rle_ge; apply Rplus_le_reg_l with r; ring_simplify; auto.
apply Rplus_le_reg_l with r; ring_simplify; auto.
apply H8; elim L3; auto.
apply (MaxUniqueP b radix r); auto.
left.
elim H0 with f1; auto.
intros ff (T1,(T2,T3)).
replace f with ff; auto.
apply FcanonicUnique with radix b p; auto with zarith.
fold FtoRradix; rewrite T2; rewrite H3; rewrite Y; auto.
apply RleRoundedR0 with (5:=L3) (b:=b) (precision:=p); auto with zarith real.
apply MinRoundedModeP with p; auto with zarith.
right; intros.
case (ClosestMinOrMax b radix r q); auto; intros Q1.
case (ClosestMinOrMax b radix r f); auto; intros Q2.
apply (MinUniqueP b radix r); auto.
elim H6; intros.
absurd (Rabs (q - r) <= Rabs (f2 - r))%R.
apply Rlt_not_le.
unfold FtoRradix; rewrite (MinUniqueP b radix r q f1); auto.
fold FtoRradix; rewrite Rabs_right.
rewrite Rabs_left1.
rewrite H5.
apply Rplus_lt_reg_r with (r+f1)%R; apply Rmult_lt_reg_l with (/2)%R; auto with real.
apply Rlt_le_trans with r;[idtac|right; field].
apply Rle_lt_trans with (2:=Y); right; field.
apply Rplus_le_reg_l with r; ring_simplify; auto.
apply Rle_ge; apply Rplus_le_reg_l with r; ring_simplify; auto.
apply H8; elim L3; auto.
case (ClosestMinOrMax b radix r f); auto; intros Q2.
elim H4; intros.
absurd (Rabs (f - r) <= Rabs (f2 - r))%R.
apply Rlt_not_le.
unfold FtoRradix; rewrite (MinUniqueP b radix r f f1); auto.
fold FtoRradix; rewrite Rabs_right.
rewrite Rabs_left1.
rewrite H5.
apply Rplus_lt_reg_r with (r+f1)%R; apply Rmult_lt_reg_l with (/2)%R; auto with real.
apply Rlt_le_trans with r;[idtac|right; field].
apply Rle_lt_trans with (2:=Y); right; field.
apply Rplus_le_reg_l with r; ring_simplify; auto.
apply Rle_ge; apply Rplus_le_reg_l with r; ring_simplify; auto.
apply H8; elim L3; auto.
apply (MaxUniqueP b radix r); auto.
Qed.

Lemma equiv_RNDs_aux6: forall (f1 f2:float), 
  Fbounded b f1 -> Fcanonic radix b f2 -> (FtoRradix f1 =f2) -> Feven f1 -> 
     FNeven b radix p f2.
intros.
apply FNevenEq with f1; auto with zarith.
unfold FNeven, Fnormalize.
case (Z_zerop (Fnum f1)); intros.
unfold Feven, Even; exists 0%Z; simpl; auto with zarith.
elim H2; intros.
unfold Fshift, Feven, Even.
exists (x*Zpower_nat radix
          (min (p - Fdigit radix f1) (Zabs_nat (dExp b + Fexp f1))))%Z.
rewrite H3.
apply trans_eq with (2 * x *
      Zpower_nat radix
        (min (p - Fdigit radix f1) (Zabs_nat (dExp b + Fexp f1))))%Z; auto with zarith.
Qed.

Lemma equiv_RNDs_aux7: forall (m e:Z) (f2:float), 
   Fcanonic radix b f2 -> (FtoRradix f2 = Float2 m e) -> Even m -> 
   (Zabs m <= Zpower_nat radix p)%Z -> (-dExp b <= e)%Z ->
     FNeven b radix p f2.
intros.
case (Zle_lt_or_eq  (Zabs m) (Zpower_nat radix p)); auto; intros.
apply equiv_RNDs_aux6 with (Float m e); auto.
split; simpl; auto with zarith.
rewrite H0; unfold float2R; rewrite Gappa_integer.F2R_split.
rewrite Gappa_integer.Z2R_IZR; simpl; auto.
case (Zle_or_lt 0 m); intros.
apply equiv_RNDs_aux6 with (Float (nNormMin radix p) (e+1)); auto.
split; simpl; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply ZltNormMinVnum; auto with zarith.
unfold nNormMin; auto with zarith.
rewrite H0; unfold float2R; rewrite Gappa_integer.F2R_split.
rewrite Gappa_integer.Z2R_IZR; simpl; auto.
unfold FtoRradix, FtoR, nNormMin; simpl.
rewrite Zabs_eq in H4; auto with zarith.
rewrite H4; repeat rewrite Zpower_nat_Z_powerRZ.
repeat rewrite <- powerRZ_add; auto with real zarith.
replace (pred p + (e + 1))%Z with (p+e)%Z; auto.
rewrite inj_pred; auto with zarith; unfold Zpred; ring.
unfold Feven, Even; exists (Zpower_nat radix (p-2)).
apply trans_eq with (nNormMin radix p); auto; unfold nNormMin.
replace (pred p) with (1+(p-2))%nat; auto with zarith.
apply equiv_RNDs_aux6 with (Float (-nNormMin radix p) (e+1)); auto.
split; simpl; auto with zarith.
rewrite Zabs_Zopp; rewrite Zabs_eq; auto with zarith.
apply ZltNormMinVnum; auto with zarith.
unfold nNormMin; auto with zarith.
rewrite H0; unfold float2R; rewrite Gappa_integer.F2R_split.
rewrite Gappa_integer.Z2R_IZR; simpl; auto.
unfold FtoRradix, FtoR, nNormMin; simpl.
rewrite <- Zabs_Zopp in H4; rewrite Zabs_eq in H4; auto with zarith.
replace (IZR m) with (-IZR (-m))%R.
rewrite Ropp_Ropp_IZR.
rewrite H4; repeat rewrite Zpower_nat_Z_powerRZ.
repeat rewrite Ropp_mult_distr_l_reverse.
repeat rewrite <- powerRZ_add; auto with real zarith.
replace (pred p + (e + 1))%Z with (p+e)%Z; auto.
rewrite inj_pred; auto with zarith; unfold Zpred; ring.
rewrite Ropp_Ropp_IZR; auto with real.
unfold Feven, Even; exists (-(Zpower_nat radix (p-2)))%Z.
apply trans_eq with (-nNormMin radix p)%Z; auto; unfold nNormMin.
replace (pred p) with (1+(p-2))%nat; auto with zarith.
rewrite Zpower_nat_is_exp; auto with zarith.
replace (Zpower_nat radix 1) with 2%Z; auto with zarith.
Qed.



Lemma equiv_RNDs_aux8: forall (r:R),
   (0 <= r)%R ->
    (exists f:float, 
      Fcanonic radix b f /\ (FtoRradix f=gappa_rounding (rounding_float roundNE (P_of_succ_nat (p-1)) (dExp b)) r) 
     /\  (EvenClosest b radix p r f)).
apply equiv_RNDs_aux5.
apply equiv_RNDs_aux4.
intros.
elim (equiv_RNDs_aux4  (f + / 2 * Fulp b radix p f)).
intros g (H1,(H2,H3)).
exists g; split; auto; split; auto.
unfold gappa_rounding, rounding_float in H2.
assert (f + /2*Fulp b radix p f = Float2 (2*Fnum f+1) (Fexp f -1))%R.
apply trans_eq with  ((2 * Fnum f + 1)%Z * powerRZ radix (Fexp f -1))%R.
rewrite CanonicFulp; auto with zarith.
unfold Zminus; rewrite powerRZ_add; auto with real zarith.
rewrite plus_IZR; rewrite mult_IZR; unfold FtoRradix, FtoR; simpl.
field.
unfold float2R; rewrite Gappa_integer.F2R_split.
rewrite Gappa_integer.Z2R_IZR; simpl; auto.
rewrite H4 in H2.
rewrite round_extension_float2 in H2.
assert (exists l:positive,  (2 * Fnum f + 1 = Zpos l)%Z).
assert (0 < 2*Fnum f +1)%Z.
assert (0 <= Fnum f)%Z; auto with zarith.
apply LeR0Fnum with radix; auto with real zarith.
destruct (2*Fnum f+1)%Z; auto with zarith.
Contradict H5; auto with zarith.
exists p0; auto.
Contradict H5; auto with zarith.
elim H5; intros l Hl; rewrite Hl in H2.
CaseEq (Fnum f); intros ll.
unfold round in H2; simpl in H2.
elim round_constant_underflow with rndNE (float_shift (P_of_succ_nat (p - 1)) (dExp b)) 
   (-dExp b)%Z l (Fexp f-1)%Z.
intros G1 (G2,G3); clear G1 G3.
rewrite G2 in H2.
simpl in H2.
apply equiv_RNDs_aux7 with (2:=H2); auto with zarith.
unfold Even; exists 0%Z; auto with zarith.
apply Zle_trans with (-0)%Z; auto with zarith.
apply Zle_Zopp; auto with zarith.
case (dExp b); auto with zarith.
replace (Zpos l) with 1%Z; auto with zarith.
replace (Fexp f) with (-(dExp b))%Z; auto.
case H; intros.
elim H6; intros Y1 Y2.
absurd (Zpos (vNum b) <= 0)%Z.
apply Zlt_not_le; auto with zarith float.
apply Zle_trans with (1:=Y2); rewrite ll; rewrite Zabs_eq; auto with zarith.
elim H6; intros T1 (T2,T3); auto with zarith.
apply good_shift.
unfold float_shift.
rewrite Zmax_right; auto with zarith.
apply Zle_trans with (- dExp b - 0)%Z; unfold Zminus; auto with zarith.
intros Hll.
unfold round in H2; simpl in H2.
elim round_constant with rndNE (float_shift (P_of_succ_nat (p - 1)) (dExp b)) ll (Fexp f)%Z l (Fexp f-1)%Z.
intros G1 (G2,G3); clear G1 G3.
rewrite G2 in H2; simpl in H2.
unfold rndNE in H2; simpl in H2.
CaseEq ll; intros; rewrite H6 in H2; simpl in H2.
apply equiv_RNDs_aux7 with (2:=H2); auto with real zarith float.
unfold Even; exists (Zpos (Psucc p0)); auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply Zle_trans with (Zpos ll+1)%Z; auto with zarith.
rewrite H6; auto with zarith.
assert (Zpos ll < Zpower_nat radix p)%Z; auto with zarith.
rewrite <- Hll; rewrite <- pGivesBound; auto with zarith float.
rewrite <- (Zabs_eq (Fnum f)); auto with zarith float.
rewrite Hll; auto with zarith.
apply equiv_RNDs_aux7 with (2:=H2); auto with real zarith float.
unfold Even; exists (Zpos p0); auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply Zle_trans with (Zpos ll)%Z; auto with zarith.
rewrite H6; auto with zarith.
assert (Zpos ll < Zpower_nat radix p)%Z; auto with zarith.
rewrite <- Hll; rewrite <- pGivesBound; auto with zarith float.
rewrite <- (Zabs_eq (Fnum f)); auto with zarith float.
rewrite Hll; auto with zarith.
apply equiv_RNDs_aux7 with (2:=H2); auto with real zarith float.
unfold Even; exists 1%Z; auto with zarith.
rewrite Zabs_eq; auto with zarith.
apply Zle_trans with (Zpower_nat radix 1); auto with zarith.
replace (Zpos l) with (Zpos ll * 2 + 1)%Z; auto.
rewrite <- Hl; rewrite Hll; auto with zarith.
unfold float_shift.
rewrite Zpos_P_of_succ_nat; auto with zarith.
replace (Zsucc (p-1)%nat) with (Z_of_nat p); auto with zarith.
2: unfold Zsucc; rewrite inj_minus1; simpl; auto with zarith.
elim (Gappa_round_aux.digits_correct ll).
rewrite Gappa_integer.Z2R_IZR; intros P1 P2.
case H; intros.
assert (Zpos (Gappa_round_aux.digits ll) = p)%Z.
assert (p -1 < Zpos (Gappa_round_aux.digits ll))%Z.
apply Zlt_powerRZ with 2%R; auto with zarith real.
apply Rle_lt_trans with (2:=P2).
rewrite <- Hll; elim H6; intros.
apply Rmult_le_reg_l with (IZR radix); auto with real zarith.
rewrite <- mult_IZR.
rewrite <- (Zabs_eq (radix*Fnum f)); auto with zarith.
apply Rle_trans with (IZR (Zpos (vNum b))); auto with real zarith.
rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ.
right; simpl; unfold Zminus; rewrite powerRZ_add; auto with real zarith.
simpl; field.
assert (0 <= Fnum f)%Z; auto with zarith.
apply LeR0Fnum with radix; auto with zarith.
assert (Zpos (Gappa_round_aux.digits ll) -1 < p)%Z; auto with zarith.
apply Zlt_powerRZ with 2%R; auto with zarith real.
apply Rle_lt_trans with (1:=P1).
rewrite <- Hll; elim H6; intros (Y1,Y2) Y3.
apply Rle_lt_trans with (Rabs (Fnum f));[apply RRle_abs|idtac].
rewrite Rabs_Zabs.
apply Rlt_le_trans with (IZR (Zpos (vNum b))); auto with real zarith.
rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ; auto with real zarith.
rewrite H7.
replace  (Fexp f + p - p)%Z with (Fexp f) by ring.
apply Zmax_left; apply Zle_ge; auto with zarith float.
elim H6; intros Y1 (Y2,Y3); rewrite Y2.
apply Zmax_right.
assert (Zpos (Gappa_round_aux.digits ll) -1 < p)%Z; auto with zarith.
apply Zlt_powerRZ with 2%R; auto with zarith real.
apply Rle_lt_trans with (1:=P1).
rewrite <- Hll; elim Y1; intros Y4 Y5. 
apply Rle_lt_trans with (Rabs (Fnum f));[apply RRle_abs|idtac].
rewrite Rabs_Zabs.
apply Rlt_le_trans with (IZR (Zpos (vNum b))); auto with real zarith.
rewrite pGivesBound; rewrite Zpower_nat_Z_powerRZ; auto with real zarith.
intros; absurd (0 <= Fnum f)%Z; auto with zarith.
rewrite H6; auto with zarith.
apply LeR0Fnum with radix; auto with zarith.
Qed.


Lemma equiv_RNDs_aux9: forall (r:R),
    (exists f:float, 
      Fcanonic radix b f /\ (FtoRradix f=gappa_rounding (rounding_float roundNE (P_of_succ_nat (p-1)) (dExp b)) r) 
     /\  (EvenClosest b radix p r f)).
intros r; case (Rle_or_lt 0 r); intros.
apply equiv_RNDs_aux8; auto.
elim (equiv_RNDs_aux8 (-r)); auto with real.
intros f (H1,(H2,H3)).
exists (Fopp f); split.
apply FcanonicFopp; auto.
split.
unfold FtoRradix; rewrite Fopp_correct; auto with zarith.
fold FtoRradix; rewrite H2.
unfold gappa_rounding, rounding_float.
rewrite round_extension_opp; auto with real.
replace r with (-(-r))%R by ring.
apply EvenClosestOpp; auto.
Qed.



Lemma equiv_RNDs: forall (r:R),
   (FtoR radix (RND_EvenClosest b radix p r) 
     = gappa_rounding (rounding_float roundNE (P_of_succ_nat (p-1)) (dExp b)) r)%R.
intros.
elim (equiv_RNDs_aux9 r); intros f (H1,(H2,H3)).
rewrite <- H2; unfold FtoRradix.
generalize (EvenClosestUniqueP b radix p); unfold UniqueP; intros T.
apply T with r; auto with zarith; clear T.
Qed.

Lemma max_double_eq: (max_double = 9007199254740991*powerRZ 2 971)%R.
unfold max_double.
apply Rmult_eq_compat_l.
apply trans_eq with (Z2R 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848).
reflexivity.
replace 971%Z with (Z_of_nat 971) by reflexivity.
replace 2%R with (IZR 2) by reflexivity.
rewrite <- Zpower_nat_Z_powerRZ.
unfold Zpower_nat.
simpl (iter_nat 971 Z (fun x : Z => (2 * x)%Z) 1%Z).
now rewrite <- Z2R_IZR.
Qed. 

End Equiv.

Ltac destruct2 h := 
    let toto := fresh "toto" in
      rename h into toto; 
    let c:=fresh "C_"h in  let r1:=fresh "e_"h in let r2:=fresh "m_"h in 
    destruct toto as (h, c, r1,r2) .


Ltac simpl_mk_double := match goal with
   |- context [df         (mk_double ?f ?C ?r1 ?r2)] => 
                  (simpl  (df         (mk_double f C r1 r2)))
|  |- context [double_exact (mk_double ?f ?C ?r1 ?r2)] => 
                  (simpl  (double_exact (mk_double f C r1 r2)))
|  |- context [double_model (mk_double ?f ?C ?r1 ?r2)] => 
                  (simpl  (double_model (mk_double f C r1 r2)))
| h: context [df         (mk_double ?f ?C ?r1 ?r2)] |- _ => 
                  (simpl  (df        (mk_double f C r1 r2)) in h)
| h: context [double_exact  (mk_double ?f ?C ?r1 ?r2)] |- _ => 
                  (simpl  (double_exact  (mk_double f C r1 r2)) in h)
| h: context [double_model  (mk_double ?f ?C ?r1 ?r2)] |- _ => 
                  (simpl  (double_model (mk_double f C r1 r2)) in h)
| h: context [mk_double ?f ?C ?r1 ?r2 = ?d] |- _ =>
    (assert (FtoR radix f = FtoR radix (df d)) by (rewrite <- h; reflexivity);
       assert (r1 = double_exact d) by (rewrite <- h; reflexivity);
        assert (r2 = double_model d) by (rewrite <- h; reflexivity);
         clear h)
  end.

Ltac simpl_mk_single := match goal with
|  |- context [sf          (mk_single ?f ?C ?r1 ?r2)] => 
                  (simpl (sf     (mk_single f C r1 r2)))
|  |- context [single_exact  (mk_single ?f ?C ?r1 ?r2)] => 
                  (simpl (single_exact (mk_single f C r1 r2)))
|  |- context [single_model  (mk_single ?f ?C ?r1 ?r2)] => 
                  (simpl (single_model (mk_single f C r1 r2)))
| h: context [sf      (mk_single ?f ?C ?r1 ?r2)] |- _ => 
                  (simpl (sf         (mk_single f C r1 r2)) in h)
| h: context [single_exact   (mk_single ?f ?C ?r1 ?r2)] |- _ => 
                  (simpl (single_exact (mk_single f C r1 r2)) in h)
| h: context [single_model   (mk_single ?f ?C ?r1 ?r2)] |- _ => 
                  (simpl (single_model (mk_single f C r1 r2)) in h)
| h: context [mk_single ?f ?C ?r1 ?r2 = ?d] |- _ =>
    (assert (FtoR radix f = FtoR radix (sf d)) by (rewrite <- h; reflexivity);
       assert (r1 = single_exact d) by (rewrite <- h; reflexivity);
        assert (r2 = single_model d) by (rewrite <- h; reflexivity);
         clear h)
  end.

Ltac destruct2_ds := match goal with
    h : double   |- _ =>  destruct2 h 
  | h : single    |- _ =>  destruct2 h end.


Ltac simpl_IZR_aux := match goal with
  |- context [ IZR ?i ] => 
         (rewrite <- Gappa_integer.Z2R_IZR; simpl (Gappa_integer.Z2R i))
  | h: context  [ IZR ?i ] |- _ => 
        (rewrite <- Gappa_integer.Z2R_IZR in h; simpl (Gappa_integer.Z2R i) in h)
  end.


Ltac simpl_IZR_aux2 := match goal with
  |- context [ (-(?n))%Z ] => (simpl (-(n))%Z)
  | h: context  [ (-(?n))%Z ] |- _ => (simpl (-(n))%Z in h)
  end.


Ltac simpl_IZR := repeat simpl_IZR_aux; repeat simpl_IZR_aux2.

Lemma Rabs_eq: forall x y:R, (Rabs (x-y)=0 -> x=y).
intros.
case (Req_dec (x-y) 0); auto with real.
intros; absurd (Rabs (x-y)=0)%R; auto with real.
apply Rabs_no_R0; trivial.
Qed. 

Ltac Rabs_eq_transform := match goal with
  h : ( Rabs ( ?x - ?y ) = R0 ) |-_ => 
    (let hh:=fresh "h" in  
           generalize h; clear h; intros hh;
          assert (h:x=y);[apply Rabs_eq; exact hh|clear hh])
  end.

Ltac simpl_post := 
  let h1:=fresh "H" in  let h2:=fresh "H" in 
    match goal with
  h: add_double_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: sub_double_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: mul_double_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: div_double_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: sqrt_double_post _ _ _   |- _ => destruct h as (h,(h1,h2)) 
| h: neg_double_post  _ _   |- _ => destruct h as (h,(h1,h2)) 
| h: abs_double_post  _ _    |- _ => destruct h as (h,(h1,h2))
| h: double_of_real_post  _ _ _   |- _ => destruct h as (h,(h1,h2))
| h: add_single_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: sub_single_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: mul_single_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: div_single_post _ _ _ _  |- _ => destruct h as (h,(h1,h2)) 
| h: sqrt_single_post _ _ _   |- _ => destruct h as (h,(h1,h2)) 
| h: neg_single_post  _ _   |- _ => destruct h as (h,(h1,h2)) 
| h: abs_single_post  _ _   |- _ => destruct h as (h,(h1,h2))
| h: single_of_real_post  _ _ _   |- _ => destruct h as (h,(h1,h2))
end.

Ltac why2float := repeat simpl_post;
                  unfold double_round_error, double_total_error, no_overflow_double,
                      single_round_error, single_total_error, no_overflow_single,
                      round_double, round_double_aux, round_single, round_single_aux,
		      double_value, single_value
                  in * ; 
                   repeat destruct2_ds;
                   repeat simpl_mk_double; repeat simpl_mk_single;
                   repeat Rabs_eq_transform;
	            fold FtoRradix in *.


Lemma equiv_RNDs_d: forall (r:R),
   (FtoR radix (RND_EvenClosest bdouble radix 53 r) 
     = gappa_rounding (rounding_float roundNE 53 (1074)) r)%R.
intros; rewrite equiv_RNDs; auto with zarith.
Qed.

Lemma equiv_RNDs_s: forall (r:R),
   (FtoR radix (RND_EvenClosest bsingle radix 24 r) 
     = gappa_rounding (rounding_float roundNE 24 (149)) r)%R.
intros; rewrite equiv_RNDs; auto with zarith.
Qed.


Ltac why2gappa := simpl_IZR; why2float ; 
                 repeat rewrite equiv_RNDs_d  in * |- *; 
                 repeat rewrite equiv_RNDs_s  in * |- *; 
	         repeat rewrite max_double_eq in * |- *; unfold radix.



