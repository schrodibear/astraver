
Require Why.
Require ZArith.
Require Zcomplements.
Require Omega. 

Tactic Definition Omega' := Abstract Omega.

(* Parameters and axioms *)

(*Why*) Parameter v : Z.

(* Specification *)

Inductive In [t:(array Z); l,u:Z] : Prop :=
  In_cons : (i:Z) `l <= i <= u` -> #t[i]=v -> (In t l u).

Definition mean := [x,y:Z](Zdiv2 `x+y`).

(* Lemmas *)

Lemma le_mean : (x,y:Z)
  `0 <= x <= y` -> `x <= (mean x y)`.
Proof.
Intros.
Apply Zle_Zmult_right2 with z:=`2`.
Omega.
Rewrite Zmult_sym.
Rewrite (Zmult_sym (mean x y) `2`).
Unfold mean.
Elim (Zeven_odd_dec `x+y`); Intro.
Rewrite <- Zeven_div2 with `x+y`.
Omega.
Assumption.
Elim (Z_eq_dec x y); Intro.
Absurd x=y; Try Assumption.
Rewrite a in b.
Absurd (Zodd `y+y`); Try Assumption.
Absurd `y+y = 2*(Zdiv2 (y+y))+1`.
Omega.
Apply Zodd_div2.
Omega.
Assumption.
Cut `x+y = 2*(Zdiv2 (x+y))+1`.
Omega.
Apply Zodd_div2.
Omega.
Assumption.
Save.

Lemma ge_mean : (x,y:Z)
  `0 <= x <= y` -> `(mean x y) <= y`.
Proof.
Intros.
Apply Zle_Zmult_right2 with z:=`2`.
Omega.
Rewrite Zmult_sym.
Rewrite (Zmult_sym y `2`).
Unfold mean.
Elim (Zeven_odd_dec `x+y`); Intro.
Rewrite <- Zeven_div2 with `x+y`.
Omega.
Assumption.
Cut `x+y = 2*(Zdiv2 (x+y))+1`.
Omega.
Apply Zodd_div2.
Omega.
Assumption.
Save.

Lemma In_right_side : (t:(array Z))
  (sorted_array t `1` `(array_length t)-1`) ->
  (l,u:Z)
  `1 <= l` -> `u <= (array_length t)-1` -> `l <= u` -> `l <= (mean l u) <= u` ->
  ((In t `1` `(array_length t)-1`) -> (In t l u)) ->
  `(access t (mean l u)) < v` ->
  ((In t `1` `(array_length t)-1`) -> (In t `(mean l u)+1` u)).
Proof.     
Intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
Generalize (Inv H). Intro.
Decompose [In] H0.
Apply In_cons with i.
Elim (Z_gt_le_dec `(mean l u)+1` i); Intro.
Absurd (access t i)=v.
Apply Zlt_not_eq.
Apply Zle_lt_trans with (access t (mean l u)).
Apply sorted_elements with n:=`1` m:=`(array_length t)-1`.
Assumption.
Omega'.
Omega'.
Omega'.
Omega'.
Assumption.
Assumption.
Omega'.
Assumption.
Save.

Lemma In_left_side : (t:(array Z))
  (sorted_array t `1` `(array_length t)-1`) ->
  (l,u:Z)
  `1 <= l` -> `u <= (array_length t)-1` -> `l <= u` -> `l <= (mean l u) <= u` ->
  ((In t `1` `(array_length t)-1`) -> (In t l u)) ->
  `(access t (mean l u)) > v` ->
  ((In t `1` `(array_length t)-1`) -> (In t l `(mean l u)-1`)).
Proof.     
Intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
Generalize (Inv H). Intro.
Decompose [In] H0.
Apply In_cons with i.
Elim (Z_gt_le_dec i `(mean l u)-1`); Intro.
Absurd (access t i)=v.
Apply sym_not_eq.
Apply Zlt_not_eq.
Apply Zlt_le_trans with (access t (mean l u)).
Omega'.
Apply sorted_elements with n:=`1` m:=`(array_length t)-1`.
Assumption.
Omega'.
Omega'.
Omega'.
Omega'.
Assumption.
Omega'.
Assumption.
Save.

(* Obligations *)

(* Why obligation from file "bsearch.mlw", characters 563-580 *)
Lemma binary_search_po_1 : 
  (t: (array Z))
  (Pre15: `(array_length t) >= 1` /\
          (sorted_array t `1` `(array_length t) - 1`))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = `(array_length t) - 1`)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre14: Variant1 = `2 + u1 - l1`)
  (Pre13: `1 <= l1` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
          `p1 <= (array_length t) - 1`) /\
          ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
          ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  `l1 <= m1` /\ `m1 <= u1`.
Proof. 
Intros.
Split. Rewrite Post4; Apply le_mean; Omega'.
Rewrite Post4; Apply ge_mean; Omega'.
Save.

(* Why obligation from file "bsearch.mlw", characters 593-598 *)
Lemma binary_search_po_2 : 
  (t: (array Z))
  (Pre15: `(array_length t) >= 1` /\
          (sorted_array t `1` `(array_length t) - 1`))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = `(array_length t) - 1`)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre14: Variant1 = `2 + u1 - l1`)
  (Pre13: `1 <= l1` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
          `p1 <= (array_length t) - 1`) /\
          ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
          ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre12: `l1 <= m1` /\ `m1 <= u1`)
  `0 <= m1` /\ `m1 < (array_length t)`.
Proof.
Intros.
Omega'.
Save.

(* Why obligation from file "bsearch.mlw", characters 616-627 *)
Lemma binary_search_po_3 : 
  (t: (array Z))
  (Pre15: `(array_length t) >= 1` /\
          (sorted_array t `1` `(array_length t) - 1`))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = `(array_length t) - 1`)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre14: Variant1 = `2 + u1 - l1`)
  (Pre13: `1 <= l1` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
          `p1 <= (array_length t) - 1`) /\
          ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
          ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre12: `l1 <= m1` /\ `m1 <= u1`)
  (Pre11: `0 <= m1` /\ `m1 < (array_length t)`)
  (Test5: `(access t m1) < v`)
  (l2: Z)
  (Post5: l2 = `m1 + 1`)
  (`1 <= l2` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
  `p1 <= (array_length t) - 1`) /\
  ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l2 u1)))) /\
  ((`p1 > 0` -> `(access t p1) = v`))) /\
  (Zwf `0` `2 + u1 - l2` `2 + u1 - l1`).
Proof.
Intros.
Repeat Split; Try Omega'.
Subst l2 m1.
Intros; Apply In_right_side; Assumption Orelse Intuition.
Save.

(* Why obligation from file "bsearch.mlw", characters 665-676 *)
Lemma binary_search_po_4 : 
  (t: (array Z))
  (Pre15: `(array_length t) >= 1` /\
          (sorted_array t `1` `(array_length t) - 1`))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = `(array_length t) - 1`)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre14: Variant1 = `2 + u1 - l1`)
  (Pre13: `1 <= l1` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
          `p1 <= (array_length t) - 1`) /\
          ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
          ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre12: `l1 <= m1` /\ `m1 <= u1`)
  (Pre11: `0 <= m1` /\ `m1 < (array_length t)`)
  (Test4: `(access t m1) >= v`)
  (Pre10: `0 <= m1` /\ `m1 < (array_length t)`)
  (Test3: `(access t m1) > v`)
  (u2: Z)
  (Post6: u2 = `m1 - 1`)
  (`1 <= l1` /\ `u2 <= (array_length t) - 1` /\ (`0 <= p1` /\
  `p1 <= (array_length t) - 1`) /\
  ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u2)))) /\
  ((`p1 > 0` -> `(access t p1) = v`))) /\
  (Zwf `0` `2 + u2 - l1` `2 + u1 - l1`).
Proof.
Intuition.
Subst u2 m1.
Intros; Apply In_left_side; Assumption Orelse Intuition.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "bsearch.mlw", characters 688-747 *)
Lemma binary_search_po_5 : 
  (t: (array Z))
  (Pre15: `(array_length t) >= 1` /\
          (sorted_array t `1` `(array_length t) - 1`))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = `(array_length t) - 1`)
  (p0: Z)
  (Post3: p0 = `0`)
  (Variant1: Z)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Pre14: Variant1 = `2 + u1 - l1`)
  (Pre13: `1 <= l1` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
          `p1 <= (array_length t) - 1`) /\
          ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
          ((`p1 > 0` -> `(access t p1) = v`)))
  (Test6: `l1 <= u1`)
  (m1: Z)
  (Post4: m1 = (mean l1 u1))
  (Pre12: `l1 <= m1` /\ `m1 <= u1`)
  (Pre11: `0 <= m1` /\ `m1 < (array_length t)`)
  (Test4: `(access t m1) >= v`)
  (Pre10: `0 <= m1` /\ `m1 < (array_length t)`)
  (Test2: `(access t m1) <= v`)
  (p2: Z)
  (Post7: p2 = m1)
  (l2: Z)
  (Post8: l2 = `u1 + 1`)
  (`1 <= l2` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p2` /\
  `p2 <= (array_length t) - 1`) /\
  ((`p2 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l2 u1)))) /\
  ((`p2 > 0` -> `(access t p2) = v`))) /\
  (Zwf `0` `2 + u1 - l2` `2 + u1 - l1`).
Proof.
Intuition.
Absurd `p2 = 0`; Omega'.
Subst p2; Omega.
Unfold Zwf; Omega.
Save.

(* Why obligation from file "bsearch.mlw", characters 327-498 *)
Lemma binary_search_po_6 : 
  (t: (array Z))
  (Pre15: `(array_length t) >= 1` /\
          (sorted_array t `1` `(array_length t) - 1`))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = `(array_length t) - 1`)
  (p0: Z)
  (Post3: p0 = `0`)
  `1 <= l0` /\ `u0 <= (array_length t) - 1` /\ (`0 <= p0` /\
  `p0 <= (array_length t) - 1`) /\
  ((`p0 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l0 u0)))) /\
  ((`p0 > 0` -> `(access t p0) = v`)).
Proof.
Intuition.
Subst l0 u0; Assumption.
Save.

(* Why obligation from file "bsearch.mlw", characters 169-861 *)
Lemma binary_search_po_7 : 
  (t: (array Z))
  (Pre15: `(array_length t) >= 1` /\
          (sorted_array t `1` `(array_length t) - 1`))
  (l0: Z)
  (Post1: l0 = `1`)
  (u0: Z)
  (Post2: u0 = `(array_length t) - 1`)
  (p0: Z)
  (Post3: p0 = `0`)
  (l1: Z)
  (p1: Z)
  (u1: Z)
  (Post9: (`1 <= l1` /\ `u1 <= (array_length t) - 1` /\ (`0 <= p1` /\
          `p1 <= (array_length t) - 1`) /\
          ((`p1 = 0` -> ((In t `1` `(array_length t) - 1`) -> (In t l1 u1)))) /\
          ((`p1 > 0` -> `(access t p1) = v`))) /\ `l1 > u1`)
  (`1 <= p1` /\ `p1 <= (array_length t) - 1`) /\ `(access t p1) = v` \/
  `p1 = 0` /\ ~(In t `1` `(array_length t) - 1`).
Proof.
Intuition.
Elim (Z_lt_ge_dec `0` p1); Intro.
Left; Omega'.
Right. 
Cut `p1 = 0`; [ Intro | Omega' ].
Split. Assumption.
Intro. 
Generalize (H4 H6 H9); Intro.
Decompose [In] H10.
Absurd `l1 <= i <= u1`; Omega'.
Save.


