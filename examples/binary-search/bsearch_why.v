
Require Correctness.
Require Sorted.
Require ZArith.
Require Zcomplements.
Require Omega. 

Tactic Definition Omega' := Abstract Omega.

(* Parameters and axioms *)

Parameter N : Z.

Axiom N_positive : `N >= 0`.

Parameter v : Z.

(* Specification *)

Inductive In [t:(array (Zs N) Z); l,u:Z] : Prop :=
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

Lemma In_right_side : (t:(array (Zs N) Z))
  (sorted_array t `1` N) ->
  (l,u:Z)
  `1 <= l` -> `u <= N` -> `l <= u` -> `l <= (mean l u) <= u` ->
  ((In t `1` N) -> (In t l u)) ->
  `(access t (mean l u)) < v` ->
  ((In t `1` N) -> (In t `(mean l u)+1` u)).
Proof.     
Intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
Generalize (Inv H). Intro.
Decompose [In] H0.
Apply In_cons with i.
Elim (Z_gt_le_dec `(mean l u)+1` i); Intro.
Absurd (access t i)=v.
Apply Zlt_not_eq.
Apply Zle_lt_trans with (access t (mean l u)).
Apply sorted_elements with n:=`1` m:=N.
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

Lemma In_left_side : (t:(array (Zs N) Z))
  (sorted_array t `1` N) ->
  (l,u:Z)
  `1 <= l` -> `u <= N` -> `l <= u` -> `l <= (mean l u) <= u` ->
  ((In t `1` N) -> (In t l u)) ->
  `(access t (mean l u)) > v` ->
  ((In t `1` N) -> (In t l `(mean l u)-1`)).
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
Apply sorted_elements with n:=`1` m:=N.
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

Lemma binary_search_po_1 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (well_founded ? (Zwf ZERO)).
Proof. Auto with *. Save.

Lemma binary_search_po_2 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (m1: Z) 
  m1 = (mean l1 u1) ->
  `l1 <= m1` /\ `m1 <= u1`.
Proof.
Intros.
Clear H3 result2 H5; Simpl in H6.
Split. Rewrite H8; Apply le_mean; Omega'.
Rewrite H8; Apply ge_mean; Omega'.
Save.

Lemma binary_search_po_3 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (m1: Z) 
  m1 = (mean l1 u1) ->
  `l1 <= m1` /\ `m1 <= u1` ->
  `0 <= m1` /\ `m1 < N + 1`.
Proof.
Intros.
Clear H3 result2 H5.
Omega'.
Save.

Lemma binary_search_po_4 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (m1: Z) 
  m1 = (mean l1 u1) ->
  `l1 <= m1` /\
  `m1 <= u1` ->
  (result4: bool) 
  (if result4 then `(access t m1) < v` else `(access t m1) >= v`) ->
  (if true then `(access t m1) < v` else `(access t m1) >= v`) ->
  (l2: Z) 
  l2 = `m1 + 1` ->
  `1 <= l2` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l2 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) /\ (Zwf `0` `2 + u1 - l2` `2 + u1 - l1`).
Proof.
Intros.
Clear H3 result2 H5; Simpl in H6.
Clear result4 H10; Simpl in H11.
Repeat Split; Try Omega'.
Rewrite H12; Clear H12; Rewrite H8.
Intros; Apply In_right_side; Assumption Orelse Intuition.
Rewrite <- H8; Assumption.
Save.

Lemma binary_search_po_5 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (m1: Z) 
  m1 = (mean l1 u1) ->
  `l1 <= m1` /\
  `m1 <= u1` ->
  (result4: bool) 
  (if result4 then `(access t m1) < v` else `(access t m1) >= v`) ->
  (if false then `(access t m1) < v` else `(access t m1) >= v`) ->
  `0 <= m1` /\ `m1 < N + 1`.
Proof.
Intros.
Clear H3 result2 H5; Simpl in H6.
Clear result4 H10; Simpl in H11.
Repeat Split; Try Omega'.
Save.

Lemma binary_search_po_6 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (m1: Z) 
  m1 = (mean l1 u1) ->
  `l1 <= m1` /\
  `m1 <= u1` ->
  (result4: bool) 
  (if result4 then `(access t m1) < v` else `(access t m1) >= v`) ->
  (if false then `(access t m1) < v` else `(access t m1) >= v`) ->
  (result5: bool) 
  (if result5 then `(access t m1) > v` else `(access t m1) <= v`) ->
  (if true then `(access t m1) > v` else `(access t m1) <= v`) ->
  (u2: Z) 
  u2 = `m1 - 1` ->
  `1 <= l1` /\ `u2 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u2)))) /\
  ((`p1 > 0` -> (access t p1) = v)) /\ (Zwf `0` `2 + u2 - l1` `2 + u1 - l1`).
Proof.
Intros.
Omega'.
Save.

Lemma binary_search_po_7 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (m1: Z) 
  m1 = (mean l1 u1) ->
  `l1 <= m1` /\
  `m1 <= u1` ->
  (result4: bool) 
  (if result4 then `(access t m1) < v` else `(access t m1) >= v`) ->
  (if false then `(access t m1) < v` else `(access t m1) >= v`) ->
  (result5: bool) 
  (if result5 then `(access t m1) > v` else `(access t m1) <= v`) ->
  (if false then `(access t m1) > v` else `(access t m1) <= v`) ->
  (p2: Z) 
  p2 = m1 ->
  (l2: Z) 
  l2 = `u1 + 1` ->
  `1 <= l2` /\ `u1 <= N` /\ `0 <= p2` /\ `p2 <= N` /\
  ((p2 = `0` -> ((In t `1` N) -> (In t l2 u1)))) /\
  ((`p2 > 0` -> (access t p2) = v)) /\ (Zwf `0` `2 + u1 - l2` `2 + u1 - l1`).
Proof.
Intros.
Clear H3 result2 H5; Simpl in H6.
Clear result4 H10; Simpl in H11.
Clear result5 H12; Simpl in H13.
Repeat Split; Try Omega'.
Intros; Absurd `p2 = 0`; Omega'.
Intro; Rewrite H14; Omega'.
Save.

Lemma binary_search_po_8 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (l2: Z) 
  (p2: Z) 
  (u2: Z) 
  `1 <= l2` /\ `u2 <= N` /\ `0 <= p2` /\ `p2 <= N` /\
  ((p2 = `0` -> ((In t `1` N) -> (In t l2 u2)))) /\
  ((`p2 > 0` -> (access t p2) = v)) /\
  (Zwf `0` `2 + u2 - l2` `2 + u1 - l1`) ->
  (Zwf `0` `2 + u2 - l2` Variant1).
Proof.
Intros.
Rewrite H4; Tauto.
Save.

Lemma binary_search_po_9 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if true then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  (l2: Z) 
  (p2: Z) 
  (u2: Z) 
  `1 <= l2` /\ `u2 <= N` /\ `0 <= p2` /\ `p2 <= N` /\
  ((p2 = `0` -> ((In t `1` N) -> (In t l2 u2)))) /\
  ((`p2 > 0` -> (access t p2) = v)) /\
  (Zwf `0` `2 + u2 - l2` `2 + u1 - l1`) ->
  `1 <= l2` /\ `u2 <= N` /\ `0 <= p2` /\ `p2 <= N` /\
  ((p2 = `0` -> ((In t `1` N) -> (In t l2 u2)))) /\
  ((`p2 > 0` -> (access t p2) = v)).
Proof.
Intros; Intuition.
Save.

Lemma binary_search_po_10 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (Variant1: Z) 
  (u1: Z) 
  (p1: Z) 
  (l1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  Variant1 = `2 + u1 - l1` ->
  (result2: bool) 
  (if result2 then `l1 <= u1` else `l1 > u1`) ->
  (if false then `l1 <= u1` else `l1 > u1`) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) ->
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) /\
  ((if false then `l1 <= u1` else `l1 > u1`)).
Proof.
Intros.
Intuition.
Save.

Lemma binary_search_po_11 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  `1 <= l0` /\ `u0 <= N` /\ `0 <= p0` /\ `p0 <= N` /\
  ((p0 = `0` -> ((In t `1` N) -> (In t l0 u0)))) /\
  ((`p0 > 0` -> (access t p0) = v)).
Proof.
Intros.
Generalize N_positive; Intro.
Repeat Split; Intros; Try Omega'.
Rewrite H0; Rewrite H1; Assumption.
Save.

Lemma binary_search_po_12 : 
  (t: (array `N + 1` Z)) 
  (sorted_array t `1` N) ->
  (l0: Z) 
  l0 = `1` ->
  (u0: Z) 
  u0 = N ->
  (p0: Z) 
  p0 = `0` ->
  (l1: Z) 
  (p1: Z) 
  (u1: Z) 
  `1 <= l1` /\ `u1 <= N` /\ `0 <= p1` /\ `p1 <= N` /\
  ((p1 = `0` -> ((In t `1` N) -> (In t l1 u1)))) /\
  ((`p1 > 0` -> (access t p1) = v)) /\
  ((if false then `l1 <= u1` else `l1 > u1`)) ->
  `1 <= p1` /\ `p1 <= N` /\ (access t p1) = v \/ p1 = `0` /\ ~(In t `1` N).
Proof.
Intros.
Intuition.
Elim (Z_lt_ge_dec `0` p1); Intro.
Left; Omega'.
Right. 
Cut `p1 = 0`; [ Intro | Omega' ].
Split. Assumption.
Intro. 
Generalize (H7 H9 H11); Intro.
Decompose [In] H12.
Absurd `l1 <= i <= u1`; Omega'.
Save.
