
Require Import Why.
Require Import ZArith.
Require Import Zcomplements.
Require Import Omega.
 
Ltac Omega' := abstract omega.

(* Parameters and axioms *)

(*Why*) Parameter v : Z.

(* Specification *)

Inductive In (t:array Z) (l u:Z) : Prop :=
    In_cons : forall i:Z, (l <= i <= u)%Z -> access t i = v -> In t l u.

Definition mean (x y:Z) := Zdiv2 (x + y).

(* Lemmas *)

Lemma le_mean : forall x y:Z, (0 <= x <= y)%Z -> (x <= mean x y)%Z.
Proof.
intros.
apply Zmult_le_reg_r with (p := 2%Z).
omega.
rewrite Zmult_comm.
rewrite (Zmult_comm (mean x y) 2).
unfold mean.
elim (Zeven_odd_dec (x + y)); intro.
rewrite <- Zeven_div2 with (x + y)%Z.
omega.
assumption.
elim (Z_eq_dec x y); intro.
absurd (x = y); try assumption.
rewrite a in b.
absurd (Zodd (y + y)); try assumption.
absurd ((y + y)%Z = (2 * Zdiv2 (y + y) + 1)%Z).
omega.
apply Zodd_div2.
omega.
assumption.
cut ((x + y)%Z = (2 * Zdiv2 (x + y) + 1)%Z).
omega.
apply Zodd_div2.
omega.
assumption.
Qed.

Lemma ge_mean : forall x y:Z, (0 <= x <= y)%Z -> (mean x y <= y)%Z.
Proof.
intros.
apply Zmult_le_reg_r with (p := 2%Z).
omega.
rewrite Zmult_comm.
rewrite (Zmult_comm y 2).
unfold mean.
elim (Zeven_odd_dec (x + y)); intro.
rewrite <- Zeven_div2 with (x + y)%Z.
omega.
assumption.
cut ((x + y)%Z = (2 * Zdiv2 (x + y) + 1)%Z).
omega.
apply Zodd_div2.
omega.
assumption.
Qed.

Lemma In_right_side :
 forall t:array Z,
   sorted_array t 1 (array_length t - 1) ->
   forall l u:Z,
     (1 <= l)%Z ->
     (u <= array_length t - 1)%Z ->
     (l <= u)%Z ->
     (l <= mean l u <= u)%Z ->
     (In t 1 (array_length t - 1) -> In t l u) ->
     (access t (mean l u) < v)%Z ->
     In t 1 (array_length t - 1) -> In t (mean l u + 1) u.
     Proof.
     intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
generalize (Inv H).
 intro.
decompose [In] H0.
apply In_cons with i.
elim (Z_gt_le_dec (mean l u + 1) i); intro.
absurd (access t i = v).
apply Zlt_not_eq.
apply Zle_lt_trans with (access t (mean l u)).
apply sorted_elements with (n := 1%Z) (m := (array_length t - 1)%Z).
assumption.
Omega'.
Omega'.
Omega'.
Omega'.
assumption.
assumption.
Omega'.
assumption.
Qed.

Lemma In_left_side :
 forall t:array Z,
   sorted_array t 1 (array_length t - 1) ->
   forall l u:Z,
     (1 <= l)%Z ->
     (u <= array_length t - 1)%Z ->
     (l <= u)%Z ->
     (l <= mean l u <= u)%Z ->
     (In t 1 (array_length t - 1) -> In t l u) ->
     (access t (mean l u) > v)%Z ->
     In t 1 (array_length t - 1) -> In t l (mean l u - 1).
     Proof.
     intros t Hsorted l u Hl Hu Hlu Hm Inv Hv H.
generalize (Inv H).
 intro.
decompose [In] H0.
apply In_cons with i.
elim (Z_gt_le_dec i (mean l u - 1)); intro.
absurd (access t i = v).
apply sym_not_eq.
apply Zlt_not_eq.
apply Zlt_le_trans with (access t (mean l u)).
Omega'.
apply sorted_elements with (n := 1%Z) (m := (array_length t - 1)%Z).
assumption.
Omega'.
Omega'.
Omega'.
Omega'.
assumption.
Omega'.
assumption.
Qed.

(* Obligations *)

(* Why obligation from file "bsearch.mlw", characters 576-593 *)
Lemma binary_search_po_1 : 
  forall (t: (array Z)),
  forall (Pre15: (array_length t) >= 1 /\
                 (sorted_array t 1 ((array_length t) - 1))),
  forall (l0: Z),
  forall (Post1: l0 = 1),
  forall (u0: Z),
  forall (Post2: u0 = ((array_length t) - 1)),
  forall (p0: Z),
  forall (Post3: p0 = 0),
  forall (Variant1: Z),
  forall (l1: Z),
  forall (p1: Z),
  forall (u1: Z),
  forall (Pre14: Variant1 = (2 + u1 - l1)),
  forall (Pre13: 1 <= l1 /\ u1 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
                 ((array_length t) - 1)) /\
                 ((p1 = 0 ->
                   ((In t 1 ((array_length t) - 1)) -> (In t l1 u1)))) /\
                 ((p1 > 0 -> (access t p1) = v))),
  forall (Test6: l1 <= u1),
  forall (m1: Z),
  forall (Post4: m1 = (mean l1 u1)),
  l1 <= m1 /\ m1 <= u1.
 Proof.
 intros.
split.
 rewrite Post4; apply le_mean; Omega'.
rewrite Post4; apply ge_mean; Omega'.
Qed.

(* Why obligation from file "bsearch.mlw", characters 606-611 *)
Lemma binary_search_po_2 : 
  forall (t: (array Z)),
  forall (Pre15: (array_length t) >= 1 /\
                 (sorted_array t 1 ((array_length t) - 1))),
  forall (l0: Z),
  forall (Post1: l0 = 1),
  forall (u0: Z),
  forall (Post2: u0 = ((array_length t) - 1)),
  forall (p0: Z),
  forall (Post3: p0 = 0),
  forall (Variant1: Z),
  forall (l1: Z),
  forall (p1: Z),
  forall (u1: Z),
  forall (Pre14: Variant1 = (2 + u1 - l1)),
  forall (Pre13: 1 <= l1 /\ u1 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
                 ((array_length t) - 1)) /\
                 ((p1 = 0 ->
                   ((In t 1 ((array_length t) - 1)) -> (In t l1 u1)))) /\
                 ((p1 > 0 -> (access t p1) = v))),
  forall (Test6: l1 <= u1),
  forall (m1: Z),
  forall (Post4: m1 = (mean l1 u1)),
  forall (Pre12: l1 <= m1 /\ m1 <= u1),
  0 <= m1 /\ m1 < (array_length t).
Proof.
intros.
Omega'.
Qed.

(* Why obligation from file "bsearch.mlw", characters 629-640 *)
Lemma binary_search_po_3 : 
  forall (t: (array Z)),
  forall (Pre15: (array_length t) >= 1 /\
                 (sorted_array t 1 ((array_length t) - 1))),
  forall (l0: Z),
  forall (Post1: l0 = 1),
  forall (u0: Z),
  forall (Post2: u0 = ((array_length t) - 1)),
  forall (p0: Z),
  forall (Post3: p0 = 0),
  forall (Variant1: Z),
  forall (l1: Z),
  forall (p1: Z),
  forall (u1: Z),
  forall (Pre14: Variant1 = (2 + u1 - l1)),
  forall (Pre13: 1 <= l1 /\ u1 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
                 ((array_length t) - 1)) /\
                 ((p1 = 0 ->
                   ((In t 1 ((array_length t) - 1)) -> (In t l1 u1)))) /\
                 ((p1 > 0 -> (access t p1) = v))),
  forall (Test6: l1 <= u1),
  forall (m1: Z),
  forall (Post4: m1 = (mean l1 u1)),
  forall (Pre12: l1 <= m1 /\ m1 <= u1),
  forall (Pre11: 0 <= m1 /\ m1 < (array_length t)),
  forall (Test5: (access t m1) < v),
  forall (l2: Z),
  forall (Post5: l2 = (m1 + 1)),
  (1 <= l2 /\ u1 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
  ((array_length t) - 1)) /\
  ((p1 = 0 -> ((In t 1 ((array_length t) - 1)) -> (In t l2 u1)))) /\
  ((p1 > 0 -> (access t p1) = v))) /\ (Zwf 0 (2 + u1 - l2) (2 + u1 - l1)).
Proof.
intros.
repeat split; try Omega'.
subst l2 m1.
intros; apply In_right_side; assumption || intuition.
Qed.

(* Why obligation from file "bsearch.mlw", characters 678-689 *)
Lemma binary_search_po_4 : 
  forall (t: (array Z)),
  forall (Pre15: (array_length t) >= 1 /\
                 (sorted_array t 1 ((array_length t) - 1))),
  forall (l0: Z),
  forall (Post1: l0 = 1),
  forall (u0: Z),
  forall (Post2: u0 = ((array_length t) - 1)),
  forall (p0: Z),
  forall (Post3: p0 = 0),
  forall (Variant1: Z),
  forall (l1: Z),
  forall (p1: Z),
  forall (u1: Z),
  forall (Pre14: Variant1 = (2 + u1 - l1)),
  forall (Pre13: 1 <= l1 /\ u1 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
                 ((array_length t) - 1)) /\
                 ((p1 = 0 ->
                   ((In t 1 ((array_length t) - 1)) -> (In t l1 u1)))) /\
                 ((p1 > 0 -> (access t p1) = v))),
  forall (Test6: l1 <= u1),
  forall (m1: Z),
  forall (Post4: m1 = (mean l1 u1)),
  forall (Pre12: l1 <= m1 /\ m1 <= u1),
  forall (Pre11: 0 <= m1 /\ m1 < (array_length t)),
  forall (Test4: (access t m1) >= v),
  forall (Pre10: 0 <= m1 /\ m1 < (array_length t)),
  forall (Test3: (access t m1) > v),
  forall (u2: Z),
  forall (Post6: u2 = (m1 - 1)),
  (1 <= l1 /\ u2 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
  ((array_length t) - 1)) /\
  ((p1 = 0 -> ((In t 1 ((array_length t) - 1)) -> (In t l1 u2)))) /\
  ((p1 > 0 -> (access t p1) = v))) /\ (Zwf 0 (2 + u2 - l1) (2 + u1 - l1)).
Proof.
intuition.
subst u2 m1.
intros; apply In_left_side; assumption || intuition.
Qed.

(* Why obligation from file "bsearch.mlw", characters 701-760 *)
Lemma binary_search_po_5 : 
  forall (t: (array Z)),
  forall (Pre15: (array_length t) >= 1 /\
                 (sorted_array t 1 ((array_length t) - 1))),
  forall (l0: Z),
  forall (Post1: l0 = 1),
  forall (u0: Z),
  forall (Post2: u0 = ((array_length t) - 1)),
  forall (p0: Z),
  forall (Post3: p0 = 0),
  forall (Variant1: Z),
  forall (l1: Z),
  forall (p1: Z),
  forall (u1: Z),
  forall (Pre14: Variant1 = (2 + u1 - l1)),
  forall (Pre13: 1 <= l1 /\ u1 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
                 ((array_length t) - 1)) /\
                 ((p1 = 0 ->
                   ((In t 1 ((array_length t) - 1)) -> (In t l1 u1)))) /\
                 ((p1 > 0 -> (access t p1) = v))),
  forall (Test6: l1 <= u1),
  forall (m1: Z),
  forall (Post4: m1 = (mean l1 u1)),
  forall (Pre12: l1 <= m1 /\ m1 <= u1),
  forall (Pre11: 0 <= m1 /\ m1 < (array_length t)),
  forall (Test4: (access t m1) >= v),
  forall (Pre10: 0 <= m1 /\ m1 < (array_length t)),
  forall (Test2: (access t m1) <= v),
  forall (p2: Z),
  forall (Post7: p2 = m1),
  forall (l2: Z),
  forall (Post8: l2 = (u1 + 1)),
  (1 <= l2 /\ u1 <= ((array_length t) - 1) /\ (0 <= p2 /\ p2 <=
  ((array_length t) - 1)) /\
  ((p2 = 0 -> ((In t 1 ((array_length t) - 1)) -> (In t l2 u1)))) /\
  ((p2 > 0 -> (access t p2) = v))) /\ (Zwf 0 (2 + u1 - l2) (2 + u1 - l1)).
Proof.
intuition.
absurd (p2 = 0%Z); Omega'.
subst p2; omega.
Qed.

(* Why obligation from file "bsearch.mlw", characters 310-776 *)
Lemma binary_search_po_6 : 
  forall (t: (array Z)),
  forall (Pre15: (array_length t) >= 1 /\
                 (sorted_array t 1 ((array_length t) - 1))),
  forall (l0: Z),
  forall (Post1: l0 = 1),
  forall (u0: Z),
  forall (Post2: u0 = ((array_length t) - 1)),
  forall (p0: Z),
  forall (Post3: p0 = 0),
  forall (Variant1: Z),
  forall (l1: Z),
  forall (p1: Z),
  forall (u1: Z),
  forall (Pre14: Variant1 = (2 + u1 - l1)),
  forall (Pre13: 1 <= l1 /\ u1 <= ((array_length t) - 1) /\ (0 <= p1 /\ p1 <=
                 ((array_length t) - 1)) /\
                 ((p1 = 0 ->
                   ((In t 1 ((array_length t) - 1)) -> (In t l1 u1)))) /\
                 ((p1 > 0 -> (access t p1) = v))),
  forall (Test1: l1 > u1),
  (1 <= p1 /\ p1 <= ((array_length t) - 1)) /\ (access t p1) = v \/ p1 = 0 /\
  ~(In t 1 ((array_length t) - 1)).
Proof.
intuition.
elim (Z_lt_ge_dec 0 p1); intro.
left; Omega'.
right.
 cut (p1 = 0%Z); [ intro | Omega' ].
split.
 assumption.
intro.
 generalize (H2 H5 H8); intro.
decompose [In] H9.
absurd (l1 <= i <= u1)%Z; Omega'.
Qed.

(* Why obligation from file "bsearch.mlw", characters 350-511 *)
Lemma binary_search_po_7 : 
  forall (t: (array Z)),
  forall (Pre15: (array_length t) >= 1 /\
                 (sorted_array t 1 ((array_length t) - 1))),
  forall (l0: Z),
  forall (Post1: l0 = 1),
  forall (u0: Z),
  forall (Post2: u0 = ((array_length t) - 1)),
  forall (p0: Z),
  forall (Post3: p0 = 0),
  1 <= l0 /\ u0 <= ((array_length t) - 1) /\ (0 <= p0 /\ p0 <=
  ((array_length t) - 1)) /\
  ((p0 = 0 -> ((In t 1 ((array_length t) - 1)) -> (In t l0 u0)))) /\
  ((p0 > 0 -> (access t p0) = v)).
Proof.
intuition.
subst l0 u0; assumption.
Qed.


