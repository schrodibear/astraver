
Require Import Why.
Require Import ZArith.
Require Import Zcomplements.
Require Import Omega.
 
Ltac Omega' := abstract omega.

(* Parameters and axioms *)

Parameter v : Z.

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

 Proof.
 intros.
split.
 rewrite Post5; apply le_mean; Omega'.
rewrite Post5; apply ge_mean; Omega'.
Qed.

Proof.
intros.
Omega'.
Qed.

Proof.
intros.
repeat split; try Omega'.
subst l2 m1.
intros; apply In_right_side; assumption || intuition.
Qed.

Proof.
intuition.
subst u2 m1.
intros; apply In_left_side; assumption || intuition.
Qed.

Proof.
intuition.
absurd (p2 = 0%Z); Omega'.
subst p2; omega.
Qed.

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

Proof.
intuition.
subst l0 u0; assumption.
Qed.


