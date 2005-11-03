(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.
Require Import heap.
Require Import Inftree.
Require Import ZArithRing.

Lemma double_div2 : forall x:Z, Zdiv2 (2 * x) = x.
Proof.
simple destruct x; auto.
Qed.

Lemma double_div2_bis : forall x:Z, (0 <= x)%Z -> Zdiv2 (2 * x + 1) = x.
Proof.
simple destruct x; auto.
intros.
simpl in H.
absurd (0 <= Zneg p)%Z.
simpl.
 compute.
 auto.
 assumption.
Qed.

Lemma lem_div2_0 :
 forall n:Z, (1 <= n)%Z -> (-1 <= Zdiv2 (n - 2) <= n - 1)%Z.
Proof.
intros.
elim (Z_lt_ge_dec 1 n); intro.
elim (Z_modulo_2 n).
intro H0; elim H0; clear H0; intros.
replace (n - 2)%Z with (2 * (x - 1))%Z.
rewrite double_div2.
omega.
 omega.
intro H0; elim H0; clear H0; intros.
replace (n - 2)%Z with (2 * (x - 1) + 1)%Z.
rewrite double_div2_bis.
omega.
 omega.
 omega.
 replace n with 1%Z.
simpl.
 omega.
 omega.
Qed.

Lemma lem_div2_1 : forall n:Z, (1 <= n)%Z -> (0 <= Zdiv2 (n - 2) + 1)%Z.
Proof.
intros n Hn.
 generalize (lem_div2_0 n Hn).
 omega.
Qed.

Lemma lem_div2_2 :
 forall n i:Z,
   (1 <= n)%Z ->
   (Zdiv2 (n - 2) + 1 <= i <= n - 1)%Z -> (2 * i >= n - 1)%Z.
Proof.
intros n i Hn.
elim (Z_lt_ge_dec 1 n); intro.
elim (Z_modulo_2 n).
intro H0; elim H0; clear H0; intros x Hx.
replace (n - 2)%Z with (2 * (x - 1))%Z.
rewrite double_div2.
omega.
 omega.
 intro H0; elim H0; clear H0; intros x Hx.
replace (n - 2)%Z with (2 * (x - 1) + 1)%Z.
rewrite double_div2_bis.
omega.
 omega.
 omega.
 replace n with 1%Z.
simpl.
 omega.
 omega.
Qed.


(* Obligations. *)

Proof.
intuition.
Qed.

Proof.
intuition SameLength t1 t0; try omega.
rewrite H10; auto with *.
apply permut_trans with (t' := t0); assumption.
unfold Zwf; Omega'.
Qed.

Proof.
intros.
generalize (lem_div2_0 (array_length t) Pre16); intuition try Omega'.
apply heap_leaf.
generalize (lem_div2_1 (array_length t) Pre16); Omega'.
apply (lem_div2_2 (array_length t) i); trivial || Omega'.
auto with datatypes.
Qed.

Proof.
intuition.
SameLength t0 t; auto with *.
Qed.

Proof.
intuition.
Qed.

Proof.
intuition.
SameLength t2 t1; omega.
apply heap_id with (t := t1).
apply heap_weakening.
 Omega'.
apply H1; Omega'.
 Omega'.
decompose [exchange] Post15; clear Post15.
unfold array_id.
intros i0 Hi0.
 symmetry.
 apply H18; Omega'.
Qed.

Proof.
intuition.
SameLength t3 t2; omega.
(* heap *)
subst k2; apply H17; Omega'.
(* t[0] <= t[k] *)
subst k2; ring (k1 - 1 + 1)%Z.
 rewrite (H16 k1); [ idtac | Omega' ].
decompose [exchange] Post15.
rewrite H24.
apply inftree_1 with (n := (k1 - 1)%Z).
apply H19.
apply inftree_weakening.
 Omega'.
apply inftree_exchange with (t1 := t1).
 Omega'.
apply inftree_3.
apply H1; Omega'.
assumption.
 Omega'.
(* sorted *)
subst k2; ring (k1 - 1 + 1)%Z.
  elim (Z_le_lt_eq_dec k1 (array_length t1 - 1) H6); intro.
  (* k0 < N-1 *)
  replace k1 with (k1 + 1 - 1)%Z; [ idtac | Omega' ].
  apply left_extension.
 Omega'.
 Omega'.
  apply sorted_array_id with (t1 := t2).
   apply sorted_array_id with (t1 := t1).
   SameLength t3 t2; SameLength t2 t1; SameLength t1 t.
  rewrite H20; rewrite H21.
 apply H7; Omega'.
  decompose [exchange] Post15.
  unfold array_id.
 intros i Hi.
 symmetry.
   SameLength t3 t2; apply H25; try Omega'.
  unfold array_id.
 intros i Hi.
 symmetry.
 apply H16; Omega'.
  (* t3[k0] <= t3[k0+1] *)
  ring (k1 + 1 - 1)%Z.
   rewrite (H16 k1); [ idtac | Omega' ].
  rewrite (H16 (k1 + 1)%Z);
   [ idtac | SameLength t3 t2; SameLength t2 t1; Omega' ].
  decompose [exchange] Post15.
  rewrite H24.
 rewrite (H25 (k1 + 1)%Z); [ idtac | Omega' | Omega' | Omega' ].
  apply H4; Omega'.
  (* k0 = N-1 *)
  rewrite b.
   unfold sorted_array.
  intros HN x HHx Hx.
   absurd (x >= array_length t3 - 1)%Z; SameLength t3 t2;
    SameLength t2 t1; Omega'.
(* (permut t3 t) *)
apply permut_trans with (t' := t2); try assumption.
 apply permut_trans with (t' := t1).
apply exchange_is_permut with (i := 0%Z) (j := k1).
 assumption.
 assumption.
 Qed.

Proof.
intuition SameLength t0 t; try omega.
apply heap_all.
subst k; assumption.
tauto.
intro; absurd (array_length t0 - 1 + 1 <= array_length t0 - 1)%Z;
 Omega'.
Qed.

Proof.
intuition.
elim (Z_le_lt_eq_dec 1 (array_length t) Pre16); intro.
  (* 1 < N *)
  replace 0%Z with (1 - 1)%Z; [ idtac | Omega' ].
  apply left_extension.
 Omega'.
 Omega'.
  replace 1%Z with (k1 + 1)%Z; [ idtac | Omega' ].
  replace (array_length t1 - (k1 + 1))%Z with (array_length t1 - 1)%Z;
   [ idtac | Omega' ].
  apply H6; SameLength t1 t; Omega'.
  replace (1 - 1)%Z with 0%Z; [ idtac | Omega' ].
 (* Ring `1-1`. *)
  replace 1%Z with (k1 + 1)%Z; [ idtac | Omega' ].
  apply H4; SameLength t1 t; Omega'.
  (* 1 = N *)
  unfold sorted_array.
   intros HN x HHx Hx.
   absurd (x >= array_length t - 1)%Z; SameLength t1 t; Omega'.
Qed.

Require Import swap_why.
Require Import downheap_why.


