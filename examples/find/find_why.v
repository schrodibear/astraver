(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export find_spec.
Require Import find_lemmas.
Require Import find_proofs.

Require Import Why.
Require Import Omega.


Proof.
intros; generalize le_f_N; generalize le_1_f.
intuition; SameLength A0 A; omega.
Qed.

Proof.
intuition SameLength A1 A.
unfold i_invariant in H13; omega.
omega.
Qed.

Proof.
intros.
 subst r.
subst i3.
generalize
 (subgoal_1 m1 n1 i1 j1 i2 A A0 A1 Inv_mn Test14 zero_f_SN Inv_ij Test9
    Inv_i Test4).
intuition.
Qed.

Proof.
intuition.
unfold j_invariant in H8; unfold termination in H12; omega.
Qed.

Proof.
intuition SameLength A1 A.
unfold j_invariant in H8; unfold termination in H12; omega.
unfold j_invariant in H8; unfold termination in H12; omega.
Qed.

Proof.
intros.
 subst r.
subst j3.
generalize
 (subgoal_2 m1 n1 i1 j1 i2 j2 A A0 A1 Inv_mn Test14 zero_f_SN Inv_ij
    Test9 Inv_i Inv_j Test6).
intuition.
Qed.

Proof.
intuition.
unfold m_invariant in H7.
unfold termination in H12.
omega.
Qed.

Proof.
intuition.
Qed.

Proof.
intuition SameLength A1 A.
unfold i_invariant in H16; omega.
unfold i_invariant in H16; omega.
Qed.

Proof.
intuition SameLength A1 A.
unfold termination in H28; unfold j_invariant in H25; omega.
unfold termination in H28; unfold j_invariant in H25; omega.
Qed.

Proof.
intuition WhyArrays.
ArraySubst A2; omega.
Qed.

Proof.
intros.
subst r.
assert (H: exchange A3 A1 i2 j2).
subst A3.
 subst A2.
 subst w.
auto with datatypes.

assert (H0: (access A3 i2 <= access A0 f)).
elim H; intros; rewrite H3; omega.
assert (H1: (access A0 f <= access A3 j2)).
elim H; intros; rewrite H5; omega.
generalize
 (subgoal_3 m1 n1 i1 j1 i2 j2 A A0 A1 A3 Pre27 Inv_mn Test14 zero_f_SN
    Inv_ij Test9 Inv_i Inv_j Pre22 Test8 H H0 H1).
intuition subst; intuition.
Qed.

Proof.
intuition.
 Qed.

Proof.
intros; subst r i j; intuition.
apply Lemma_4_14; auto.
elim H; elim H3; omega.
apply Lemma_5_14'; auto.
elim H; elim H3; omega.
unfold termination; right; elim H; elim H3; intros; split.
omega.
auto.
Qed.

Proof.
intuition elim H13; omega.
Qed.

Proof.
intros; subst n2 r.
assert (array_length A0 = array_length A).
intuition; ProveSameLength A0 A.
rewrite H in Pre25; rewrite Pre27 in Pre25.
generalize
 (subgoal_5 m1 n1 i1 j1 A A0 A1 Inv_mn Test14 Pre25 Inv_ij Pre24 Test13).
intuition.
Qed.

Proof.
intros; subst m2 r.
assert (array_length A0 = array_length A).
intuition; ProveSameLength A0 A.
rewrite H in Pre25; rewrite Pre27 in Pre25.
generalize
 (subgoal_6 m1 n1 i1 j1 A A0 A1 Inv_mn Test14 Pre25 Inv_ij Pre24 Test12
    Test11).
intuition.
Qed.

Proof.
intros; subst n2 m2 r.
assert (array_length A0 = array_length A).
intuition; ProveSameLength A0 A.
rewrite H in Pre25; rewrite Pre27 in Pre25.
generalize
 (subgoal_7 m1 n1 i1 j1 A A0 A1 Inv_mn Test14 Pre25 Inv_ij Pre24 Test12
    Test10).
intuition.
Qed.

Proof.
intuition.
subst m; exact (Lemma_1 A).
subst n; exact (Lemma_2 A).
Qed.

Proof.
intuition.
apply Lemma_3 with (m := m1) (n := n1); auto.
Qed.


