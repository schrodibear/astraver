
Require Import Sumbool.
Require Import Why.
Require Import Omega.
Require Import ZArithRing.

Require Import Zcomplements.
Require Import Zpower.

Definition square x := (x * x)%Z.
Definition double x := (2 * x)%Z.

Definition div2 := Zdiv2.

Definition is_odd x :=
  bool_of_sumbool (sumbool_not _ _ (Zeven_odd_dec x)).

(* Some auxiliary lemmas about Zdiv2 are necessary *)

Lemma Zdiv2_ge_0 : forall x:Z, (x >= 0)%Z -> (Zdiv2 x >= 0)%Z.
Proof.
simple destruct x; auto with zarith.
simple destruct p; auto with zarith.
simpl.
 omega.
intros.
 absurd (Zneg p >= 0)%Z; red; auto with zarith.
Qed.

Lemma Zdiv2_lt : forall x:Z, (x > 0)%Z -> (Zdiv2 x < x)%Z.
Proof.
simple destruct x.
intro.
 absurd (0 > 0)%Z; [ omega | assumption ].
simple destruct p; auto with zarith.

simpl.
intro p0.
replace (Zpos (xI p0)) with (2 * Zpos p0 + 1)%Z.
omega.
simpl.
 auto with zarith.

intro p0.
simpl.
replace (Zpos (xO p0)) with (2 * Zpos p0)%Z.
omega.
simpl.
 auto with zarith.

simpl.
 omega.

intros.
 absurd (Zneg p > 0)%Z; red; auto with zarith.
elim p; auto with zarith.
Qed.

(* A property of Zpower:  x^(2*n) = (x^2)^n *)

Lemma Zpower_2n :
 forall x n:Z, (n >= 0)%Z -> Zpower x (double n) = Zpower (square x) n.
Proof.
unfold double.
intros x0 n Hn.
replace (2 * n)%Z with (n + n)%Z.
rewrite Zpower_exp.
pattern n.
apply natlike_ind.

simpl.
 auto with zarith.

intros.
unfold Zsucc.
rewrite Zpower_exp.
rewrite Zpower_exp.
replace (Zpower x0 1) with x0.
replace (Zpower (square x0) 1) with (square x0).
rewrite <- H0.
unfold square.
ring.

unfold Zpower; unfold Zpower_pos; simpl.
 omega.

unfold Zpower; unfold Zpower_pos; simpl.
 omega.

omega.
omega.
omega.
omega.
omega.
assumption.
assumption.
omega.
Qed.

(* Obligations *)

(*Why*) Parameter x : Z.

(* Why obligation from file "power.mlw", characters 553-565 *)
Lemma power1_po_1 : 
  forall (m: Z),
  forall (n: Z),
  forall (Pre4: n >= 0),
  forall (m0: Z),
  forall (Post1: m0 = x),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (m1: Z),
  forall (n0: Z),
  forall (y1: Z),
  forall (Pre3: Variant1 = n0),
  forall (Pre2: (Zpower x n) = (y1 * (Zpower m1 n0)) /\ n0 >= 0),
  forall (Test4: n0 > 0),
  forall (Test3: (Zodd n0)),
  forall (y2: Z),
  forall (Post5: y2 = (y1 * m1)),
  forall (m: Z),
  forall (HW_3: m = (m1 * m1)),
  forall (n1: Z),
  forall (HW_4: n1 = (div2 n0)),
  ((Zpower x n) = (y2 * (Zpower m n1)) /\ n1 >= 0) /\ (Zwf 0 n1 n0).
Proof.
simpl; intros.
repeat split; try omega.
decompose [and] Pre2; clear Pre2.
rewrite (Zodd_div2 n0 H0 Test3) in H.
 rewrite H.
rewrite Zpower_exp.
replace (Zpower m1 1) with m1.
rewrite Zpower_2n.
unfold square.
subst m2 n1 y2; unfold div2.
ring.
generalize (Zdiv2_ge_0 n0); omega.
unfold Zpower; unfold Zpower_pos; simpl; ring.
generalize (Zdiv2_ge_0 n0); omega.
omega.
subst; apply Zdiv2_ge_0; omega.
subst; apply Zdiv2_lt; omega.
Qed.

(* Why obligation from file "power.mlw", characters 565-565 *)
Lemma power1_po_2 : 
  forall (m: Z),
  forall (n: Z),
  forall (Pre4: n >= 0),
  forall (m0: Z),
  forall (Post1: m0 = x),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (m1: Z),
  forall (n0: Z),
  forall (y1: Z),
  forall (Pre3: Variant1 = n0),
  forall (Pre2: (Zpower x n) = (y1 * (Zpower m1 n0)) /\ n0 >= 0),
  forall (Test4: n0 > 0),
  forall (Test2: (Zeven n0)),
  forall (result3: unit),
  forall (Post4: result3 = tt),
  forall (m: Z),
  forall (HW_7: m = (m1 * m1)),
  forall (n1: Z),
  forall (HW_8: n1 = (div2 n0)),
  ((Zpower x n) = (y1 * (Zpower m n1)) /\ n1 >= 0) /\ (Zwf 0 n1 n0).
Proof.
simpl; intros.
repeat split; try omega.
decompose [and] Pre2; clear Pre2.
rewrite (Zeven_div2 n0 Test2) in H.
 rewrite H.
rewrite Zpower_2n.
unfold square.
subst; unfold div2.
ring.
generalize (Zdiv2_ge_0 n0); omega.
subst; apply Zdiv2_ge_0; omega.
subst; apply Zdiv2_lt; omega.
Qed.

(* Why obligation from file "power.mlw", characters 427-616 *)
Lemma power1_po_3 : 
  forall (n: Z),
  forall (Pre4: n >= 0),
  forall (m0: Z),
  forall (Post1: m0 = x),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (m1: Z),
  forall (n0: Z),
  forall (y1: Z),
  forall (Pre3: Variant1 = n0),
  forall (Pre2: (Zpower x n) = (y1 * (Zpower m1 n0)) /\ n0 >= 0),
  forall (Test1: n0 <= 0),
  y1 = (Zpower x n).
Proof.
intros.
intuition.
rewrite H.
replace n0 with 0%Z.
simpl; ring.
omega.
Qed.

(* Why obligation from file "power.mlw", characters 461-506 *)
Lemma power1_po_4 : 
  forall (n: Z),
  forall (Pre4: n >= 0),
  forall (m0: Z),
  forall (Post1: m0 = x),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  (Zpower x n) = (y0 * (Zpower m0 n)) /\ n >= 0.
Proof.
intros.
split; [ idtac | omega ].
subst y0; ring.
subst m0; trivial.
Qed.


