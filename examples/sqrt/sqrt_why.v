(********************************************************************

  A simple algorithm for computing the square root of a non-negative
  integer.

  Proofs of obligations generated by Why.

  (c) Claude MarchÃ©, may 2002

**********************************************************************)

(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)


Require Import ZArith.
Require Import Zcomplements.
Require Import ZArithRing.
Require Import Zdiv.
Require Import Omega.
Require Import Why.

(* some basic arithmetic lemmas *)

Lemma sqr_gt :
 forall x y:Z, (x > y)%Z -> (y > 0)%Z -> (x * x > y * y)%Z.
Proof.
intros.
assert (x * y > y * y)%Z.
apply Zmult_gt_compat_r; omega.
assert (x * x > x * y)%Z.
apply Zmult_gt_compat_l; omega.
omega.
Qed.

Lemma Z_mod_same : forall a:Z, (a > 0)%Z -> (a mod a)%Z = 0%Z.
Proof.
intros a aPos.
generalize (Z_mod_plus 0 1 a aPos).
replace (0 + 1 * a)%Z with a.
intros.
rewrite H.
compute.
trivial.
ring.
Qed.

Lemma Z_div_same : forall a:Z, (a > 0)%Z -> (a / a)%Z = 1%Z.
Proof.
intros a aPos.
generalize (Z_div_plus 0 1 a aPos).
replace (0 + 1 * a)%Z with a.
intros.
rewrite H.
compute.
trivial.
ring.
Qed.

(* some general lemmas for invariants *)

Lemma iter_sqrt_pos :
 forall x z:Z, (x > 0)%Z -> (z > 0)%Z -> ((x / z + z) / 2 > 0)%Z.
Proof.
intros x z xPos zPos.
assert (x / z + z >= 2)%Z.
assert (x + z * z >= z + z)%Z.
assert (x + (z - 1) * (z - 1) >= 1)%Z.
generalize (sqr_pos (z - 1)).
intros.
omega.
replace (z * z)%Z with ((z - 1) * (z - 1) + z + z - 1)%Z.
omega.
ring.
generalize (Z_div_ge (x + z * z) (z + z) z zPos H).
intro.
generalize (Z_div_plus x z z zPos).
intro H1.
rewrite H1 in H0.
clear H1.
generalize (Z_div_plus z 1 z zPos).
replace (1 * z)%Z with z.
intro H2.
rewrite H2 in H0.
clear H2.
generalize (Z_div_plus 0 1 z zPos).
replace (1 * z)%Z with z.
replace (0 + z)%Z with z.
intro.
rewrite H1 in H0.
simpl in H0.
trivial.
trivial.
ring.
ring.
assert (2 > 0)%Z.
omega.
generalize (Z_div_ge (x / z + z) 2 2 H0 H).
replace (2 / 2)%Z with 1%Z.
intro; omega.
compute.
trivial.
Qed.

Lemma iter_sqrt_pos2 : forall x:Z, (x > 0)%Z -> ((x + 1) / 2 > 0)%Z.
Proof.
intros.
assert (x + 1 >= 2)%Z.
 omega.
assert ((x + 1) / 2 >= 2 / 2)%Z.
apply Z_div_ge; try omega.
assert (2 / 2 > 0)%Z; try omega.
compute; trivial.
Qed.

Lemma iter_sqrt_invar1 :
 forall x y z:Z,
   (x > 0)%Z ->
   (y > 0)%Z -> z = ((x / y + y) / 2)%Z -> (2 * y * z <= x + y * y)%Z.
Proof.
intros x y z xPos yPos zVal.
assert (2 * z <= x / y + y)%Z.
rewrite zVal.
apply Z_mult_div_ge; omega.
assert (2 * y * z <= y * (x / y + y))%Z.
replace (2 * y * z)%Z with (y * (2 * z))%Z; try ring.
apply Zmult_le_compat_l; trivial || omega.
assert (y * (x / y + y) <= x + y * y)%Z.
assert ((y * (x / y + y))%Z = (y * (x / y) + y * y)%Z); try ring.
 assert (y * (x / y) <= x)%Z.
apply Z_mult_div_ge; omega.
omega.
omega.
Qed.

Lemma iter_sqrt_invar2 :
 forall x y z:Z,
   (x > 0)%Z ->
   (y > 0)%Z ->
   z = ((x / y + y) / 2)%Z -> (2 * y * (z + 1) > x + y * y)%Z.
Proof.
intros x y z xPos yPos zVal.
assert (TwoPos: (2 > 0)); try omega.
generalize (Z_div_mod_eq x y yPos).
generalize (Z_mod_lt x y yPos).
generalize (Z_div_mod_eq (x / y + y) 2 TwoPos).
generalize (Z_mod_lt (x / y + y) 2 TwoPos).
intros.
rewrite zVal.
replace (2 * y * ((x / y + y) / 2 + 1))%Z with
 (y * (2 * ((x / y + y) / 2)) + y + y)%Z; try ring.
replace (2 * ((x / y + y) / 2))%Z with
 (x / y + y - (x / y + y) mod 2)%Z.
replace (y * (x / y + y - (x / y + y) mod 2))%Z with
 (y * (x / y) + y * y - y * ((x / y + y) mod 2))%Z.
replace (y * (x / y))%Z with (x - x mod y)%Z.
assert (y >= y * ((x / y + y) mod 2))%Z.
pattern y at 1; replace y with (y * 1)%Z.
apply Zmult_ge_compat_l.
omega.
omega.
ring.
omega.
omega.
ring.
omega.
Qed.

Lemma iter_sqrt_invar3 :
 forall x y z:Z,
   (x > 0)%Z ->
   (y > 0)%Z -> z = ((x / y + y) / 2)%Z -> (x < (z + 1) * (z + 1))%Z.
Proof.
intros x y z xPos yPos zVal.
cut ((z + 1) * (z + 1) - x > 0)%Z; try omega.
assert (4 * y * y * ((z + 1) * (z + 1) - x) >= 1)%Z.
replace (4 * y * y * ((z + 1) * (z + 1) - x))%Z with
 (2 * y * (z + 1) * (2 * y * (z + 1)) - 4 * y * y * x)%Z; try ring.
generalize (iter_sqrt_invar2 x y z xPos yPos zVal).
intro.
assert
 (2 * y * (z + 1) * (2 * y * (z + 1)) > (x + y * y) * (x + y * y))%Z.
assert (2 * y * (z + 1) * (x + y * y) > (x + y * y) * (x + y * y))%Z.
apply Zmult_gt_compat_r.
generalize (sqr_pos y).
omega.
assumption.
assert
 (2 * y * (z + 1) * (2 * y * (z + 1)) > 2 * y * (z + 1) * (x + y * y))%Z;
 try omega.
apply Zmult_gt_compat_l; try assumption.
apply Zmult_gt_0_compat; try omega.
assert (z >= 0)%Z; try omega.
rewrite zVal.
apply Z_div_ge0; try omega.
assert (x / y >= 0)%Z; try omega.
apply Z_div_ge0; try omega.
assert ((x + y * y) * (x + y * y) - 4 * y * y * x >= 0)%Z; try omega.
replace ((x + y * y) * (x + y * y) - 4 * y * y * x)%Z with
 ((x - y * y) * (x - y * y))%Z; try ring.
apply sqr_pos.
apply (Zmult_gt_0_reg_l (4 * y * y)).
apply Zmult_gt_0_compat; try omega.
omega.
Qed.




Lemma iter_sqrt_invar4 :
 forall x y z:Z,
   (x > 0)%Z ->
   (y > 0)%Z -> z = ((x / y + y) / 2)%Z -> (z >= y)%Z -> (y * y <= x)%Z.
Proof.
intros x y z xPos yPos zVal zGey.
generalize (iter_sqrt_invar1 x y z xPos yPos zVal); intros.
assert (y * y <= y * z)%Z.
apply Zmult_le_compat_l; try omega.
assert ((2 * y * z)%Z = (y * z + y * z)%Z); try ring.
omega.
Qed.

(* beginning of proof obligations *)

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sqrt_po_1 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_2: x = 0),
  (0 * 0) <= x /\ x < ((0 + 1) * (0 + 1)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sqrt_po_2 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_3: x <> 0),
  forall (HW_4: x <= 3),
  (1 * 1) <= x /\ x < ((1 + 1) * (1 + 1)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sqrt_po_3 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_3: x <> 0),
  forall (HW_5: x > 3),
  2 <> 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sqrt_po_4 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_3: x <> 0),
  forall (HW_5: x > 3),
  forall (HW_6: 2 <> 0),
  forall (result: Z),
  forall (HW_7: result = ((Zdiv (x + 1) 2))),
  result > 0 /\ x > 0 /\ result = ((Zdiv ((Zdiv x x) + x) 2)) /\ x <
  ((x + 1) * (x + 1)) /\ x < ((result + 1) * (result + 1)).
Proof.
intuition.
subst result.
assert ((x + 1) / 2 >= 1)%Z.
pattern 1%Z at 2; replace 1%Z with (2 / 2)%Z; trivial.
apply Z_div_ge; try omega.
omega.

subst result.
assert ((x / x + x)%Z = (x + 1)%Z).
assert (xPos: (x > 0)); try omega.
generalize (Z_div_same x xPos).
 intro.
rewrite H; omega.
rewrite H; trivial.

subst result.
assert ((x + 1) * (x + 1) >= (x + 1) * 1)%Z.
apply Zmult_ge_compat_l; try omega.
assert (((x + 1) * 1)%Z = (x + 1)%Z); try ring.
omega.

subst result.
apply (iter_sqrt_invar3 x x); try omega.
assert ((x / x + x)%Z = (x + 1)%Z).
assert (xPos: (x > 0)); try omega.
generalize (Z_div_same x xPos).
 intro.
rewrite H; omega.
rewrite H; trivial.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sqrt_po_5 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_3: x <> 0),
  forall (HW_5: x > 3),
  forall (HW_6: 2 <> 0),
  forall (result: Z),
  forall (HW_7: result = ((Zdiv (x + 1) 2))),
  forall (HW_8: result > 0 /\ x > 0 /\ result =
                ((Zdiv ((Zdiv x x) + x) 2)) /\ x < ((x + 1) * (x + 1)) /\ x <
                ((result + 1) * (result + 1))),
  forall (y: Z),
  forall (z: Z),
  forall (HW_9: z > 0 /\ y > 0 /\ z = ((Zdiv ((Zdiv x y) + y) 2)) /\ x <
                ((y + 1) * (y + 1)) /\ x < ((z + 1) * (z + 1))),
  forall (HW_10: z < y),
  forall (y0: Z),
  forall (HW_11: y0 = z),
  z <> 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sqrt_po_6 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_3: x <> 0),
  forall (HW_5: x > 3),
  forall (HW_6: 2 <> 0),
  forall (result: Z),
  forall (HW_7: result = ((Zdiv (x + 1) 2))),
  forall (HW_8: result > 0 /\ x > 0 /\ result =
                ((Zdiv ((Zdiv x x) + x) 2)) /\ x < ((x + 1) * (x + 1)) /\ x <
                ((result + 1) * (result + 1))),
  forall (y: Z),
  forall (z: Z),
  forall (HW_9: z > 0 /\ y > 0 /\ z = ((Zdiv ((Zdiv x y) + y) 2)) /\ x <
                ((y + 1) * (y + 1)) /\ x < ((z + 1) * (z + 1))),
  forall (HW_10: z < y),
  forall (y0: Z),
  forall (HW_11: y0 = z),
  forall (HW_12: z <> 0),
  forall (result0: Z),
  forall (HW_13: result0 = ((Zdiv x z))),
  forall (HW_14: 2 <> 0),
  forall (result1: Z),
  forall (HW_15: result1 = ((Zdiv (result0 + z) 2))),
  forall (z0: Z),
  forall (HW_16: z0 = result1),
  (z0 > 0 /\ y0 > 0 /\ z0 = ((Zdiv ((Zdiv x y0) + y0) 2)) /\ x <
  ((y0 + 1) * (y0 + 1)) /\ x < ((z0 + 1) * (z0 + 1))) /\ (Zwf 0 y0 y).
Proof.
unfold Zwf; intuition.
subst.
apply iter_sqrt_pos; omega.
subst; auto.
subst; auto.
apply (iter_sqrt_invar3 x z); auto.
subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sqrt_po_7 : 
  forall (x: Z),
  forall (HW_1: x >= 0),
  forall (HW_3: x <> 0),
  forall (HW_5: x > 3),
  forall (HW_6: 2 <> 0),
  forall (result: Z),
  forall (HW_7: result = ((Zdiv (x + 1) 2))),
  forall (HW_8: result > 0 /\ x > 0 /\ result =
                ((Zdiv ((Zdiv x x) + x) 2)) /\ x < ((x + 1) * (x + 1)) /\ x <
                ((result + 1) * (result + 1))),
  forall (y: Z),
  forall (z: Z),
  forall (HW_9: z > 0 /\ y > 0 /\ z = ((Zdiv ((Zdiv x y) + y) 2)) /\ x <
                ((y + 1) * (y + 1)) /\ x < ((z + 1) * (z + 1))),
  forall (HW_17: z >= y),
  (y * y) <= x /\ x < ((y + 1) * (y + 1)).
Proof.
intuition.
apply (iter_sqrt_invar4 x y z); try omega.
Qed.

