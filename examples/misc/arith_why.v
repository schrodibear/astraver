(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Omega.
Require Import Zdiv.
Require Import ZArithRing.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  x >= 0 /\ (0 + x * y) = (x * y).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (HW_2: x >= 0 /\ (0 + x * y) = (x * y)),
  forall (a: Z),
  forall (b: Z),
  forall (p: Z),
  forall (HW_3: a >= 0 /\ (p + a * b) = (x * y)),
  forall (HW_4: a <> 0),
  forall (HW_5: ((Zmod a 2)) = 1),
  forall (p0: Z),
  forall (HW_6: p0 = (p + b)),
  2 <> 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult_po_3 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (HW_2: x >= 0 /\ (0 + x * y) = (x * y)),
  forall (a: Z),
  forall (b: Z),
  forall (p: Z),
  forall (HW_3: a >= 0 /\ (p + a * b) = (x * y)),
  forall (HW_4: a <> 0),
  forall (HW_5: ((Zmod a 2)) = 1),
  forall (p0: Z),
  forall (HW_6: p0 = (p + b)),
  forall (HW_7: 2 <> 0),
  forall (result: Z),
  forall (HW_8: result = ((Zdiv a 2))),
  forall (a0: Z),
  forall (HW_9: a0 = result),
  forall (b0: Z),
  forall (HW_10: b0 = (2 * b)),
  (a0 >= 0 /\ (p0 + a0 * b0) = (x * y)) /\ (Zwf 0 a0 a).
Proof.
intuition.
subst; apply Z_div_ge0; omega.
assert (h: p + a * b = x * y). assumption.
rewrite (Z_div_mod_eq a 2) in h.
rewrite <- h.
subst.
replace (a mod 2) with 1. 
ring.
omega.
unfold Zwf.
 repeat split; try omega.
subst; apply Z_div_lt; try omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult_po_4 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (HW_2: x >= 0 /\ (0 + x * y) = (x * y)),
  forall (a: Z),
  forall (b: Z),
  forall (p: Z),
  forall (HW_3: a >= 0 /\ (p + a * b) = (x * y)),
  forall (HW_4: a <> 0),
  forall (HW_11: ((Zmod a 2)) <> 1),
  2 <> 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult_po_5 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (HW_2: x >= 0 /\ (0 + x * y) = (x * y)),
  forall (a: Z),
  forall (b: Z),
  forall (p: Z),
  forall (HW_3: a >= 0 /\ (p + a * b) = (x * y)),
  forall (HW_4: a <> 0),
  forall (HW_11: ((Zmod a 2)) <> 1),
  forall (HW_12: 2 <> 0),
  forall (result: Z),
  forall (HW_13: result = ((Zdiv a 2))),
  forall (a0: Z),
  forall (HW_14: a0 = result),
  forall (b0: Z),
  forall (HW_15: b0 = (2 * b)),
  (a0 >= 0 /\ (p + a0 * b0) = (x * y)) /\ (Zwf 0 a0 a).
Proof.
intuition.
subst; apply Z_div_ge0; try omega.
assert (h: p + a * b = x * y). assumption.
rewrite (Z_div_mod_eq a 2) in h.
rewrite <- h.
subst.
replace (a mod 2)%Z with 0%Z.
ring.
cut (2 > 0)%Z; [ intro h' | omega ].
generalize (Z_mod_lt a 2 h').
cut ((a mod 2)%Z <> 1%Z); intros; try omega.
omega.
unfold Zwf.
repeat split; try omega.
subst; apply Z_div_lt; try omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma mult_po_6 : 
  forall (x: Z),
  forall (y: Z),
  forall (HW_1: x >= 0 /\ y >= 0),
  forall (HW_2: x >= 0 /\ (0 + x * y) = (x * y)),
  forall (a: Z),
  forall (b: Z),
  forall (p: Z),
  forall (HW_3: a >= 0 /\ (p + a * b) = (x * y)),
  forall (HW_16: a = 0),
  p = (x * y).
Proof.
intuition; subst.
transitivity (p + 0*b); auto.
ring.
Save.

(*Why*) Parameter mult_valid :
  forall (x: Z), forall (y: Z), forall (_: x >= 0 /\ y >= 0),
  (sig_1 Z (fun (result: Z)  => (result = (x * y)))).

