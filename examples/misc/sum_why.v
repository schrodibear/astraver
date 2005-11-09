(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sum_po_1 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  (2 * 0) = (0 * (0 + 1)) /\ 0 <= n.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sum_po_2 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_2: (2 * 0) = (0 * (0 + 1)) /\ 0 <= n),
  forall (i: Z),
  forall (s: Z),
  forall (HW_3: (2 * s) = (i * (i + 1)) /\ i <= n),
  forall (HW_4: i < n),
  forall (i0: Z),
  forall (HW_5: i0 = (i + 1)),
  forall (s0: Z),
  forall (HW_6: s0 = (s + i0)),
  ((2 * s0) = (i0 * (i0 + 1)) /\ i0 <= n) /\ (Zwf 0 (n - i0) (n - i)).
Proof.
intuition.
subst.
ring.
assert (h: 2 * s = i * (i + 1)). assumption.
rewrite h; ring.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma sum_po_3 : 
  forall (n: Z),
  forall (HW_1: n >= 0),
  forall (HW_2: (2 * 0) = (0 * (0 + 1)) /\ 0 <= n),
  forall (i: Z),
  forall (s: Z),
  forall (HW_3: (2 * s) = (i * (i + 1)) /\ i <= n),
  forall (HW_7: i >= n),
  (2 * s) = (n * (n + 1)).
Proof.
intuition.
assert (i=n). omega. subst; auto with arith.
Save.

