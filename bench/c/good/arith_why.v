(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.




(* Why obligation from file "arith.why", characters 177-303 *)
Lemma test_po_1 : 
  forall (k: Z),
  forall (j: Z),
  forall (l: Z),
  forall (Post5: l = 1),
  forall (m: Z),
  forall (Post4: m = 12),
  forall (i0: Z),
  forall (Post1: i0 = (j + k)),
  forall (l1: Z),
  forall (Post2: l1 = (l * j)),
  forall (j0: Z),
  forall (Post3: j0 = (j + l1 + 10 * k + i0 + m)),
  i0 = (j + k) /\ j0 = (3 * j + 11 * k + 12).
Proof.
intuition.
subst; omega.
Save.

