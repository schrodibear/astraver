(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.




(*Why axiom*) Lemma dist1 :
  (forall (x:Z),
   (forall (y:Z), (forall (z:Z), (x * (y + z)) = (x * y + x * z)))).
Admitted.

(*Why axiom*) Lemma dist2 :
  (forall (x:Z),
   (forall (y:Z), (forall (z:Z), ((x + y) * z) = (x * z + y * z)))).
Admitted.

(* Why obligation from file "arith.why", characters 460-483 *)
Lemma test_po_1 : 
  forall (k: Z),
  forall (j: Z),
  forall (l: Z),
  forall (Post5: l = 1),
  forall (m: Z),
  forall (Post4: m = 12),
  forall (caduceus4: Z),
  forall (Post1: caduceus4 = j),
  (forall (l0:Z),
   (l0 = (l * j) ->
    (forall (result:Z),
     (result = l0 -> (caduceus4 + k) = (j + k) /\
      (j + (result + 10 * k + (caduceus4 + k) + m)) = (3 * j + 11 * k + 12))))).
Proof.
intuition.
subst; omega.
Save.

