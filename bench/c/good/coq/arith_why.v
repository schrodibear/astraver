(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.




Admitted.

Admitted.

Admitted.

Admitted.

Proof.
intuition.
subst; omega.
Save.

(* Why obligation from file "why/arith.why", characters 138-162 *)
Lemma test_impl_po_1 : 
  forall (k: Z),
  forall (j: Z),
  forall (l: Z),
  forall (Post5: l = 1),
  forall (m: Z),
  forall (Post4: m = 12),
  forall (caduceus_4: Z),
  forall (Post1: caduceus_4 = j),
  (forall (l0:Z),
   (l0 = (l * j) ->
    (forall (result:Z),
     (result = l0 -> (caduceus_4 + k) = (j + k) /\
      (j + (result + 10 * k + (caduceus_4 + k) + m)) = (3 * j + 11 * k + 12))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

