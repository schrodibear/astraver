(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Caduceus.

(*Why axiom*) Lemma dist1 :
  (forall (x:Z),
   (forall (y:Z), (forall (z:Z), (x * (y + z)) = (x * y + x * z)))).
Admitted.

(*Why axiom*) Lemma dist2 :
  (forall (x:Z),
   (forall (y:Z), (forall (z:Z), ((x + y) * z) = (x * z + y * z)))).
Admitted.

(*Why axiom*) Lemma id1 : (forall (x:Z), (x * 1) = x).
Admitted.

(*Why axiom*) Lemma id2 : (forall (x:Z), (1 * x) = x).
Admitted.

