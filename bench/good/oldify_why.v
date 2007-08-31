
Require Import Why.

(*Why logic*) Definition q1 : Z -> Z -> Z -> Prop.
Admitted.







(*Why logic*) Definition q : (array Z) -> (array Z) -> Z -> Prop.
Admitted.





(* Why obligation from file "", line 0, characters -1--1: *)
(*Why goal*) Lemma g_po_1 : 
  forall (t: (array Z)),
  forall (result: Z),
  forall (HW_1: result = (array_length t)),
  forall (t0: (array Z)),
  forall (HW_2: (q t0 t result)),
  (q t0 t (array_length t)).
Proof.
intuition.
subst; intuition.
Save.



