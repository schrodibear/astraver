(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)
Require Export jessie_why.

Require Export WhyFloats.

(* Why obligation from file "/users/demons/ayad/why/bench/jc/good/sterbenz.jc", line 5, characters 11-35: *)
(*Why goal*) Lemma test1_ensures_default_po_1 : 
  forall (HW_1: (* JC_4 *) True),
  forall (why__return: double),
  forall (HW_3: why__return = (r_to_d nearest_even (Rmult (2)%R (35 / 10)%R))),
  (* JC_5 *) (eq (d_to_r why__return) (7)%R).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

