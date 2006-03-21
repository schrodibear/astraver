
Require Import Why.


(*Why logic*) Definition N : Z.
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  0 <= i.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_2 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (HW_3: 0 <= i),
  forall (i0: Z),
  forall (HW_4: 0 <= i0),
  forall (HW_5: i0 < N),
  0 <= i0 /\ i0 < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_3 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (HW_3: 0 <= i),
  forall (i0: Z),
  forall (HW_4: 0 <= i0),
  forall (HW_5: i0 < N),
  forall (HW_6: 0 <= i0 /\ i0 < (array_length t)),
  forall (result: Z),
  forall (HW_7: result = (access t i0)),
  forall (HW_8: result = 0),
  forall (HW_9: 0 <= i0 /\ i0 < N),
  (access t i0) = 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_4 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (HW_3: 0 <= i),
  forall (i0: Z),
  forall (HW_4: 0 <= i0),
  forall (HW_5: i0 < N),
  forall (HW_6: 0 <= i0 /\ i0 < (array_length t)),
  forall (result: Z),
  forall (HW_7: result = (access t i0)),
  forall (HW_10: result <> 0),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  0 <= i1 /\ (Zwf 0 (N - i1) (N - i0)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_5 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (HW_3: 0 <= i),
  forall (i0: Z),
  forall (HW_4: 0 <= i0),
  forall (HW_12: i0 >= N),
  forall (HW_13: 0 <= N /\ N < N),
  (access t N) = 0.
Proof.
intuition.
Save.

