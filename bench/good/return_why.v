
Require Import Why.

(*Why*) Parameter N : Z.

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
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: i0 < N),
  forall (result: Z),
  forall (HW_5: result = (access t i0)),
  forall (HW_6: result = 0),
  (0 <= i0 /\ i0 < N -> (access t i0) = 0).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_3 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: i0 < N),
  forall (result: Z),
  forall (HW_5: result = (access t i0)),
  forall (HW_7: result <> 0),
  forall (i1: Z),
  forall (HW_8: i1 = (i0 + 1)),
  0 <= i1 /\ (Zwf 0 (N - i1) (N - i0)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_4 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: i0 < N),
  0 <= i0 /\ i0 < (array_length t).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p_po_5 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_9: i0 >= N),
  (0 <= N /\ N < N -> (access t N) = 0).
Proof.
intuition.
Save.

