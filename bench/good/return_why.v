(* Load Programs. *)
Require Import Why.

(*Why*) Parameter N : Z.

(* Why obligation from file "good/return.mlw", characters 285-290 *)
Lemma p_po_1 : 
  forall (t: (array Z)),
  forall (Pre9: (array_length t) = N),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = (N - i1)),
  forall (Pre7: 0 <= i1),
  forall (Test4: i1 < N),
  0 <= i1 /\ i1 < (array_length t).
Proof.
intuition.
Qed.

(* Why obligation from file "good/return.mlw", characters 314-316 *)
Lemma p_po_2 : 
  forall (t: (array Z)),
  forall (Pre9: (array_length t) = N),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = (N - i1)),
  forall (Pre7: 0 <= i1),
  forall (Test4: i1 < N),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t)),
  forall (Test3: (access t i1) = 0),
  (0 <= i1 /\ i1 < N -> (access t i1) = 0).
Proof.
intuition.
Qed.

(* Why obligation from file "good/return.mlw", characters 317-317 *)
Lemma p_po_3 : 
  forall (t: (array Z)),
  forall (Pre9: (array_length t) = N),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = (N - i1)),
  forall (Pre7: 0 <= i1),
  forall (Test4: i1 < N),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t)),
  forall (Test2: (access t i1) <> 0),
  (forall (i:Z), (i = (i1 + 1) -> 0 <= i /\ (Zwf 0 (N - i) (N - i1)))).
Proof.
intuition.
Qed.

(* Why obligation from file "good/return.mlw", characters 189-195 *)
Lemma p_po_4 : 
  forall (t: (array Z)),
  forall (Pre9: (array_length t) = N),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  0 <= i0.
Proof.
intuition.
Qed.

(* Why obligation from file "good/return.mlw", characters 351-352 *)
Lemma p_po_5 : 
  forall (t: (array Z)),
  forall (Pre9: (array_length t) = N),
  forall (i0: Z),
  forall (Post1: i0 = 0),
  forall (i1: Z),
  forall (Post3: 0 <= i1 /\ i1 >= N),
  (0 <= N /\ N < N -> (access t N) = 0).
Proof.
auto with *.
Qed.

