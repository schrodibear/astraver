
Require Import Why.

(*Why*) Parameter N : Z.

(* Why obligation from file "good/return.mlw", characters 285-294 *)
Lemma p_po_1 : 
  forall (t: (array Z)),
  forall (Pre5: (array_length t) = N),
  forall (i0: Z),
  forall (Post2: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre4: Variant1 = (N - i1)),
  forall (Pre3: 0 <= i1),
  forall (Test4: i1 < N),
  0 <= i1 /\ i1 < (array_length t).
Proof.
intuition.
Qed.

(* Why obligation from file "good/return.mlw", characters 300-317 *)
Lemma p_po_2 : 
  forall (t: (array Z)),
  forall (Pre5: (array_length t) = N),
  forall (i0: Z),
  forall (Post2: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre4: Variant1 = (N - i1)),
  forall (Pre3: 0 <= i1),
  forall (Test4: i1 < N),
  forall (Pre2: 0 <= i1 /\ i1 < (array_length t)),
  forall (Test3: (access t i1) = 0),
  forall (result2: Z),
  forall (Post5: result2 = i1),
  (forall (result:Z),
   (result = result2 -> (0 <= result /\ result < N -> (access t result) = 0))).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "good/return.mlw", characters 317-317 *)
Lemma p_po_3 : 
  forall (t: (array Z)),
  forall (Pre5: (array_length t) = N),
  forall (i0: Z),
  forall (Post2: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre4: Variant1 = (N - i1)),
  forall (Pre3: 0 <= i1),
  forall (Test4: i1 < N),
  forall (Pre2: 0 <= i1 /\ i1 < (array_length t)),
  forall (Test2: (access t i1) <> 0),
  forall (result2: unit),
  forall (Post4: result2 = tt),
  (forall (i:Z), (i = (i1 + 1) -> 0 <= i /\ (Zwf 0 (N - i) (N - i1)))).
Proof.
intuition.
Save.

(* Why obligation from file "good/return.mlw", characters 155-345 *)
Lemma p_po_4 : 
  forall (t: (array Z)),
  forall (Pre5: (array_length t) = N),
  forall (i0: Z),
  forall (Post2: i0 = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre4: Variant1 = (N - i1)),
  forall (Pre3: 0 <= i1),
  forall (Test1: i1 >= N),
  (forall (result:Z),
   (result = N -> (0 <= result /\ result < N -> (access t result) = 0))).
Proof.
intuition.
Save.

(* Why obligation from file "good/return.mlw", characters 189-195 *)
Lemma p_po_5 : 
  forall (t: (array Z)),
  forall (Pre5: (array_length t) = N),
  forall (i0: Z),
  forall (Post2: i0 = 0),
  0 <= i0.
Proof.
intuition.
Save.

