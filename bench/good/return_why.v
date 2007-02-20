
Require Import Why.


(*Why logic*) Definition N : Z.
Admitted.

(* Why obligation from file "good/return.mlw", line 13, characters 6-196: *)
(*Why goal*) Lemma p_po_1 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: (* File "good/return.mlw", line 12, characters 5-11 *) i = 0),
  (* File "good/return.mlw", line 13, characters 5-195 *) 0 <= i.
Proof.
intuition.
Save.

(* Why obligation from file "good/return.mlw", line 16, characters 11-16: *)
(*Why goal*) Lemma p_po_2 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: (* File "good/return.mlw", line 12, characters 5-11 *) i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: (* File "good/return.mlw", line 13, characters 11-17 *) i0 <
                N),
  (* File "good/return.mlw", line 16, characters 10-15 *) (0 <= i0 /\ i0 <
  (array_length t)).
Proof.
intuition.
Save.

(* Why obligation from file "good/return.mlw", line 21, characters 6-7: *)
(*Why goal*) Lemma p_po_3 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: (* File "good/return.mlw", line 12, characters 5-11 *) i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: (* File "good/return.mlw", line 13, characters 11-17 *) i0 <
                N),
  forall (HW_5: (* File "good/return.mlw", line 16, characters 10-15 *) (0 <=
                i0 /\ i0 < (array_length t))),
  forall (result: Z),
  forall (HW_6: (* File "good/return.mlw", line 16, characters 10-15 *)
                result = (access t i0)),
  forall (HW_7: (* File "good/return.mlw", line 16, characters 10-19 *)
                result = 0),
  forall (HW_8: 0 <= i0 /\ i0 < N),
  (* File "good/return.mlw", line 21, characters 5-6 *) (access t i0) = 0.
Proof.
intuition.
Save.

(* Why obligation from file "good/return.mlw", line 17, characters 8-19: *)
(*Why goal*) Lemma p_po_4 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: (* File "good/return.mlw", line 12, characters 5-11 *) i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_4: (* File "good/return.mlw", line 13, characters 11-17 *) i0 <
                N),
  forall (HW_5: (* File "good/return.mlw", line 16, characters 10-15 *) (0 <=
                i0 /\ i0 < (array_length t))),
  forall (result: Z),
  forall (HW_6: (* File "good/return.mlw", line 16, characters 10-15 *)
                result = (access t i0)),
  forall (HW_9: (* File "good/return.mlw", line 16, characters 10-19 *)
                result <> 0),
  forall (i1: Z),
  forall (HW_10: (* File "good/return.mlw", line 17, characters 7-18 *)
                 i1 = (i0 + 1)),
  (* File "good/return.mlw", line 17, characters 7-18 *) (0 <= i1 /\
  (Zwf 0 (N - i1) (N - i0))).
Proof.
intuition.
Save.

(* Why obligation from file "good/return.mlw", line 19, characters 6-7: *)
(*Why goal*) Lemma p_po_5 : 
  forall (t: (array Z)),
  forall (HW_1: (array_length t) = N),
  forall (i: Z),
  forall (HW_2: (* File "good/return.mlw", line 12, characters 5-11 *) i = 0),
  forall (i0: Z),
  forall (HW_3: 0 <= i0),
  forall (HW_11: (* File "good/return.mlw", line 13, characters 11-17 *)
                 i0 >= N),
  forall (HW_12: 0 <= N /\ N < N),
  (* File "good/return.mlw", line 19, characters 5-6 *) (access t N) = 0.
Proof.
intuition.
Save.

