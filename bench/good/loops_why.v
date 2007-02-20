
Require Import Why.
Require Import Omega.

(* Why obligation from file "good/loops.mlw", line 10, characters 6-17: *)
(*Why goal*) Lemma loop1_po_1 : 
  forall (i: Z),
  forall (HW_1: i <= 10),
  forall (i0: Z),
  forall (HW_2: i0 <= 10),
  forall (HW_3: (* File "good/loops.mlw", line 8, characters 9-16 *) i0 < 10),
  forall (i1: Z),
  forall (HW_4: (* File "good/loops.mlw", line 10, characters 5-16 *)
                i1 = (i0 + 1)),
  (* File "good/loops.mlw", line 10, characters 5-16 *) (i1 <= 10 /\
  (Zwf 0 (10 - i1) (10 - i0))).
Proof.
intuition.
Save.

(* Why obligation from file "good/loops.mlw", line 8, characters 4-82: *)
(*Why goal*) Lemma loop1_po_2 : 
  forall (i: Z),
  forall (HW_1: i <= 10),
  forall (i0: Z),
  forall (HW_2: i0 <= 10),
  forall (HW_5: (* File "good/loops.mlw", line 8, characters 9-16 *) i0 >= 10),
  (* File "good/loops.mlw", line 8, characters 3-81 *) i0 = 10.
Proof.
intuition.
Save.



(* Why obligation from file "good/loops.mlw", line 19, characters 2-45: *)
(*Why goal*) Lemma oppose_po_1 : 
  (* File "good/loops.mlw", line 19, characters 1-44 *)
  (forall (u:unit),
   (forall (x:Z),
    (* File "good/loops.mlw", line 19, characters 23-32 *)
    (forall (x0:Z),
     ((* File "good/loops.mlw", line 19, characters 23-32 *) x0 = (Zopp x) ->
      x0 = (Zopp x))))).
Proof.
intuition.
Save.



(* Why obligation from file "good/loops.mlw", line 24, characters 58-69: *)
(*Why goal*) Lemma loop2_po_1 : 
  forall (x: Z),
  forall (HW_1: x <= 10),
  forall (x0: Z),
  forall (HW_2: x0 <= 10),
  forall (HW_3: (* File "good/loops.mlw", line 24, characters 11-18 *) x0 <
                10),
  forall (x1: Z),
  forall (HW_4: (* File "good/loops.mlw", line 24, characters 57-68 *)
                x1 = (x0 + 1)),
  (* File "good/loops.mlw", line 24, characters 57-68 *) (x1 <= 10 /\
  (Zwf 0 (10 - x1) (10 - x0))).
Proof.
intuition.
Save.

(* Why obligation from file "good/loops.mlw", line 24, characters 6-74: *)
(*Why goal*) Lemma loop2_po_2 : 
  forall (x: Z),
  forall (HW_1: x <= 10),
  forall (x0: Z),
  forall (HW_2: x0 <= 10),
  forall (HW_5: (* File "good/loops.mlw", line 24, characters 11-18 *) x0 >=
                10),
  (* File "good/loops.mlw", line 24, characters 5-73 *) x0 = 10.
Proof.
intuition.
Save.

(* Why obligation from file "good/loops.mlw", line 26, characters 22-33: *)
(*Why goal*) Lemma loop2_po_3 : 
  forall (x: Z),
  forall (HW_1: x <= 10),
  forall (x0: Z),
  forall (HW_2: x0 <= 10),
  forall (HW_5: (* File "good/loops.mlw", line 24, characters 11-18 *) x0 >=
                10),
  forall (HW_6: (* File "good/loops.mlw", line 26, characters 8-14 *) x0 > 0),
  forall (x1: Z),
  forall (HW_7: (* File "good/loops.mlw", line 26, characters 21-32 *) x1 =
                (Zopp x0)),
  (* File "good/loops.mlw", line 26, characters 21-32 *) x1 = (Zopp 10).
Proof.
intuition.
Save.

(* Why obligation from file "good/loops.mlw", line 26, characters 6-34: *)
(*Why goal*) Lemma loop2_po_4 : 
  forall (x: Z),
  forall (HW_1: x <= 10),
  forall (x0: Z),
  forall (HW_2: x0 <= 10),
  forall (HW_5: (* File "good/loops.mlw", line 24, characters 11-18 *) x0 >=
                10),
  forall (HW_8: (* File "good/loops.mlw", line 26, characters 8-14 *) x0 <= 0),
  (* File "good/loops.mlw", line 26, characters 5-33 *) x0 = (Zopp 10).
Proof.
intuition.
Save.



