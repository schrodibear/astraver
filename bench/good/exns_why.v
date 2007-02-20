(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.















(* Why obligation from file "good/exns.mlw", line 44, characters 2-73: *)
(*Why goal*) Lemma p7_po_1 : 
  (* File "good/exns.mlw", line 44, characters 1-72 *)
  (forall (_:unit),
   (* File "good/exns.mlw", line 45, characters 9-15 *)
   (forall (x:Z),
    ((* File "good/exns.mlw", line 45, characters 9-15 *) x = 1 ->
     (* File "good/exns.mlw", line 45, characters 17-24 *) x = 1))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.



(* Why obligation from file "good/exns.mlw", line 47, characters 2-96: *)
(*Why goal*) Lemma p8_po_1 : 
  (* File "good/exns.mlw", line 47, characters 1-95 *)
  (forall (_:unit),
   (* File "good/exns.mlw", line 48, characters 9-15 *)
   (forall (x:Z),
    ((* File "good/exns.mlw", line 48, characters 9-15 *) x = 1 ->
     (* File "good/exns.mlw", line 48, characters 26-28 *) (x = 1 /\ x = 1)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.



(* Why obligation from file "good/exns.mlw", line 51, characters 2-97: *)
(*Why goal*) Lemma p9_po_1 : 
  (* File "good/exns.mlw", line 51, characters 1-96 *)
  (forall (_:unit),
   (* File "good/exns.mlw", line 52, characters 19-25 *)
   (forall (x:Z),
    ((* File "good/exns.mlw", line 52, characters 19-25 *) x = 1 ->
     (* File "good/exns.mlw", line 52, characters 27-29 *) (x = 1 /\ x = 1)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.









(* Why obligation from file "good/exns.mlw", line 69, characters 2-123: *)
(*Why goal*) Lemma p13_po_1 : 
  (* File "good/exns.mlw", line 69, characters 1-122 *)
  (forall (_:unit),
   (* File "good/exns.mlw", line 72, characters 13-19 *)
   (forall (x:Z),
    ((* File "good/exns.mlw", line 72, characters 13-19 *) x = 2 -> x = 2))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.



(* Why obligation from file "good/exns.mlw", line 82, characters 6-12: *)
(*Why goal*) Lemma p13a_po_1 : 
  forall (x: Z),
  forall (HW_1: (* File "good/exns.mlw", line 79, characters 9-15 *) x = 1),
  (* File "good/exns.mlw", line 82, characters 5-11 *)
  (forall (x:Z),
   ((* File "good/exns.mlw", line 82, characters 5-11 *) x = 0 -> x <> 1)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.



(* Why obligation from file "good/exns.mlw", line 95, characters 6-20: *)
(*Why goal*) Lemma p14_po_1 : 
  forall (x: Z),
  forall (HW_2: (* File "good/exns.mlw", line 92, characters 8-14 *) x <> 1),
  forall (HW_4: (* File "good/exns.mlw", line 93, characters 8-14 *) x <> 2),
  forall (HW_6: (* File "good/exns.mlw", line 94, characters 8-14 *) x <> 3),
  (* File "good/exns.mlw", line 95, characters 5-19 *) (x <> 1 /\ x <> 2 /\
  x <> 3).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.



