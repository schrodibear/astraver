
Require Import Why.
Require Import Omega.

(*Why*) Parameter v2 : Z.

(*Why*) Parameter v3 : Z.

































(*Why type*) Parameter foo: Set.

(*Why*) Parameter v5 : foo.

(*Why*) Parameter f1 : forall (_: Z), forall (_: bool), Z.







(*Why*) Parameter f4 : forall (_: unit), unit.

(*Why*) Parameter f5 : forall (_: foo), foo.

(*Why*) Parameter f6 : forall (x: foo), foo.

(*Why*) Parameter f7 : forall (x: foo), foo.





(*Why*) Inductive ET_E1 (T:Set) : Set :=
          | Val_E1 : T -> ET_E1 T
          | Exn_E1 : ET_E1 T.

(*Why*) Definition post_E1 (T:Set) (P:Prop) (Q:T -> Prop)
          (x:ET_E1 T) :=
          match x with
          | Val_E1 v => Q v
          | Exn_E1 => P
          end.

(*Why*) Implicit Arguments post_E1.

(*Why*) Inductive ET_E2 (T:Set) : Set :=
          | Val_E2 : T -> ET_E2 T
          | Exn_E2 : Z -> ET_E2 T.

(*Why*) Definition post_E2 (T:Set) (P:Z -> Prop) (Q:T -> Prop)
          (x:ET_E2 T) :=
          match x with
          | Val_E2 v => Q v
          | Exn_E2 v => P v
          end.

(*Why*) Implicit Arguments post_E2.

(*Why*) Inductive ET_E3 (T:Set) : Set :=
          | Val_E3 : T -> ET_E3 T
          | Exn_E3 : foo -> ET_E3 T.

(*Why*) Definition post_E3 (T:Set) (P:foo -> Prop) (Q:T -> Prop)
          (x:ET_E3 T) :=
          match x with
          | Val_E3 v => Q v
          | Exn_E3 v => P v
          end.

(*Why*) Implicit Arguments post_E3.







(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p2_po_1 : 
  ~False.
Proof.
tauto.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p3_po_1 : 
  True /\ True.
Proof.
tauto.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p4_po_1 : 
  True \/ False.
Proof.
tauto.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p5_po_1 : 
  False \/ ~False.
Proof.
tauto.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p6_po_1 : 
  (True -> ~False).
Proof.
tauto.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p7_po_1 : 
  (forall (x:Z), x = x).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p8_po_1 : 
  True /\ (forall (x:Z), x = x).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma p9_po_1 : 
  (forall (x:Z), (forall (y:Z), (x = y -> x = y))).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma ar6_po_1 : 
  1 <> 0.
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr1_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr2_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 4),
  0 <= (1 + 2) /\ (1 + 2) < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr3_po_1 : 
  forall (v4: Z),
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1 /\ v4 = 0),
  0 <= v4 /\ v4 < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr4_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (result: Z),
  forall (HW_2: result = (access v6 0)),
  0 <= result /\ result < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr4_po_2 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr5_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr6_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 4),
  0 <= (1 + 2) /\ (1 + 2) < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr7_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (result: Z),
  forall (HW_2: result = (access v6 0)),
  0 <= result /\ result < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma arr7_po_2 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma fc3_po_1 : 
  0 >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "good/all.mlw", line 0, characters 0-0: *)
(*Why goal*) Lemma an2_po_1 : 
  forall (v4: Z),
  forall (HW_1: v4 >= 0),
  forall (v4_0: Z),
  forall (HW_2: v4_0 = (v4 + 1)),
  v4_0 > v4.
Proof.
intuition.
Save.



