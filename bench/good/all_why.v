
Require Import Why.
Require Import Omega.

Parameter foo : Set.

(*Why*) Parameter v2 : Z.

(*Why*) Parameter v3 : Z.

(*Why*) Parameter v5 : foo.

(*Why*) Parameter f1 : forall (_: Z), forall (_: bool), Z.

(*Why*) Parameter f2 : forall (_: Z), bool.

(*Why*) Parameter f3 :
  forall (x: Z), forall (y: Z), forall (_: x >= 0),
  (sig_2 Z Z (fun (y0: Z) (result: Z)  => (y0 = (y + x + result)))).

(*Why*) Parameter f4 : forall (_: unit), unit.

(*Why*) Parameter f5 : forall (_: foo), foo.

(*Why*) Parameter f6 : forall (x: foo), foo.

(*Why*) Parameter f7 : forall (x: foo), foo.

(*Why*) Parameter f8 :
  forall (t: (array Z)),
  (sig_1 unit (fun (result: unit)  => ((access t 1) = 2))).

(* Why obligation from file "good/all.mlw", characters 709-727 *)
Lemma p2_po_1 : 
  ~False.
Proof.
tauto.
Qed.





(* Why obligation from file "good/all.mlw", characters 737-759 *)
Lemma p3_po_1 : 
  True /\ True.
Proof.
tauto.
Qed.





(* Why obligation from file "good/all.mlw", characters 769-791 *)
Lemma p4_po_1 : 
  True \/ False.
Proof.
tauto.
Qed.





(* Why obligation from file "good/all.mlw", characters 801-828 *)
Lemma p5_po_1 : 
  False \/ ~False.
auto.
Qed.





(* Why obligation from file "good/all.mlw", characters 838-864 *)
Lemma p6_po_1 : 
  (True -> ~False).
Proof.
auto.
Qed.





(* Why obligation from file "good/all.mlw", characters 874-900 *)
Lemma p7_po_1 : 
  (forall (x:Z), x = x).
Proof.
auto.
Qed.





(* Why obligation from file "good/all.mlw", characters 910-945 *)
Lemma p8_po_1 : 
  True /\ (forall (x:Z), x = x).
Proof.
auto.
Qed.


(* Why obligation from file "good/all.mlw", characters 955-1002 *)
Lemma p9_po_1 : 
  (forall (x:Z), (forall (y:Z), (x = y -> x = y))).
Proof.
trivial.
Qed.

(* Why obligation from file "good/all.mlw", characters 1198-1201 *)
Lemma ar6_po_1 : 
  ~(1 = 0).
Proof.
omega.
Qed.





(* Why obligation from file "good/all.mlw", characters 1212-1215 *)
Lemma ar7_po_1 : 
  ~(1 = 0).
Proof.
omega.
Qed.

















































































































(* Why obligation from file "good/all.mlw", characters 2156-2190 *)
Lemma arr1_po_1 : 
  forall (v6: (array Z)),
  forall (Pre2: (array_length v6) >= 1),
  0 <= 0 /\ 0 < (array_length v6).
intros; omega.
Qed.





(* Why obligation from file "good/all.mlw", characters 2203-2239 *)
Lemma arr2_po_1 : 
  forall (v6: (array Z)),
  forall (Pre2: (array_length v6) >= 4),
  0 <= (1 + 2) /\ (1 + 2) < (array_length v6).
intros; omega.
Qed.





(* Why obligation from file "good/all.mlw", characters 2251-2298 *)
Lemma arr3_po_1 : 
  forall (v4: Z),
  forall (v6: (array Z)),
  forall (Pre2: (array_length v6) >= 1 /\ v4 = 0),
  0 <= v4 /\ v4 < (array_length v6).
intros; omega.
Qed.





(* Why obligation from file "good/all.mlw", characters 2354-2359 *)
Lemma arr4_po_1 : 
  forall (v6: (array Z)),
  forall (Pre3: (array_length v6) >= 10 /\ (access v6 0) = 9),
  0 <= 0 /\ 0 < (array_length v6).
intros; omega.
Qed.

(* Why obligation from file "good/all.mlw", characters 2310-2363 *)
Lemma arr4_po_2 : 
  forall (v6: (array Z)),
  forall (Pre3: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (Pre2: 0 <= 0 /\ 0 < (array_length v6)),
  0 <= (access v6 0) /\ (access v6 0) < (array_length v6).
intros; omega.
Qed.





(* Why obligation from file "good/all.mlw", characters 2376-2415 *)
Lemma arr5_po_1 : 
  forall (v6: (array Z)),
  forall (Pre2: (array_length v6) >= 1),
  0 <= 0 /\ 0 < (array_length v6).
intros; simpl; omega.
Qed.


(* Why obligation from file "good/all.mlw", characters 2427-2470 *)
Lemma arr6_po_1 : 
  forall (v6: (array Z)),
  forall (Pre2: (array_length v6) >= 4),
  0 <= (1 + 2) /\ (1 + 2) < (array_length v6).
intros; simpl; omega.
Qed.



(* Why obligation from file "good/all.mlw", characters 2482-2540 *)
Lemma arr7_po_1 : 
  forall (v6: (array Z)),
  forall (Pre3: (array_length v6) >= 10 /\ (access v6 0) = 9),
  0 <= (access v6 0) /\ (access v6 0) < (array_length v6).
intros; omega.
Qed.

(* Why obligation from file "good/all.mlw", characters 2526-2531 *)
Lemma arr7_po_2 : 
  forall (v6: (array Z)),
  forall (Pre3: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (Pre2: 0 <= (access v6 0) /\ (access v6 0) < (array_length v6)),
  0 <= 0 /\ 0 < (array_length v6).
intros; simpl; omega.
Qed.





(* Why obligation from file "good/all.mlw", characters 2645-2653 *)
Lemma fc3_po_1 : 
  forall (a: Z),
  forall (Post2: a = 0),
  forall (b: Z),
  forall (Post1: b = 0),
  a >= 0.
 intros; omega. Qed.









(* Why obligation from file "good/all.mlw", characters 2796-2844 *)
Lemma an2_po_1 : 
  forall (v4: Z),
  forall (Pre1: v4 >= 0),
  forall (v4_0: Z),
  forall (Post1: v4_0 = (v4 + 1)),
  v4_0 > v4.
Proof.
intros; omega.
Qed.


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



(*Why*) Parameter f1_ex : forall (n: Z), (EM unit unit).

(*Why*) Parameter f2_ex : forall (x: Z), (tuple_2 Z (EM unit (EM Z bool))).
