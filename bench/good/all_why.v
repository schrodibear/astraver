
Require Import Why.
Require Import Omega.





(*Why*) Parameter v2 : Z.

(*Why*) Parameter v3 : Z.

(*Why type*) Definition foo: Set.
Admitted.

















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

(*Why*) Parameter p1_valid : (sig_1 Z (fun (result: Z)  => (True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p2_po_1 : 
  ~False.
Proof.
tauto.
Save.


(*Why*) Parameter p2_valid : (sig_1 Z (fun (result: Z)  => (~False))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p3_po_1 : 
  True /\ True.
Proof.
tauto.
Save.


(*Why*) Parameter p3_valid : (sig_1 Z (fun (result: Z)  => (True /\ True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p4_po_1 : 
  True \/ False.
Proof.
tauto.
Save.


(*Why*) Parameter p4_valid : (sig_1 Z (fun (result: Z)  => (True \/ False))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p5_po_1 : 
  False \/ ~False.
Proof.
tauto.
Save.


(*Why*) Parameter p5_valid :
  (sig_1 Z (fun (result: Z)  => (False \/ ~False))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p6_po_1 : 
  (True -> ~False).
Proof.
tauto.
Save.



(*Why*) Parameter p6_valid :
  (sig_1 Z (fun (result: Z)  => ((True -> ~False)))).

(*Why*) Parameter p7_valid :
  (sig_1 Z (fun (result: Z)  => ((forall (x:Z), x = x)))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma p8_po_1 : 
  True /\ (forall (x:Z), x = x).
Proof.
intuition.
Save.














(*Why*) Parameter p8_valid :
  (sig_1 Z (fun (result: Z)  => (True /\ (forall (x:Z), x = x)))).

(*Why*) Parameter p9_valid :
  (sig_1 Z
   (fun (result: Z)  => ((forall (x:Z), (forall (y:Z), (x = y -> x = y)))))).

(*Why*) Parameter acc1_valid : Z.

(*Why*) Parameter acc2_valid : Z.

(*Why*) Parameter acc3_valid :
  forall (t: (array Z)),
  (sig_1 unit (fun (result: unit)  => ((access t 1) = 2))).

(*Why*) Parameter d1_valid :
  forall (_: unit), forall (v1: bool),
  (sig_1 bool (fun (result: bool)  => (True))).

(*Why*) Parameter d2_valid :
  forall (_: unit), forall (v4: Z), (sig_1 Z (fun (result: Z)  => (True))).

(*Why*) Parameter ar1_valid : Z.

(*Why*) Parameter ar2_valid : Z.

(*Why*) Parameter ar3_valid : Z.

(*Why*) Parameter ar4_valid : Z.

(*Why*) Parameter ar5_valid : Z.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma ar6_po_1 : 
  1 <> 0.
Proof.
intuition.
Save.












(*Why*) Parameter ar6_valid : Z.

(*Why*) Parameter ar7_valid : Z.

(*Why*) Parameter a1_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter a2_valid :
  forall (_: unit), forall (v1: bool),
  (sig_2 bool unit (fun (v1_0: bool) (result: unit)  => (True))).

(*Why*) Parameter a3_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter a4_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter s1_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter s2_valid :
  forall (_: unit), forall (v1: bool), forall (v4: Z),
  (sig_3 bool Z unit (fun (v1_0: bool) (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter s3_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter s4_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z Z (fun (v4_0: Z) (result: Z)  => (True))).

(*Why*) Parameter c1_valid : Z.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma c2_po_1 : 
  forall (v1: bool),
  (if v1 then True else True).
Proof.
destruct v1; intuition.
Save.



















(*Why*) Parameter c2_valid :
  forall (_: unit), forall (v1: bool), (sig_1 Z (fun (result: Z)  => (True))).

(*Why*) Parameter c3_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter l1_valid : Z.

(*Why*) Parameter l2_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter l3_valid : Z.

(*Why*) Parameter l4_valid :
  forall (_: unit), forall (v4: Z),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter l5_valid :
  forall (_: unit), forall (v1: bool), forall (v4: Z),
  (sig_3 bool Z unit (fun (v1_0: bool) (v4_0: Z) (result: unit)  => (True))).

(*Why*) Parameter lr1_valid : unit.

(*Why*) Parameter lr2_valid : Z.

(*Why*) Parameter lr3_valid : unit.

(*Why*) Parameter r1_valid : bool.

(*Why*) Parameter r2_valid : bool.

(*Why*) Parameter r3_valid : bool.

(*Why*) Parameter r4_valid : bool.

(*Why*) Parameter r5_valid : bool.

(*Why*) Parameter r6_valid : bool.

(*Why*) Parameter r7_valid : bool.

(*Why*) Parameter r8_valid : bool.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr1_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.


(*Why*) Parameter arr1_valid :
  forall (_: unit), forall (v6: (array Z)), forall (_: (array_length v6) >=
  1), (sig_1 Z (fun (result: Z)  => (True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr2_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 4),
  0 <= (1 + 2) /\ (1 + 2) < (array_length v6).
Proof.
intuition.
Save.


(*Why*) Parameter arr2_valid :
  forall (_: unit), forall (v6: (array Z)), forall (_: (array_length v6) >=
  4), (sig_1 Z (fun (result: Z)  => (True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr3_po_1 : 
  forall (v4: Z),
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1 /\ v4 = 0),
  0 <= v4 /\ v4 < (array_length v6).
Proof.
intuition.
Save.


(*Why*) Parameter arr3_valid :
  forall (_: unit), forall (v4: Z), forall (v6: (array Z)),
  forall (_: (array_length v6) >= 1 /\ v4 = 0),
  (sig_1 Z (fun (result: Z)  => (True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr4_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr4_po_2 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (HW_2: 0 <= 0 /\ 0 < (array_length v6)),
  forall (result: Z),
  forall (HW_3: result = (access v6 0)),
  0 <= result /\ result < (array_length v6).
Proof.
intuition.
Save.


(*Why*) Parameter arr4_valid :
  forall (_: unit), forall (v6: (array Z)), forall (_: (array_length v6) >=
  10 /\ (access v6 0) = 9), (sig_1 Z (fun (result: Z)  => (True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr5_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 1),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.


(*Why*) Parameter arr5_valid :
  forall (_: unit), forall (v6: (array Z)), forall (_: (array_length v6) >=
  1),
  (sig_2 (array Z) unit (fun (v6_0: (array Z)) (result: unit)  => (True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr6_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 4),
  0 <= (1 + 2) /\ (1 + 2) < (array_length v6).
Proof.
intuition.
Save.


(*Why*) Parameter arr6_valid :
  forall (_: unit), forall (v6: (array Z)), forall (_: (array_length v6) >=
  4),
  (sig_2 (array Z) unit (fun (v6_0: (array Z)) (result: unit)  => (True))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr7_po_1 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  0 <= 0 /\ 0 < (array_length v6).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma arr7_po_2 : 
  forall (v6: (array Z)),
  forall (HW_1: (array_length v6) >= 10 /\ (access v6 0) = 9),
  forall (HW_2: 0 <= 0 /\ 0 < (array_length v6)),
  forall (result: Z),
  forall (HW_3: result = (access v6 0)),
  0 <= result /\ result < (array_length v6).
Proof.
intuition.
Save.




(*Why*) Parameter arr7_valid :
  forall (_: unit), forall (v6: (array Z)), forall (_: (array_length v6) >=
  10 /\ (access v6 0) = 9),
  (sig_2 (array Z) unit (fun (v6_0: (array Z)) (result: unit)  => (True))).

(*Why*) Parameter fc1_valid : foo.

(*Why*) Parameter fc2_valid : unit.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma fc3_po_1 : 
  0 >= 0.
Proof.
intuition.
Save.



(*Why*) Parameter fc3_valid : Z.

(*Why*) Parameter an1_valid : (sig_1 Z (fun (result: Z)  => (result = 0))).

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma an2_po_1 : 
  forall (v4: Z),
  forall (HW_1: v4 >= 0),
  forall (v4_0: Z),
  forall (HW_2: v4_0 = (v4 + 1)),
  v4_0 > v4.
Proof.
intuition.
Save.






(*Why*) Parameter an2_valid :
  forall (_: unit), forall (v4: Z), forall (_: v4 >= 0),
  (sig_2 Z unit (fun (v4_0: Z) (result: unit)  => (v4_0 > v4))).

(*Why*) Parameter f1_ex : forall (n: Z), (EM unit unit).

(*Why*) Parameter f2_ex : forall (x: Z), (tuple_2 Z (EM unit (EM Z bool))).

