(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.


(* Why obligation from file "search.mlw", characters 383-388 *)
Lemma search1_po_1 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = ((array_length t) - i1)),
  forall (Pre7: 0 <= i1 /\
                (forall (k:Z), (0 <= k /\ k < i1 -> (access t k) <> 0))),
  forall (Test4: i1 < (array_length t)),
  0 <= i1 /\ i1 < (array_length t).
Proof.
auto with *.
Qed.

(* Why obligation from file "search.mlw", characters 414-414 *)
Lemma search1_po_2 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = ((array_length t) - i1)),
  forall (Pre7: 0 <= i1 /\
                (forall (k:Z), (0 <= k /\ k < i1 -> (access t k) <> 0))),
  forall (Test4: i1 < (array_length t)),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t)),
  forall (Test2: (access t i1) <> 0),
  (forall (i:Z),
   (i = (i1 + 1) -> (0 <= i /\
    (forall (k:Z), (0 <= k /\ k < i -> (access t k) <> 0))) /\
    (Zwf 0 ((array_length t) - i) ((array_length t) - i1)))).
Proof.
intuition.
assert (k = i1 \/ (k < i1)%Z).
 omega.
 intuition.
subst k.
 auto.
apply (H0 k).
 omega.
 assumption.
Qed.

(* Why obligation from file "search.mlw", characters 237-442 *)
Lemma search1_po_3 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = ((array_length t) - i1)),
  forall (Pre7: 0 <= i1 /\
                (forall (k:Z), (0 <= k /\ k < i1 -> (access t k) <> 0))),
  forall (Test1: i1 >= (array_length t)),
  (forall (k:Z), (0 <= k /\ k < (array_length t) -> (access t k) <> 0)).
Proof.
intuition.
apply (H0 k); omega.
Qed.

(* Why obligation from file "search.mlw", characters 286-334 *)
Lemma search1_po_4 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  0 <= i /\ (forall (k:Z), (0 <= k /\ k < i -> (access t k) <> 0)).
Proof.
intuition.
Qed.


(* Why obligation from file "search.mlw", characters 885-890 *)
Lemma search2_po_1 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = ((array_length t) - i1)),
  forall (Pre7: 0 <= i1 /\
                (forall (k:Z), (0 <= k /\ k < i1 -> (access t k) <> 0))),
  forall (Test4: i1 < (array_length t)),
  0 <= i1 /\ i1 < (array_length t).
Proof.
auto with *.
Qed.

(* Why obligation from file "search.mlw", characters 911-911 *)
Lemma search2_po_2 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = ((array_length t) - i1)),
  forall (Pre7: 0 <= i1 /\
                (forall (k:Z), (0 <= k /\ k < i1 -> (access t k) <> 0))),
  forall (Test4: i1 < (array_length t)),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t)),
  forall (Test2: (access t i1) <> 0),
  (forall (i:Z),
   (i = (i1 + 1) -> (0 <= i /\
    (forall (k:Z), (0 <= k /\ k < i -> (access t k) <> 0))) /\
    (Zwf 0 ((array_length t) - i) ((array_length t) - i1)))).
Proof.
intuition.
assert (k = i1 \/ (k < i1)%Z).
 omega.
 intuition.
subst k.
 auto.
apply (H0 k).
 omega.
 assumption.
Qed.

(* Why obligation from file "search.mlw", characters 740-939 *)
Lemma search2_po_3 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre8: Variant1 = ((array_length t) - i1)),
  forall (Pre7: 0 <= i1 /\
                (forall (k:Z), (0 <= k /\ k < i1 -> (access t k) <> 0))),
  forall (Test1: i1 >= (array_length t)),
  (forall (k:Z), (0 <= k /\ k < (array_length t) -> (access t k) <> 0)).
Proof.
intuition.
apply (H0 k); omega.
Qed.

(* Why obligation from file "search.mlw", characters 789-837 *)
Lemma search2_po_4 : 
  forall (t: (array Z)),
  forall (i: Z),
  forall (Post2: i = 0),
  0 <= i /\ (forall (k:Z), (0 <= k /\ k < i -> (access t k) <> 0)).
Proof.
intuition.
Qed.


(* Why obligation from file "search.mlw", characters 1503-1517 *)
Lemma search3_po_1 : 
  forall (t: (array Z)),
  forall (Pre17: 0 <= (array_length t)),
  0 <= 0 /\ 0 <= (array_length t).
Proof.
intros; omega.
Qed.

(* Why obligation from file "search.mlw", characters 1314-1335 *)
Lemma search3_po_2 : 
  forall (t: (array Z)),
  forall (Pre17: 0 <= (array_length t)),
  forall (Pre16: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre14: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre15: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Variant1: Z),
  forall (i0: Z),
  forall (Pre12: Variant1 = ((array_length t) - i0)),
  forall (Pre11: 0 <= i0 /\ i0 <= (array_length t)),
  forall (Test4: i0 = (array_length t)),
  (forall (k:Z), (i0 <= k /\ k < (array_length t) -> (access t k) <> 0)).
Proof.
intros; omega.
Qed.

(* Why obligation from file "search.mlw", characters 1350-1354 *)
Lemma search3_po_3 : 
  forall (t: (array Z)),
  forall (Pre17: 0 <= (array_length t)),
  forall (Pre16: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre14: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre15: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Variant1: Z),
  forall (i0: Z),
  forall (Pre12: Variant1 = ((array_length t) - i0)),
  forall (Pre11: 0 <= i0 /\ i0 <= (array_length t)),
  forall (Test3: i0 <> (array_length t)),
  0 <= i0 /\ i0 < (array_length t).
Proof.
intuition.
Qed.

(* Why obligation from file "search.mlw", characters 1377-1397 *)
Lemma search3_po_4 : 
  forall (t: (array Z)),
  forall (Pre17: 0 <= (array_length t)),
  forall (Pre16: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre14: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre15: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Variant1: Z),
  forall (i0: Z),
  forall (Pre12: Variant1 = ((array_length t) - i0)),
  forall (Pre11: 0 <= i0 /\ i0 <= (array_length t)),
  forall (Test3: i0 <> (array_length t)),
  forall (Pre10: 0 <= i0 /\ i0 < (array_length t)),
  forall (Test1: (access t i0) <> 0),
  0 <= (i0 + 1) /\ (i0 + 1) <= (array_length t).
Proof.
intuition.
Qed.

(* Why obligation from file "search.mlw", characters 1249-1494 *)
Lemma search3_po_5 : 
  forall (t: (array Z)),
  forall (Pre17: 0 <= (array_length t)),
  forall (Pre16: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre14: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre15: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Variant1: Z),
  forall (i0: Z),
  forall (Pre12: Variant1 = ((array_length t) - i0)),
  forall (Pre11: 0 <= i0 /\ i0 <= (array_length t)),
  forall (Test3: i0 <> (array_length t)),
  forall (Pre10: 0 <= i0 /\ i0 < (array_length t)),
  forall (Test1: (access t i0) <> 0),
  forall (Pre9: 0 <= (i0 + 1) /\ (i0 + 1) <= (array_length t)),
  forall (Pre7: 0 <= (i0 + 1) /\ (i0 + 1) <= (array_length t)),
  forall (Pre8: 0 <= (i0 + 1) /\ (i0 + 1) <= (array_length t)),
  (Zwf 0 ((array_length t) - (i0 + 1)) Variant1).
Proof.
unfold Zwf; intuition.
Qed.

(* Why obligation from file "search.mlw", characters 1377-1397 *)
Lemma search3_po_6 : 
  forall (t: (array Z)),
  forall (Pre17: 0 <= (array_length t)),
  forall (Pre16: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre14: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Pre15: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Variant1: Z),
  forall (i0: Z),
  forall (Pre12: Variant1 = ((array_length t) - i0)),
  forall (Pre11: 0 <= i0 /\ i0 <= (array_length t)),
  forall (Test3: i0 <> (array_length t)),
  forall (Pre10: 0 <= i0 /\ i0 < (array_length t)),
  forall (Test1: (access t i0) <> 0),
  forall (Pre9: 0 <= (i0 + 1) /\ (i0 + 1) <= (array_length t)),
  forall (Post11: (forall (k:Z),
                   ((i0 + 1) <= k /\ k < (array_length t) -> (access t k) <>
                    0))),
  (forall (k:Z), (i0 <= k /\ k < (array_length t) -> (access t k) <> 0)).
Proof.
intuition.
assert (k = i0 \/ (i0 < k)%Z).
 omega.
 intuition.
subst k; auto.
apply Post11 with k; omega.
Qed.

(* Why obligation from file "search.mlw", characters 1149-1608 *)
Lemma search3_po_7 : 
  forall (t: (array Z)),
  forall (Pre17: 0 <= (array_length t)),
  forall (Pre16: 0 <= 0 /\ 0 <= (array_length t)),
  forall (Post23: (forall (k:Z),
                   (0 <= k /\ k < (array_length t) -> (access t k) <> 0))),
  (forall (k:Z), (0 <= k /\ k < (array_length t) -> (access t k) <> 0)).
Proof.
trivial.
Qed.

