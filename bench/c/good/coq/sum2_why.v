
Require Import caduceus_why.


Admitted.

Admitted.

Proof.
intuition.
apply shift_not_null with (p:=t) (i:=i2).
apply valid_not_null with (i:=0) (j:=n).
auto.
subst; auto.
subst aux_1.
rewrite offset_shift.
assert (0 <= offset t + 0).
apply valid1 with (p:=t) (i:=0) (j:=n). 
assumption.
omega.
subst aux_1.
rewrite offset_shift.
rewrite length_shift.
assert (offset t + n <= length t).
apply valid3 with (i:=0).
assumption.
omega.
Qed.

Proof.
intuition; subst; auto with *.
(* rewrite sum2... *)
Admitted.

Proof.
intuition.
assert (0<=n).
apply valid2 with t; auto.
omega.
subst.
(* rewrite sum1... *)
Admitted.

Proof.
intuition.
assert (i2=n).
omega.
subst; auto.
Save.

Proof.
Admitted.



Proof.
intuition; subst; auto with *.
(* TODO *)
Save.


Proof.
(* FILL PROOF HERE *)
Save.

Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 380-409 *)
Lemma test1_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post3: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post13: aux_1 = (shift t i2)),
  (valid alloc aux_1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 380-409 *)
Lemma test1_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post3: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)),
  forall (Test2: i2 < n),
  forall (aux_1: pointer),
  forall (Post13: aux_1 = (shift t i2)),
  forall (Pre2: (valid alloc aux_1)),
  forall (result1: Z),
  forall (Post15: result1 = (acc intP aux_1)),
  (forall (i:Z),
   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (s1 + result1) =
    (sum intP t 0 i)) /\ (Zwf 0 (n - i) (n - i2)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 209-447 *)
Lemma test1_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post3: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum intP t 0 i2)),
  forall (Test1: i2 >= n),
  s1 = (sum intP t 0 n).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 258-325 *)
Lemma test1_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post3: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ s = (sum intP t 0 i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 982-1005 *)
Lemma test2_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre9: Variant1 = (n - i2)),
  forall (Pre8: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post16: caduceus1 = (shift t i2)),
  (valid alloc caduceus1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 966-1064 *)
Lemma test2_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre9: Variant1 = (n - i2)),
  forall (Pre8: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post16: caduceus1 = (shift t i2)),
  forall (Pre7: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post18: caduceus2 = (acc intP0 caduceus1)),
  forall (Pre6: (valid alloc caduceus1)),
  forall (intP1: ((memory) Z)),
  forall (Post20: intP1 = (upd intP0 caduceus1 (caduceus2 + 1))),
  (forall (i:Z),
   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (sum intP1 t 0 n) =
    ((sum intP t 0 n) + i)) /\ (Zwf 0 (n - i) (n - i2)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 729-1103 *)
Lemma test2_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre9: Variant1 = (n - i2)),
  forall (Pre8: (0 <= i2 /\ i2 <= n) /\ (sum intP0 t 0 n) =
                ((sum intP t 0 n) + i2)),
  forall (Test1: i2 >= n),
  (sum intP0 t 0 n) = ((sum intP t 0 n) + n) /\
  (assigns alloc intP intP0 (all_loc t)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 780-887 *)
Lemma test2_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre10: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ (sum intP t 0 n) = ((sum intP t 0 n) + i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

