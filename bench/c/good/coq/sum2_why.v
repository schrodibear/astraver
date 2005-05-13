
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

(* Why obligation from file "why/sum2.why", characters 452-453 *)
Lemma test1_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post6: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum alloc intP t 0 i2)),
  forall (Test2: i2 < n),
  (forall (result:pointer),
   (result = (shift t i2) ->
    (forall (result0:Z),
     (result0 = (acc intP result) -> (s1 + result0) =
      (s1 + (acc intP (shift t i2))))) /\
    (valid alloc result))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 430-555 *)
Lemma test1_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post6: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum alloc intP t 0 i2)),
  forall (Test2: i2 < n),
  forall (s2: Z),
  forall (Post3: s2 = (s1 + (acc intP (shift t i2)))),
  forall (i3: Z),
  forall (Post4: i3 = (i2 + 1)),
  ((0 <= i3 /\ i3 <= n) /\ s2 = (sum alloc intP t 0 i3)) /\
  (Zwf 0 (n - i3) (n - i2)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 243-565 *)
Lemma test1_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post6: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (s1: Z),
  forall (Pre5: Variant1 = (n - i2)),
  forall (Pre4: (0 <= i2 /\ i2 <= n) /\ s1 = (sum alloc intP t 0 i2)),
  forall (Test1: i2 >= n),
  (forall (result:Z), (result = s1 -> result = (sum alloc intP t 0 n))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 300-385 *)
Lemma test1_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 n)),
  forall (s: Z),
  forall (Post6: s = 0),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ s = (sum alloc intP t 0 i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 1170-1192 *)
Lemma test2_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre7: Variant1 = (n - i2)),
  forall (Pre6: (0 <= i2 /\ i2 <= n) /\ (sum alloc intP0 t 0 n) =
                ((sum alloc intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post6: caduceus1 = (shift t i2)),
  (valid alloc caduceus1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 1154-1252 *)
Lemma test2_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre7: Variant1 = (n - i2)),
  forall (Pre6: (0 <= i2 /\ i2 <= n) /\ (sum alloc intP0 t 0 n) =
                ((sum alloc intP t 0 n) + i2)),
  forall (Test2: i2 < n),
  forall (caduceus1: pointer),
  forall (Post6: caduceus1 = (shift t i2)),
  forall (Pre5: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post5: caduceus2 = (acc intP0 caduceus1)),
  forall (Pre4: (valid alloc caduceus1)),
  forall (intP1: ((memory) Z)),
  forall (Post17: intP1 = (upd intP0 caduceus1 (caduceus2 + 1))),
  (forall (i:Z),
   (i = (i2 + 1) -> ((0 <= i /\ i <= n) /\ (sum alloc intP1 t 0 n) =
    ((sum alloc intP t 0 n) + i)) /\ (Zwf 0 (n - i) (n - i2)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 881-1290 *)
Lemma test2_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  forall (Variant1: Z),
  forall (i2: Z),
  forall (intP0: ((memory) Z)),
  forall (Pre7: Variant1 = (n - i2)),
  forall (Pre6: (0 <= i2 /\ i2 <= n) /\ (sum alloc intP0 t 0 n) =
                ((sum alloc intP t 0 n) + i2)),
  forall (Test1: i2 >= n),
  (sum alloc intP0 t 0 n) = ((sum alloc intP t 0 n) + n) /\
  (not_assigns alloc intP intP0 (pset_all (pset_singleton t))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/sum2.why", characters 934-1071 *)
Lemma test2_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre8: (valid_range alloc t 0 n)),
  forall (i1: Z),
  forall (Post1: i1 = 0),
  (0 <= i1 /\ i1 <= n) /\ (sum alloc intP t 0 n) =
  ((sum alloc intP t 0 n) + i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

