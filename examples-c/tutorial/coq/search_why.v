(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/search.why", characters 427-508 *)
Lemma index_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post6: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test4: i1 < n),
  (valid alloc (shift t i1)).
Proof.
intuition.
Save.

(* Why obligation from file "why/search.why", characters 521-527 *)
Lemma index_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post6: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test4: i1 < n),
  forall (Pre3: (valid alloc (shift t i1))),
  forall (Test3: (acc intP (shift t i1)) = v),
  (forall (result:unit),
   (result = tt ->
    (forall (result:Z),
     (result = i1 ->
      ((0 <= result /\ result < n -> (acc intP (shift t result)) = v)) /\
      ((result = n ->
        (forall (i:Z), (0 <= i /\ i < n -> (acc intP (shift t i)) <> v)))))))).
Proof.
intuition.
subst.
auto.
Save.

(* Why obligation from file "why/search.why", characters 544-564 *)
Lemma index_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post6: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test4: i1 < n),
  forall (Pre3: (valid alloc (shift t i1))),
  forall (Test2: (acc intP (shift t i1)) <> v),
  forall (i2: Z),
  forall (Post3: i2 = (i1 + 1)),
  (0 <= i2 /\
  (forall (k:Z), (0 <= k /\ k < i2 -> (acc intP (shift t k)) <> v))) /\
  (Zwf 0 (n - i2) (n - i1)).
Proof.
intuition.
assert (k<i1 \/ k=i1).
omega.
intuition.
apply (H0 k); intuition.
apply Test2.
subst; auto.
Save.

(* Why obligation from file "why/search.why", characters 191-571 *)
Lemma index_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post6: i = 0),
  forall (Variant1: Z),
  forall (i1: Z),
  forall (Pre5: Variant1 = (n - i1)),
  forall (Pre4: 0 <= i1 /\
                (forall (k:Z),
                 (0 <= k /\ k < i1 -> (acc intP (shift t k)) <> v))),
  forall (Test1: i1 >= n),
  (forall (result:Z),
   (result = i1 ->
    ((0 <= result /\ result < n -> (acc intP (shift t result)) = v)) /\
    ((result = n ->
      (forall (i:Z), (0 <= i /\ i < n -> (acc intP (shift t i)) <> v)))))).
Proof.
intuition.
apply H0 with i0.
omega.
subst;auto.
Save.

(* Why obligation from file "why/search.why", characters 242-385 *)
Lemma index_impl_po_5 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre6: (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (Post6: i = 0),
  0 <= i /\ (forall (k:Z), (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)).
Proof.
intuition.
Save.

