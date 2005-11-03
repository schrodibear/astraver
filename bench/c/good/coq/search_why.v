(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export search_spec_why.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
  (0 <= 0 /\
  (forall (k:Z), (0 <= k /\ k < 0 -> (acc intP (shift t k)) <> v))).
Proof.
intuition.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: pointer),
  forall (HW_4: result = (shift t i)),
  forall (result0: Z),
  forall (HW_5: result0 = (acc intP result)),
  forall (HW_6: result0 = v),
  (* File \"search.c819618234.c\", line 0, characters 6-41 *)
  ((0 <= i /\ i < n -> (acc intP (shift t i)) = v)).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: pointer),
  forall (HW_4: result = (shift t i)),
  forall (result0: Z),
  forall (HW_5: result0 = (acc intP result)),
  forall (HW_7: result0 <> v),
  forall (i0: Z),
  forall (HW_8: i0 = (i + 1)),
  (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
  (0 <= i0 /\
  (forall (k:Z), (0 <= k /\ k < i0 -> (acc intP (shift t k)) <> v))) /\
  (Zwf 0 (n - i0) (n - i)).
Proof.
intuition.
assert (k=i1 \/ k<i1).
  omega.
intuition.
subst; auto.
apply H0 with k; auto.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: pointer),
  forall (HW_4: result = (shift t i)),
  (valid alloc result).
Proof.
intuition.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_5 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_9: i >= n),
  (* File \"search.c819618234.c\", line 0, characters 6-41 *)
  ((0 <= n /\ n < n -> (acc intP (shift t n)) = v)).
Proof.
intuition.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
  (0 <= 0 /\
  (forall (k:Z), (0 <= k /\ k < 0 -> (acc intP (shift t k)) <> v))).
Proof.
intuition.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: pointer),
  forall (HW_4: result = (shift t i)),
  forall (result0: Z),
  forall (HW_5: result0 = (acc intP result)),
  forall (HW_6: result0 = v),
  (* File \"search.c819618234.c\", line 0, characters 10-111 *)
  (((0 <= i /\ i < n -> (acc intP (shift t i)) = v)) /\
  ((i = n -> (forall (i:Z), (0 <= i /\ i < n -> (acc intP (shift t i)) <> v))))).
Proof.
intuition.
subst; auto.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: pointer),
  forall (HW_4: result = (shift t i)),
  forall (result0: Z),
  forall (HW_5: result0 = (acc intP result)),
  forall (HW_7: result0 <> v),
  forall (i0: Z),
  forall (HW_8: i0 = (i + 1)),
  (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
  (0 <= i0 /\
  (forall (k:Z), (0 <= k /\ k < i0 -> (acc intP (shift t k)) <> v))) /\
  (Zwf 0 (n - i0) (n - i)).
Proof.
intuition.
assert (k=i1\/ k < i1).
  omega.
inversion_clear H1.
subst; auto.
apply H0 with k;auto.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: pointer),
  forall (HW_4: result = (shift t i)),
  (valid alloc result).
Proof.
intuition.
subst.
apply H0 with i0; auto with *.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_5 : 
  forall (t: pointer),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (HW_1: (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File \"search.c819618234.c1069824147.i\", line 0, characters 11-59 *)
                (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intP (shift t k)) <> v)))),
  forall (HW_9: i >= n),
  (* File \"search.c819618234.c\", line 0, characters 10-111 *)
  (((0 <= i /\ i < n -> (acc intP (shift t i)) = v)) /\
  ((i = n -> (forall (i:Z), (0 <= i /\ i < n -> (acc intP (shift t i)) <> v))))).
Proof.
intuition.
Save.

(* Why obligation from file "why/search.why", line 0, characters 0-0: *)
(*Why goal*) Lemma test_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (HW_1: (valid_range alloc t 0 3)),
  (* File \"search.c819618234.c1069824147.i\", line 0, characters 10-31 *)
  (valid_range alloc t 0 (4 - 1)).
Proof.
intuition.
Save.

