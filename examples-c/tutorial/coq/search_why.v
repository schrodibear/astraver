(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export search_spec_why.

(* Why obligation from file "search.c", line 8, characters 18-66: *)
(*Why goal*) Lemma index_impl_po_1 : 
  forall (t: (pointer global)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_global: (memory Z global)),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  (* File "search.c", line 8, characters 17-65 *) (0 <= 0 /\
  (forall (k:Z), (0 <= k /\ k < 0 -> (acc intM_global (shift t k)) <> v))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_2 : 
  forall (t: (pointer global)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_global: (memory Z global)),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_global (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: (pointer global)),
  forall (HW_4: result = (shift t i)),
  (valid alloc result).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "search.c", line 3, characters 6-107: *)
(*Why goal*) Lemma index_impl_po_3 : 
  forall (t: (pointer global)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_global: (memory Z global)),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_global (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: (pointer global)),
  forall (HW_4: result = (shift t i)),
  forall (HW_5: (valid alloc result)),
  forall (result0: Z),
  forall (HW_6: result0 = (acc intM_global result)),
  forall (HW_7: result0 = v),
  (* File "search.c", line 3, characters 5-106 *)
  (((0 <= i /\ i < n -> (acc intM_global (shift t i)) = v)) /\
  ((i = n ->
    (forall (i:Z), (0 <= i /\ i < n -> (acc intM_global (shift t i)) <> v))))).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_4 : 
  forall (t: (pointer global)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_global: (memory Z global)),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_global (shift t k)) <> v)))),
  forall (HW_3: i < n),
  forall (result: (pointer global)),
  forall (HW_4: result = (shift t i)),
  forall (HW_5: (valid alloc result)),
  forall (result0: Z),
  forall (HW_6: result0 = (acc intM_global result)),
  forall (HW_8: result0 <> v),
  forall (i0: Z),
  forall (HW_9: i0 = (i + 1)),
  (* File "search.c", line 8, characters 17-65 *) (0 <= i0 /\
  (forall (k:Z), (0 <= k /\ k < i0 -> (acc intM_global (shift t k)) <> v))) /\
  (Zwf 0 (n - i0) (n - i)).
Proof.
intuition.
assert (h : k<i \/ k=i); [ omega | inversion_clear h].
(* case k < i *)
apply (H0 k); auto.
(* case k=i *)
subst; auto.
Save.

(* Why obligation from file "search.c", line 3, characters 6-107: *)
(*Why goal*) Lemma index_impl_po_5 : 
  forall (t: (pointer global)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_global: (memory Z global)),
  forall (HW_1: (* File "search.c", line 1, characters 14-35 *)
                (valid_range alloc t 0 (n - 1))),
  forall (i: Z),
  forall (HW_2: (* File "search.c", line 8, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_global (shift t k)) <> v)))),
  forall (HW_10: i >= n),
  (* File "search.c", line 3, characters 5-106 *)
  (((0 <= i /\ i < n -> (acc intM_global (shift t i)) = v)) /\
  ((i = n ->
    (forall (i:Z), (0 <= i /\ i < n -> (acc intM_global (shift t i)) <> v))))).
Proof.
intuition.
apply H0 with i0; auto with *.
Save.
