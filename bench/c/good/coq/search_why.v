(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export search_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_1 : 
  forall (A779:Set),
  forall (t: ((pointer) A779)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  0 <= 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_2 : 
  forall (A780:Set),
  forall (t: ((pointer) A780)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_7: ((memory) Z A780)),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (k: Z),
  forall (HW_2: 0 <= k /\ k < 0),
  (acc intM_t_7 (shift t k)) <> v.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_3 : 
  forall (A781:Set),
  forall (t: ((pointer) A781)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_7: ((memory) Z A781)),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 27, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 27, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A781)),
  forall (HW_6: result = (shift t i)),
  (valid alloc result).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_4 : 
  forall (A782:Set),
  forall (t: ((pointer) A782)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_7: ((memory) Z A782)),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 27, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 27, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A782)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_7 result)),
  forall (HW_9: result0 = v),
  forall (HW_10: 0 <= i /\ i < n),
  (acc intM_t_7 (shift t i)) = v.
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_5 : 
  forall (A783:Set),
  forall (t: ((pointer) A783)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_7: ((memory) Z A783)),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 27, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 27, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A783)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_7 result)),
  forall (HW_11: result0 <> v),
  forall (i0: Z),
  forall (HW_12: i0 = (i + 1)),
  0 <= i0.
Proof.
intuition.
Save.

Proof.
intuition.
assert (k=i \/ k<i).
  omega.
intuition.
subst; auto.
apply H4 with k; auto.
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_6 : 
  forall (A784:Set),
  forall (t: ((pointer) A784)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_7: ((memory) Z A784)),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 27, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 27, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A784)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_7 result)),
  forall (HW_11: result0 <> v),
  forall (i0: Z),
  forall (HW_12: i0 = (i + 1)),
  forall (k: Z),
  forall (HW_13: 0 <= k /\ k < i0),
  (acc intM_t_7 (shift t k)) <> v.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_7 : 
  forall (A785:Set),
  forall (t: ((pointer) A785)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_7: ((memory) Z A785)),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 27, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 27, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A785)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_7 result)),
  forall (HW_11: result0 <> v),
  forall (i0: Z),
  forall (HW_12: i0 = (i + 1)),
  (Zwf 0 (n - i0) (n - i)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index2_impl_po_8 : 
  forall (A786:Set),
  forall (t: ((pointer) A786)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_7: ((memory) Z A786)),
  forall (HW_1: (* File "search.c", line 22, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 27, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 27, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_7 (shift t k)) <> v)))),
  forall (HW_14: i >= n),
  forall (HW_15: 0 <= n /\ n < n),
  (acc intM_t_7 (shift t n)) = v.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_1 : 
  forall (A787:Set),
  forall (t: ((pointer) A787)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  0 <= 0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_2 : 
  forall (A788:Set),
  forall (t: ((pointer) A788)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A788)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (k: Z),
  forall (HW_2: 0 <= k /\ k < 0),
  (acc intM_t_6 (shift t k)) <> v.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_3 : 
  forall (A789:Set),
  forall (t: ((pointer) A789)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A789)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A789)),
  forall (HW_6: result = (shift t i)),
  (valid alloc result).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_4 : 
  forall (A790:Set),
  forall (t: ((pointer) A790)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A790)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A790)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_6 result)),
  forall (HW_9: result0 = v),
  forall (HW_10: 0 <= i /\ i < n),
  (acc intM_t_6 (shift t i)) = v.
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_5 : 
  forall (A791:Set),
  forall (t: ((pointer) A791)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A791)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A791)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_6 result)),
  forall (HW_9: result0 = v),
  forall (HW_11: i = n),
  forall (i0: Z),
  forall (HW_12: 0 <= i0 /\ i0 < n),
  (acc intM_t_6 (shift t i0)) <> v.
Proof.
intuition.
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
assert (k=i\/ k < i).
  omega.
intuition.
subst; auto.
apply H4 with k;auto.

Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
assert (i0=i\/ i0 < i).
  omega.
intuition.
apply H4 with i0;auto.
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_6 : 
  forall (A792:Set),
  forall (t: ((pointer) A792)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A792)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A792)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_6 result)),
  forall (HW_13: result0 <> v),
  forall (i0: Z),
  forall (HW_14: i0 = (i + 1)),
  0 <= i0.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_7 : 
  forall (A793:Set),
  forall (t: ((pointer) A793)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A793)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A793)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_6 result)),
  forall (HW_13: result0 <> v),
  forall (i0: Z),
  forall (HW_14: i0 = (i + 1)),
  forall (k: Z),
  forall (HW_15: 0 <= k /\ k < i0),
  (acc intM_t_6 (shift t k)) <> v.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_8 : 
  forall (A794:Set),
  forall (t: ((pointer) A794)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A794)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_5: i < n),
  forall (result: ((pointer) A794)),
  forall (HW_6: result = (shift t i)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc intM_t_6 result)),
  forall (HW_13: result0 <> v),
  forall (i0: Z),
  forall (HW_14: i0 = (i + 1)),
  (Zwf 0 (n - i0) (n - i)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_9 : 
  forall (A795:Set),
  forall (t: ((pointer) A795)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A795)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_16: i >= n),
  forall (HW_17: 0 <= i /\ i < n),
  (acc intM_t_6 (shift t i)) = v.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma index_impl_po_10 : 
  forall (A796:Set),
  forall (t: ((pointer) A796)),
  forall (n: Z),
  forall (v: Z),
  forall (alloc: alloc_table),
  forall (intM_t_6: ((memory) Z A796)),
  forall (HW_1: (* File "search.c", line 4, characters 14-35 *)
                (valid_range alloc t 0 (n - 1)) /\ (valid_range alloc t 0 3)),
  forall (HW_3: (* File "search.c", line 11, characters 17-65 *) (0 <= 0 /\
                (forall (k:Z),
                 (0 <= k /\ k < 0 -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (i: Z),
  forall (HW_4: (* File "search.c", line 11, characters 17-65 *) (0 <= i /\
                (forall (k:Z),
                 (0 <= k /\ k < i -> (acc intM_t_6 (shift t k)) <> v)))),
  forall (HW_16: i >= n),
  forall (HW_18: i = n),
  forall (i0: Z),
  forall (HW_19: 0 <= i0 /\ i0 < n),
  (acc intM_t_6 (shift t i0)) <> v.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (t: ((pointer) t_8)),
  forall (HW_1: (valid_range alloc t 0 3)),
  (* File "search.c", line 4, characters 14-35 *)
  (valid_range alloc t 0 (4 - 1)).
Proof.
intuition.
Save.

