(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export all_zeros_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_0_impl_po_1 : 
  forall (t: ((pointer) Z5)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z5: ((memory) Z Z5)),
  forall (HW_1: (* File "all_zeros.c", line 24, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (k: Z),
  forall (HW_3: k = 0),
  (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <= k /\ k <= n) /\
  (forall (i:Z), (0 <= i /\ i < k -> (acc int_Z5 (shift t i)) = 0))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_0_impl_po_2 : 
  forall (t: ((pointer) Z5)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z5: ((memory) Z Z5)),
  forall (HW_1: (* File "all_zeros.c", line 24, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (k: Z),
  forall (HW_3: k = 0),
  forall (HW_4: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k /\ k <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k -> (acc int_Z5 (shift t i)) = 0)))),
  forall (k0: Z),
  forall (HW_5: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k0 /\ k0 <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k0 -> (acc int_Z5 (shift t i)) = 0)))),
  forall (HW_6: k0 < n),
  forall (result: ((pointer) Z5)),
  forall (HW_7: result = (shift t k0)),
  (valid alloc result).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_0_impl_po_3 : 
  forall (t: ((pointer) Z5)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z5: ((memory) Z Z5)),
  forall (HW_1: (* File "all_zeros.c", line 24, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (k: Z),
  forall (HW_3: k = 0),
  forall (HW_4: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k /\ k <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k -> (acc int_Z5 (shift t i)) = 0)))),
  forall (k0: Z),
  forall (HW_5: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k0 /\ k0 <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k0 -> (acc int_Z5 (shift t i)) = 0)))),
  forall (HW_6: k0 < n),
  forall (result: ((pointer) Z5)),
  forall (HW_7: result = (shift t k0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc int_Z5 result)),
  forall (HW_10: result0 <> 0),
  (* File "all_zeros.c", line 25, characters 13-57 *)
  ((0 <> 0 <->
    (forall (i:Z), (0 <= i /\ i < n -> (acc int_Z5 (shift t i)) = 0)))).
Proof.
intuition; subst.
assert (i=k2 \/ i<k2). omega. intuition.
subst; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_0_impl_po_4 : 
  forall (t: ((pointer) Z5)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z5: ((memory) Z Z5)),
  forall (HW_1: (* File "all_zeros.c", line 24, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (k: Z),
  forall (HW_3: k = 0),
  forall (HW_4: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k /\ k <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k -> (acc int_Z5 (shift t i)) = 0)))),
  forall (k0: Z),
  forall (HW_5: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k0 /\ k0 <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k0 -> (acc int_Z5 (shift t i)) = 0)))),
  forall (HW_6: k0 < n),
  forall (result: ((pointer) Z5)),
  forall (HW_7: result = (shift t k0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc int_Z5 result)),
  forall (HW_11: result0 = 0),
  forall (k1: Z),
  forall (HW_12: k1 = (k0 + 1)),
  (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <= k1 /\ k1 <=
  n) /\ (forall (i:Z), (0 <= i /\ i < k1 -> (acc int_Z5 (shift t i)) = 0))) /\
  (Zwf 0 (n - k1) (n - k0)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_0_impl_po_5 : 
  forall (t: ((pointer) Z5)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z5: ((memory) Z Z5)),
  forall (HW_1: (* File "all_zeros.c", line 24, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (k: Z),
  forall (HW_3: k = 0),
  forall (HW_4: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k /\ k <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k -> (acc int_Z5 (shift t i)) = 0)))),
  forall (k0: Z),
  forall (HW_5: (* File "all_zeros.c", line 28, characters 17-64 *) ((0 <=
                k0 /\ k0 <= n) /\
                (forall (i:Z),
                 (0 <= i /\ i < k0 -> (acc int_Z5 (shift t i)) = 0)))),
  forall (HW_13: k0 >= n),
  (* File "all_zeros.c", line 25, characters 13-57 *)
  ((1 <> 0 <->
    (forall (i:Z), (0 <= i /\ i < n -> (acc int_Z5 (shift t i)) = 0)))).
Proof.
intuition.
unfold valid_range in Pre6; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_impl_po_1 : 
  forall (t: ((pointer) Z4)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "all_zeros.c", line 4, characters 14-33 *)
                (valid_range alloc t 0 n)),
  (* File "all_zeros.c", line 7, characters 17-71 *) (n <= n /\
  (forall (i:Z), (n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0))).
Proof.
intuition; subst.
assert (i=mutable_n1-1 \/ mutable_n1<=i). omega. intuition.
subst; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_impl_po_2 : 
  forall (t: ((pointer) Z4)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "all_zeros.c", line 4, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (HW_2: (* File "all_zeros.c", line 7, characters 17-71 *) (n <= n /\
                (forall (i:Z),
                 (n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n: Z),
  forall (HW_3: (* File "all_zeros.c", line 7, characters 17-71 *)
                (mutable_n <= n /\
                (forall (i:Z),
                 (mutable_n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n0: Z),
  forall (HW_4: mutable_n0 = (mutable_n - 1)),
  forall (HW_5: mutable_n0 >= 0),
  forall (result: ((pointer) Z4)),
  forall (HW_6: result = (shift t mutable_n0)),
  (valid alloc result).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_impl_po_3 : 
  forall (t: ((pointer) Z4)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "all_zeros.c", line 4, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (HW_2: (* File "all_zeros.c", line 7, characters 17-71 *) (n <= n /\
                (forall (i:Z),
                 (n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n: Z),
  forall (HW_3: (* File "all_zeros.c", line 7, characters 17-71 *)
                (mutable_n <= n /\
                (forall (i:Z),
                 (mutable_n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n0: Z),
  forall (HW_4: mutable_n0 = (mutable_n - 1)),
  forall (HW_5: mutable_n0 >= 0),
  forall (result: ((pointer) Z4)),
  forall (HW_6: result = (shift t mutable_n0)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc int_Z4 result)),
  forall (HW_9: result0 <> 0),
  forall (HW_10: mutable_n0 < 0),
  (* File "all_zeros.c", line 5, characters 13-57 *)
  ((1 <> 0 <->
    (forall (i:Z), (0 <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_impl_po_4 : 
  forall (t: ((pointer) Z4)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "all_zeros.c", line 4, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (HW_2: (* File "all_zeros.c", line 7, characters 17-71 *) (n <= n /\
                (forall (i:Z),
                 (n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n: Z),
  forall (HW_3: (* File "all_zeros.c", line 7, characters 17-71 *)
                (mutable_n <= n /\
                (forall (i:Z),
                 (mutable_n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n0: Z),
  forall (HW_4: mutable_n0 = (mutable_n - 1)),
  forall (HW_5: mutable_n0 >= 0),
  forall (result: ((pointer) Z4)),
  forall (HW_6: result = (shift t mutable_n0)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc int_Z4 result)),
  forall (HW_9: result0 <> 0),
  forall (HW_11: mutable_n0 >= 0),
  (* File "all_zeros.c", line 5, characters 13-57 *)
  ((0 <> 0 <->
    (forall (i:Z), (0 <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_impl_po_5 : 
  forall (t: ((pointer) Z4)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "all_zeros.c", line 4, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (HW_2: (* File "all_zeros.c", line 7, characters 17-71 *) (n <= n /\
                (forall (i:Z),
                 (n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n: Z),
  forall (HW_3: (* File "all_zeros.c", line 7, characters 17-71 *)
                (mutable_n <= n /\
                (forall (i:Z),
                 (mutable_n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n0: Z),
  forall (HW_4: mutable_n0 = (mutable_n - 1)),
  forall (HW_5: mutable_n0 >= 0),
  forall (result: ((pointer) Z4)),
  forall (HW_6: result = (shift t mutable_n0)),
  forall (HW_7: (valid alloc result)),
  forall (result0: Z),
  forall (HW_8: result0 = (acc int_Z4 result)),
  forall (HW_12: result0 = 0),
  (* File "all_zeros.c", line 7, characters 17-71 *) (mutable_n0 <= n /\
  (forall (i:Z), (mutable_n0 <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0))) /\
  (Zwf 0 mutable_n0 mutable_n).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_impl_po_6 : 
  forall (t: ((pointer) Z4)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "all_zeros.c", line 4, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (HW_2: (* File "all_zeros.c", line 7, characters 17-71 *) (n <= n /\
                (forall (i:Z),
                 (n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n: Z),
  forall (HW_3: (* File "all_zeros.c", line 7, characters 17-71 *)
                (mutable_n <= n /\
                (forall (i:Z),
                 (mutable_n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n0: Z),
  forall (HW_4: mutable_n0 = (mutable_n - 1)),
  forall (HW_14: mutable_n0 < 0),
  (* File "all_zeros.c", line 5, characters 13-57 *)
  ((1 <> 0 <->
    (forall (i:Z), (0 <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma all_zeros_impl_po_7 : 
  forall (t: ((pointer) Z4)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "all_zeros.c", line 4, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (HW_2: (* File "all_zeros.c", line 7, characters 17-71 *) (n <= n /\
                (forall (i:Z),
                 (n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n: Z),
  forall (HW_3: (* File "all_zeros.c", line 7, characters 17-71 *)
                (mutable_n <= n /\
                (forall (i:Z),
                 (mutable_n <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))),
  forall (mutable_n0: Z),
  forall (HW_4: mutable_n0 = (mutable_n - 1)),
  forall (HW_13: mutable_n0 < 0),
  forall (HW_15: mutable_n0 >= 0),
  (* File "all_zeros.c", line 5, characters 13-57 *)
  ((0 <> 0 <->
    (forall (i:Z), (0 <= i /\ i < n -> (acc int_Z4 (shift t i)) = 0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

