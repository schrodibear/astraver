(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export copy_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_1 : 
  forall (A764:Set), forall (A765:Set),
  forall (t1: ((pointer) A765)),
  forall (t2: ((pointer) A764)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  n <= n.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_2 : 
  forall (A766:Set), forall (A767:Set),
  forall (t1: ((pointer) A767)),
  forall (t2: ((pointer) A766)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t1_4: ((memory) Z A767)),
  forall (intM_t2_5: ((memory) Z A766)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (k: Z),
  forall (HW_2: n <= k /\ k < n),
  (acc intM_t2_5 (shift t2 k)) = (acc intM_t1_4 (shift t1 k)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_3 : 
  forall (A768:Set), forall (A769:Set),
  forall (t1: ((pointer) A769)),
  forall (t2: ((pointer) A768)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t1_4: ((memory) Z A769)),
  forall (intM_t2_5: ((memory) Z A768)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc intM_t2_5 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i: Z),
  forall (intM_t2_5_0: ((memory) Z A768)),
  forall (HW_4: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc intM_t2_5_0 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_5: i0 = (i - 1)),
  forall (HW_6: i > 0),
  forall (result: ((pointer) A768)),
  forall (HW_7: result = (shift t2 i0)),
  forall (result0: ((pointer) A769)),
  forall (HW_8: result0 = (shift t1 i0)),
  (valid alloc result0).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_4 : 
  forall (A770:Set), forall (A771:Set),
  forall (t1: ((pointer) A771)),
  forall (t2: ((pointer) A770)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t1_4: ((memory) Z A771)),
  forall (intM_t2_5: ((memory) Z A770)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc intM_t2_5 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i: Z),
  forall (intM_t2_5_0: ((memory) Z A770)),
  forall (HW_4: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc intM_t2_5_0 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_5: i0 = (i - 1)),
  forall (HW_6: i > 0),
  forall (result: ((pointer) A770)),
  forall (HW_7: result = (shift t2 i0)),
  forall (result0: ((pointer) A771)),
  forall (HW_8: result0 = (shift t1 i0)),
  forall (HW_9: (valid alloc result0)),
  forall (result1: Z),
  forall (HW_10: result1 = (acc intM_t1_4 result0)),
  (valid alloc result).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_5 : 
  forall (A772:Set), forall (A773:Set),
  forall (t1: ((pointer) A773)),
  forall (t2: ((pointer) A772)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t1_4: ((memory) Z A773)),
  forall (intM_t2_5: ((memory) Z A772)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc intM_t2_5 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i: Z),
  forall (intM_t2_5_0: ((memory) Z A772)),
  forall (HW_4: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc intM_t2_5_0 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_5: i0 = (i - 1)),
  forall (HW_6: i > 0),
  forall (result: ((pointer) A772)),
  forall (HW_7: result = (shift t2 i0)),
  forall (result0: ((pointer) A773)),
  forall (HW_8: result0 = (shift t1 i0)),
  forall (HW_9: (valid alloc result0)),
  forall (result1: Z),
  forall (HW_10: result1 = (acc intM_t1_4 result0)),
  forall (HW_11: (valid alloc result)),
  forall (intM_t2_5_1: ((memory) Z A772)),
  forall (HW_12: intM_t2_5_1 = (upd intM_t2_5_0 result result1)),
  i0 <= n.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_6 : 
  forall (A774:Set), forall (A775:Set),
  forall (t1: ((pointer) A775)),
  forall (t2: ((pointer) A774)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t1_4: ((memory) Z A775)),
  forall (intM_t2_5: ((memory) Z A774)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc intM_t2_5 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i: Z),
  forall (intM_t2_5_0: ((memory) Z A774)),
  forall (HW_4: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc intM_t2_5_0 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_5: i0 = (i - 1)),
  forall (HW_6: i > 0),
  forall (result: ((pointer) A774)),
  forall (HW_7: result = (shift t2 i0)),
  forall (result0: ((pointer) A775)),
  forall (HW_8: result0 = (shift t1 i0)),
  forall (HW_9: (valid alloc result0)),
  forall (result1: Z),
  forall (HW_10: result1 = (acc intM_t1_4 result0)),
  forall (HW_11: (valid alloc result)),
  forall (intM_t2_5_1: ((memory) Z A774)),
  forall (HW_12: intM_t2_5_1 = (upd intM_t2_5_0 result result1)),
  forall (k: Z),
  forall (HW_13: i0 <= k /\ k < n),
  (acc intM_t2_5_1 (shift t2 k)) = (acc intM_t1_4 (shift t1 k)).
Proof.
intuition.
subst.
assert ((k = i-1)\/(k > i-1)) .
omega.
intuition.
subst.
rewrite acc_upd_eq;auto.
rewrite acc_upd_neq;auto.
apply H4.
auto with *.
apply neq_offset_neq_shift.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_7 : 
  forall (A776:Set), forall (A777:Set),
  forall (t1: ((pointer) A777)),
  forall (t2: ((pointer) A776)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t1_4: ((memory) Z A777)),
  forall (intM_t2_5: ((memory) Z A776)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc intM_t2_5 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i: Z),
  forall (intM_t2_5_0: ((memory) Z A776)),
  forall (HW_4: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc intM_t2_5_0 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_5: i0 = (i - 1)),
  forall (HW_6: i > 0),
  forall (result: ((pointer) A776)),
  forall (HW_7: result = (shift t2 i0)),
  forall (result0: ((pointer) A777)),
  forall (HW_8: result0 = (shift t1 i0)),
  forall (HW_9: (valid alloc result0)),
  forall (result1: Z),
  forall (HW_10: result1 = (acc intM_t1_4 result0)),
  forall (HW_11: (valid alloc result)),
  forall (intM_t2_5_1: ((memory) Z A776)),
  forall (HW_12: intM_t2_5_1 = (upd intM_t2_5_0 result result1)),
  (Zwf 0 i0 i).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_8 : 
  forall (A778:Set), forall (A779:Set),
  forall (t1: ((pointer) A779)),
  forall (t2: ((pointer) A778)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t1_4: ((memory) Z A779)),
  forall (intM_t2_5: ((memory) Z A778)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc intM_t2_5 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i: Z),
  forall (intM_t2_5_0: ((memory) Z A778)),
  forall (HW_4: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc intM_t2_5_0 (shift t2 k)) =
                  (acc intM_t1_4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_5: i0 = (i - 1)),
  forall (HW_14: i <= 0),
  forall (k: Z),
  forall (HW_15: 0 <= k /\ k < n),
  (acc intM_t2_5_0 (shift t2 k)) = (acc intM_t1_4 (shift t1 k)).
Proof.
intuition.
Save.

