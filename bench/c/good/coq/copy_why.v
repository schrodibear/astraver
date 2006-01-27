(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export copy_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_1 : 
  forall (A765:Set), forall (A766:Set),
  forall (t1: ((pointer) A766)),
  forall (t2: ((pointer) A765)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A766)),
  forall (int_Z5: ((memory) Z A765)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
  (forall (k:Z),
   (n <= k /\ k < n -> (acc int_Z5 (shift t2 k)) = (acc int_Z4 (shift t1 k))))).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_2 : 
  forall (A767:Set), forall (A768:Set),
  forall (t1: ((pointer) A768)),
  forall (t2: ((pointer) A767)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A768)),
  forall (int_Z5: ((memory) Z A767)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_2: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc int_Z5 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i: Z),
  forall (int_Z5_0: ((memory) Z A767)),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc int_Z5_0 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_4: i0 = (i - 1)),
  forall (HW_5: i > 0),
  forall (result: ((pointer) A767)),
  forall (HW_6: result = (shift t2 i0)),
  forall (result0: ((pointer) A768)),
  forall (HW_7: result0 = (shift t1 i0)),
  (valid alloc result0).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_3 : 
  forall (A769:Set), forall (A770:Set),
  forall (t1: ((pointer) A770)),
  forall (t2: ((pointer) A769)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A770)),
  forall (int_Z5: ((memory) Z A769)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_2: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc int_Z5 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i: Z),
  forall (int_Z5_0: ((memory) Z A769)),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc int_Z5_0 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_4: i0 = (i - 1)),
  forall (HW_5: i > 0),
  forall (result: ((pointer) A769)),
  forall (HW_6: result = (shift t2 i0)),
  forall (result0: ((pointer) A770)),
  forall (HW_7: result0 = (shift t1 i0)),
  forall (HW_8: (valid alloc result0)),
  forall (result1: Z),
  forall (HW_9: result1 = (acc int_Z4 result0)),
  (valid alloc result).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_4 : 
  forall (A771:Set), forall (A772:Set),
  forall (t1: ((pointer) A772)),
  forall (t2: ((pointer) A771)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A772)),
  forall (int_Z5: ((memory) Z A771)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_2: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc int_Z5 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i: Z),
  forall (int_Z5_0: ((memory) Z A771)),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc int_Z5_0 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_4: i0 = (i - 1)),
  forall (HW_5: i > 0),
  forall (result: ((pointer) A771)),
  forall (HW_6: result = (shift t2 i0)),
  forall (result0: ((pointer) A772)),
  forall (HW_7: result0 = (shift t1 i0)),
  forall (HW_8: (valid alloc result0)),
  forall (result1: Z),
  forall (HW_9: result1 = (acc int_Z4 result0)),
  forall (HW_10: (valid alloc result)),
  forall (int_Z5_1: ((memory) Z A771)),
  forall (HW_11: int_Z5_1 = (upd int_Z5_0 result result1)),
  (* File "copy.c", line 9, characters 17-70 *) (i0 <= n /\
  (forall (k:Z),
   (i0 <= k /\ k < n -> (acc int_Z5_1 (shift t2 k)) =
    (acc int_Z4 (shift t1 k))))) /\
  (Zwf 0 i0 i).
Proof.
intuition.
subst.
assert (k=i-1 \/ i<=k). 
  omega. 
intuition; subst; caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma copy_impl_po_5 : 
  forall (A773:Set), forall (A774:Set),
  forall (t1: ((pointer) A774)),
  forall (t2: ((pointer) A773)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A774)),
  forall (int_Z5: ((memory) Z A773)),
  forall (HW_1: (* File "copy.c", line 4, characters 14-58 *)
                ((valid_range alloc t1 0 n) /\ (valid_range alloc t2 0 n))),
  forall (HW_2: (* File "copy.c", line 9, characters 17-70 *) (n <= n /\
                (forall (k:Z),
                 (n <= k /\ k < n -> (acc int_Z5 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i: Z),
  forall (int_Z5_0: ((memory) Z A773)),
  forall (HW_3: (* File "copy.c", line 9, characters 17-70 *) (i <= n /\
                (forall (k:Z),
                 (i <= k /\ k < n -> (acc int_Z5_0 (shift t2 k)) =
                  (acc int_Z4 (shift t1 k)))))),
  forall (i0: Z),
  forall (HW_4: i0 = (i - 1)),
  forall (HW_12: i <= 0),
  (* File "copy.c", line 5, characters 13-56 *)
  (forall (k:Z),
   (0 <= k /\ k < n -> (acc int_Z5_0 (shift t2 k)) =
    (acc int_Z4 (shift t1 k)))).
Proof.
intuition.
Save.

