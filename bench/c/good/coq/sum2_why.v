
Require Import sum2_spec_why.


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

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_1 : 
  forall (A744:Set),
  forall (t: ((pointer) A744)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  0 <= i.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_2 : 
  forall (A745:Set),
  forall (t: ((pointer) A745)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  i <= n.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_3 : 
  forall (A746:Set),
  forall (t: ((pointer) A746)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A746)),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  0 = (sum intM_t_8 alloc t 0 i).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_4 : 
  forall (A747:Set),
  forall (t: ((pointer) A747)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A747)),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i /\
                i <= n) /\ 0 = (sum intM_t_8 alloc t 0 i))),
  forall (i0: Z),
  forall (s: Z),
  forall (HW_5: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i0 /\
                i0 <= n) /\ s = (sum intM_t_8 alloc t 0 i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A747)),
  forall (HW_7: result = (shift t i0)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_5 : 
  forall (A748:Set),
  forall (t: ((pointer) A748)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A748)),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i /\
                i <= n) /\ 0 = (sum intM_t_8 alloc t 0 i))),
  forall (i0: Z),
  forall (s: Z),
  forall (HW_5: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i0 /\
                i0 <= n) /\ s = (sum intM_t_8 alloc t 0 i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A748)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8 result)),
  forall (s0: Z),
  forall (HW_10: s0 = (s + result0)),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  0 <= i1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_6 : 
  forall (A749:Set),
  forall (t: ((pointer) A749)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A749)),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i /\
                i <= n) /\ 0 = (sum intM_t_8 alloc t 0 i))),
  forall (i0: Z),
  forall (s: Z),
  forall (HW_5: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i0 /\
                i0 <= n) /\ s = (sum intM_t_8 alloc t 0 i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A749)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8 result)),
  forall (s0: Z),
  forall (HW_10: s0 = (s + result0)),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  i1 <= n.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_7 : 
  forall (A750:Set),
  forall (t: ((pointer) A750)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A750)),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i /\
                i <= n) /\ 0 = (sum intM_t_8 alloc t 0 i))),
  forall (i0: Z),
  forall (s: Z),
  forall (HW_5: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i0 /\
                i0 <= n) /\ s = (sum intM_t_8 alloc t 0 i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A750)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8 result)),
  forall (s0: Z),
  forall (HW_10: s0 = (s + result0)),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  s0 = (sum intM_t_8 alloc t 0 i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_8 : 
  forall (A751:Set),
  forall (t: ((pointer) A751)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A751)),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i /\
                i <= n) /\ 0 = (sum intM_t_8 alloc t 0 i))),
  forall (i0: Z),
  forall (s: Z),
  forall (HW_5: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i0 /\
                i0 <= n) /\ s = (sum intM_t_8 alloc t 0 i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A751)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8 result)),
  forall (s0: Z),
  forall (HW_10: s0 = (s + result0)),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  (Zwf 0 (n - i1) (n - i0)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_9 : 
  forall (A752:Set),
  forall (t: ((pointer) A752)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A752)),
  forall (HW_1: (* File "sum2.c", line 14, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i /\
                i <= n) /\ 0 = (sum intM_t_8 alloc t 0 i))),
  forall (i0: Z),
  forall (s: Z),
  forall (HW_5: (* File "sum2.c", line 20, characters 17-47 *) ((0 <= i0 /\
                i0 <= n) /\ s = (sum intM_t_8 alloc t 0 i0))),
  forall (HW_12: i0 >= n),
  s = (sum intM_t_8 alloc t 0 n).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_1 : 
  forall (A753:Set),
  forall (t: ((pointer) A753)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  0 <= i.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_2 : 
  forall (A754:Set),
  forall (t: ((pointer) A754)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  i <= n.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_3 : 
  forall (A755:Set),
  forall (t: ((pointer) A755)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A755)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  (sum intM_t_8 alloc t 0 n) = ((sum intM_t_8 alloc t 0 n) + i).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_4 : 
  forall (A756:Set),
  forall (t: ((pointer) A756)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A756)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A756)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A756)),
  forall (HW_7: result = (shift t i0)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_5 : 
  forall (A757:Set),
  forall (t: ((pointer) A757)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A757)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A757)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A757)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A757)),
  forall (HW_10: intM_t_8_1 = (upd intM_t_8_0 result (result0 + 1))),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  0 <= i1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_6 : 
  forall (A758:Set),
  forall (t: ((pointer) A758)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A758)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A758)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A758)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A758)),
  forall (HW_10: intM_t_8_1 = (upd intM_t_8_0 result (result0 + 1))),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  i1 <= n.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_7 : 
  forall (A759:Set),
  forall (t: ((pointer) A759)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A759)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A759)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A759)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A759)),
  forall (HW_10: intM_t_8_1 = (upd intM_t_8_0 result (result0 + 1))),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  (sum intM_t_8_1 alloc t 0 n) = ((sum intM_t_8_1 alloc t 0 n) + i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_8 : 
  forall (A760:Set),
  forall (t: ((pointer) A760)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A760)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A760)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A760)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A760)),
  forall (HW_10: intM_t_8_1 = (upd intM_t_8_0 result (result0 + 1))),
  forall (i1: Z),
  forall (HW_11: i1 = (i0 + 1)),
  (Zwf 0 (n - i1) (n - i0)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_9 : 
  forall (A761:Set),
  forall (t: ((pointer) A761)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A761)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A761)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_12: i0 >= n),
  (* File "sum2.c", line 32, characters 13-45 *)
  (sum intM_t_8_0 alloc t 0 n) = ((sum intM_t_8_0 alloc t 0 n) + n).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_10 : 
  forall (A762:Set),
  forall (t: ((pointer) A762)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A762)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A762)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_12: i0 >= n),
  (not_assigns alloc intM_t_8 intM_t_8_0 (pset_all (pset_singleton t))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

