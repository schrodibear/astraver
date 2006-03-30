
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
  forall (A765:Set),
  forall (t: ((pointer) A765)),
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
  forall (A766:Set),
  forall (t: ((pointer) A766)),
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
  forall (A767:Set),
  forall (t: ((pointer) A767)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A767)),
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
  forall (A768:Set),
  forall (t: ((pointer) A768)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A768)),
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
  forall (result: ((pointer) A768)),
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
  forall (A769:Set),
  forall (t: ((pointer) A769)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A769)),
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
  forall (result: ((pointer) A769)),
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
  forall (A770:Set),
  forall (t: ((pointer) A770)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A770)),
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
  forall (result: ((pointer) A770)),
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
  forall (A771:Set),
  forall (t: ((pointer) A771)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A771)),
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
  forall (result: ((pointer) A771)),
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
  forall (A772:Set),
  forall (t: ((pointer) A772)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A772)),
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
  forall (result: ((pointer) A772)),
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
  forall (A773:Set),
  forall (t: ((pointer) A773)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A773)),
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
  forall (A774:Set),
  forall (t: ((pointer) A774)),
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
  forall (A775:Set),
  forall (t: ((pointer) A775)),
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
  forall (A776:Set),
  forall (t: ((pointer) A776)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A776)),
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
  forall (A777:Set),
  forall (t: ((pointer) A777)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A777)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A777)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A777)),
  forall (HW_7: result = (shift t i0)),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_5 : 
  forall (A778:Set),
  forall (t: ((pointer) A778)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A778)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A778)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A778)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A778)),
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
  forall (A779:Set),
  forall (t: ((pointer) A779)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A779)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A779)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A779)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A779)),
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
  forall (A780:Set),
  forall (t: ((pointer) A780)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A780)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A780)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A780)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A780)),
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
  forall (A781:Set),
  forall (t: ((pointer) A781)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A781)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A781)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_6: i0 < n),
  forall (result: ((pointer) A781)),
  forall (HW_7: result = (shift t i0)),
  forall (HW_8: (valid alloc result)),
  forall (result0: Z),
  forall (HW_9: result0 = (acc intM_t_8_0 result)),
  forall (intM_t_8_1: ((memory) Z A781)),
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
  forall (A782:Set),
  forall (t: ((pointer) A782)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A782)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A782)),
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
  forall (A783:Set),
  forall (t: ((pointer) A783)),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intM_t_8: ((memory) Z A783)),
  forall (HW_1: (* File "sum2.c", line 30, characters 14-33 *)
                (valid_range alloc t 0 n)),
  forall (i: Z),
  forall (HW_3: i = 0),
  forall (HW_4: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i /\
                i <= n) /\ (sum intM_t_8 alloc t 0 n) =
                ((sum intM_t_8 alloc t 0 n) + i))),
  forall (i0: Z),
  forall (intM_t_8_0: ((memory) Z A783)),
  forall (HW_5: (* File "sum2.c", line 37, characters 17-74 *) ((0 <= i0 /\
                i0 <= n) /\ (sum intM_t_8_0 alloc t 0 n) =
                ((sum intM_t_8_0 alloc t 0 n) + i0))),
  forall (HW_12: i0 >= n),
  (not_assigns alloc intM_t_8 intM_t_8_0 (pset_all (pset_singleton t))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

