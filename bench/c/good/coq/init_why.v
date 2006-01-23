(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export init_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc int_Z5 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc int_Z1 (acc b_Z7 s)) = 1 /\
                (acc int_Z1 (shift (acc b_Z7 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (result: ((pointer) Z5)),
  forall (HW_2: result = (shift t 1)),
  (valid alloc result).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc int_Z5 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc int_Z1 (acc b_Z7 s)) = 1 /\
                (acc int_Z1 (shift (acc b_Z7 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (result: ((pointer) Z5)),
  forall (HW_2: result = (shift t 1)),
  forall (HW_3: (valid alloc result)),
  forall (result0: Z),
  forall (HW_4: result0 = (acc int_Z5 result)),
  (valid alloc s).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc int_Z5 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc int_Z1 (acc b_Z7 s)) = 1 /\
                (acc int_Z1 (shift (acc b_Z7 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (result: ((pointer) Z5)),
  forall (HW_2: result = (shift t 1)),
  forall (HW_3: (valid alloc result)),
  forall (result0: Z),
  forall (HW_4: result0 = (acc int_Z5 result)),
  forall (HW_5: (valid alloc s)),
  forall (result1: ((pointer) Z1)),
  forall (HW_6: result1 = (acc b_Z7 s)),
  (valid alloc result1).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc int_Z5 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc int_Z1 (acc b_Z7 s)) = 1 /\
                (acc int_Z1 (shift (acc b_Z7 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (result: ((pointer) Z5)),
  forall (HW_2: result = (shift t 1)),
  forall (HW_3: (valid alloc result)),
  forall (result0: Z),
  forall (HW_4: result0 = (acc int_Z5 result)),
  forall (HW_5: (valid alloc s)),
  forall (result1: ((pointer) Z1)),
  forall (HW_6: result1 = (acc b_Z7 s)),
  forall (HW_7: (valid alloc result1)),
  forall (result2: Z),
  forall (HW_8: result2 = (acc int_Z1 result1)),
  forall (HW_9: (valid alloc s)),
  forall (result3: ((pointer) Z1)),
  forall (HW_10: result3 = (acc b_Z7 s)),
  forall (result4: ((pointer) Z1)),
  forall (HW_11: result4 = (shift result3 2)),
  (valid alloc result4).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: ((* File "init.c", line 5, characters 25-34 *)
                 (acc int_Z5 (shift t 1)) = 2 /\
                (* File "init.c", line 13, characters 25-51 *)
                ((acc int_Z1 (acc b_Z7 s)) = 1 /\
                (acc int_Z1 (shift (acc b_Z7 s) 2)) = 4)) /\
                (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (result: ((pointer) Z5)),
  forall (HW_2: result = (shift t 1)),
  forall (HW_3: (valid alloc result)),
  forall (result0: Z),
  forall (HW_4: result0 = (acc int_Z5 result)),
  forall (HW_5: (valid alloc s)),
  forall (result1: ((pointer) Z1)),
  forall (HW_6: result1 = (acc b_Z7 s)),
  forall (HW_7: (valid alloc result1)),
  forall (result2: Z),
  forall (HW_8: result2 = (acc int_Z1 result1)),
  forall (HW_9: (valid alloc s)),
  forall (result3: ((pointer) Z1)),
  forall (HW_10: result3 = (acc b_Z7 s)),
  forall (result4: ((pointer) Z1)),
  forall (HW_11: result4 = (shift result3 2)),
  forall (HW_12: (valid alloc result4)),
  forall (result5: Z),
  forall (HW_13: result5 = (acc int_Z1 result4)),
  (* File "init.c", line 15, characters 13-25 *)
  (result0 + result2 + result5) = 7 /\
  (* File "init.c", line 5, characters 25-34 *) (acc int_Z5 (shift t 1)) = 2 /\
  (* File "init.c", line 13, characters 25-51 *) ((acc int_Z1 (acc b_Z7 s)) =
  1 /\ (acc int_Z1 (shift (acc b_Z7 s) 2)) = 4).
Proof.
intuition.
subst;auto.
unfold valid1_range in H6.
apply valid_range_valid_shift with 0 (3-1).
apply H6;auto.
omega.
Save.

Proof.
intuition.
subst;auto.
rewrite H0.
rewrite H4.
rewrite H1.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  2 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (A868:Set), forall (A869:Set), forall (A870:Set), forall (A871:Set),
  forall (A872:Set), forall (A873:Set), forall (A874:Set), forall (A875:Set),
  forall (alloc: alloc_table),
  forall (int_Z3: ((memory) Z A875)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  forall (HW_2: 2 >= 1),
  forall (result: ((pointer) A875)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 2 /\
                (valid_range alloc0 result 0 (2 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (int_Z3_0: ((memory) Z A875)),
  forall (HW_5: int_Z3_0 = (upd int_Z3 result 4)),
  forall (result0: ((pointer) A875)),
  forall (HW_6: result0 = (shift result 1)),
  (valid alloc0 result0).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_3 : 
  forall (A876:Set), forall (A877:Set), forall (A878:Set), forall (A879:Set),
  forall (A880:Set), forall (A881:Set), forall (A882:Set), forall (A883:Set),
  forall (alloc: alloc_table),
  forall (int_Z3: ((memory) Z A883)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  forall (HW_2: 2 >= 1),
  forall (result: ((pointer) A883)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 2 /\
                (valid_range alloc0 result 0 (2 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (int_Z3_0: ((memory) Z A883)),
  forall (HW_5: int_Z3_0 = (upd int_Z3 result 4)),
  forall (result0: ((pointer) A883)),
  forall (HW_6: result0 = (shift result 1)),
  forall (HW_7: (valid alloc0 result0)),
  forall (int_Z3_1: ((memory) Z A883)),
  forall (HW_8: int_Z3_1 = (upd int_Z3_0 result0 5)),
  forall (HW_9: (valid alloc0 result)),
  forall (result1: Z),
  forall (HW_10: result1 = (acc int_Z3_1 result)),
  (* File "init.c", line 22, characters 13-25 *) result1 = 4.
Proof.
intuition;subst.
subst;auto.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
subst;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_eq;auto.
replace (shift result 1 <> result) with (shift result 1 <> shift result 0).
apply neq_offset_neq_shift.
omega.
rewrite shift_zero.
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  3 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (A884:Set), forall (A885:Set), forall (A886:Set), forall (A887:Set),
  forall (A888:Set), forall (A889:Set), forall (A890:Set), forall (A891:Set),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A891)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) A891)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (int_Z4_0: ((memory) Z A891)),
  forall (HW_5: int_Z4_0 = (upd int_Z4 result 3)),
  forall (result0: ((pointer) A891)),
  forall (HW_6: result0 = (shift result 1)),
  (valid alloc0 result0).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_3 : 
  forall (A892:Set), forall (A893:Set), forall (A894:Set), forall (A895:Set),
  forall (A896:Set), forall (A897:Set), forall (A898:Set), forall (A899:Set),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A899)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) A899)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (int_Z4_0: ((memory) Z A899)),
  forall (HW_5: int_Z4_0 = (upd int_Z4 result 3)),
  forall (result0: ((pointer) A899)),
  forall (HW_6: result0 = (shift result 1)),
  forall (HW_7: (valid alloc0 result0)),
  forall (int_Z4_1: ((memory) Z A899)),
  forall (HW_8: int_Z4_1 = (upd int_Z4_0 result0 4)),
  forall (result1: ((pointer) A899)),
  forall (HW_9: result1 = (shift result 2)),
  (valid alloc0 result1).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_4 : 
  forall (A900:Set), forall (A901:Set), forall (A902:Set), forall (A903:Set),
  forall (A904:Set), forall (A905:Set), forall (A906:Set), forall (A907:Set),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A907)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) A907)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (int_Z4_0: ((memory) Z A907)),
  forall (HW_5: int_Z4_0 = (upd int_Z4 result 3)),
  forall (result0: ((pointer) A907)),
  forall (HW_6: result0 = (shift result 1)),
  forall (HW_7: (valid alloc0 result0)),
  forall (int_Z4_1: ((memory) Z A907)),
  forall (HW_8: int_Z4_1 = (upd int_Z4_0 result0 4)),
  forall (result1: ((pointer) A907)),
  forall (HW_9: result1 = (shift result 2)),
  forall (HW_10: (valid alloc0 result1)),
  forall (int_Z4_2: ((memory) Z A907)),
  forall (HW_11: int_Z4_2 = (upd int_Z4_1 result1 5)),
  forall (HW_12: (valid alloc0 result)),
  forall (result2: Z),
  forall (HW_13: result2 = (acc int_Z4_2 result)),
  forall (result3: ((pointer) A907)),
  forall (HW_14: result3 = (shift result 1)),
  (valid alloc0 result3).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_5 : 
  forall (A908:Set), forall (A909:Set), forall (A910:Set), forall (A911:Set),
  forall (A912:Set), forall (A913:Set), forall (A914:Set), forall (A915:Set),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A915)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) A915)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (int_Z4_0: ((memory) Z A915)),
  forall (HW_5: int_Z4_0 = (upd int_Z4 result 3)),
  forall (result0: ((pointer) A915)),
  forall (HW_6: result0 = (shift result 1)),
  forall (HW_7: (valid alloc0 result0)),
  forall (int_Z4_1: ((memory) Z A915)),
  forall (HW_8: int_Z4_1 = (upd int_Z4_0 result0 4)),
  forall (result1: ((pointer) A915)),
  forall (HW_9: result1 = (shift result 2)),
  forall (HW_10: (valid alloc0 result1)),
  forall (int_Z4_2: ((memory) Z A915)),
  forall (HW_11: int_Z4_2 = (upd int_Z4_1 result1 5)),
  forall (HW_12: (valid alloc0 result)),
  forall (result2: Z),
  forall (HW_13: result2 = (acc int_Z4_2 result)),
  forall (result3: ((pointer) A915)),
  forall (HW_14: result3 = (shift result 1)),
  forall (HW_15: (valid alloc0 result3)),
  forall (result4: Z),
  forall (HW_16: result4 = (acc int_Z4_2 result3)),
  forall (result5: ((pointer) A915)),
  forall (HW_17: result5 = (shift result 2)),
  (valid alloc0 result5).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_6 : 
  forall (A916:Set), forall (A917:Set), forall (A918:Set), forall (A919:Set),
  forall (A920:Set), forall (A921:Set), forall (A922:Set), forall (A923:Set),
  forall (alloc: alloc_table),
  forall (int_Z4: ((memory) Z A923)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) A923)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: (valid alloc0 result)),
  forall (int_Z4_0: ((memory) Z A923)),
  forall (HW_5: int_Z4_0 = (upd int_Z4 result 3)),
  forall (result0: ((pointer) A923)),
  forall (HW_6: result0 = (shift result 1)),
  forall (HW_7: (valid alloc0 result0)),
  forall (int_Z4_1: ((memory) Z A923)),
  forall (HW_8: int_Z4_1 = (upd int_Z4_0 result0 4)),
  forall (result1: ((pointer) A923)),
  forall (HW_9: result1 = (shift result 2)),
  forall (HW_10: (valid alloc0 result1)),
  forall (int_Z4_2: ((memory) Z A923)),
  forall (HW_11: int_Z4_2 = (upd int_Z4_1 result1 5)),
  forall (HW_12: (valid alloc0 result)),
  forall (result2: Z),
  forall (HW_13: result2 = (acc int_Z4_2 result)),
  forall (result3: ((pointer) A923)),
  forall (HW_14: result3 = (shift result 1)),
  forall (HW_15: (valid alloc0 result3)),
  forall (result4: Z),
  forall (HW_16: result4 = (acc int_Z4_2 result3)),
  forall (result5: ((pointer) A923)),
  forall (HW_17: result5 = (shift result 2)),
  forall (HW_18: (valid alloc0 result5)),
  forall (result6: Z),
  forall (HW_19: result6 = (acc int_Z4_2 result5)),
  (* File "init.c", line 30, characters 13-26 *)
  (result2 + result4 + result6) = 12.
Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst.
rewrite acc_upd_neq;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_eq;auto.
rewrite acc_upd_neq;auto.
rewrite acc_upd_eq;auto.
rewrite acc_upd_eq;auto.
apply neq_offset_neq_shift;omega.
replace (shift result 1 <> result) with (shift result 1 <> shift result 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
replace (shift result 2 <> result) with (shift result 2 <> shift result 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  (valid alloc t).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  forall (HW_3: (valid alloc t)),
  forall (int_Z5_0: ((memory) Z Z5)),
  forall (HW_4: int_Z5_0 = (upd int_Z5 t 1)),
  forall (result: ((pointer) Z5)),
  forall (HW_5: result = (shift t 1)),
  (valid alloc result).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  forall (HW_3: (valid alloc t)),
  forall (int_Z5_0: ((memory) Z Z5)),
  forall (HW_4: int_Z5_0 = (upd int_Z5 t 1)),
  forall (result: ((pointer) Z5)),
  forall (HW_5: result = (shift t 1)),
  forall (HW_6: (valid alloc result)),
  forall (int_Z5_1: ((memory) Z Z5)),
  forall (HW_7: int_Z5_1 = (upd int_Z5_0 result 2)),
  forall (result0: ((pointer) Z5)),
  forall (HW_8: result0 = (shift t 2)),
  (valid alloc result0).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  forall (HW_3: (valid alloc t)),
  forall (int_Z5_0: ((memory) Z Z5)),
  forall (HW_4: int_Z5_0 = (upd int_Z5 t 1)),
  forall (result: ((pointer) Z5)),
  forall (HW_5: result = (shift t 1)),
  forall (HW_6: (valid alloc result)),
  forall (int_Z5_1: ((memory) Z Z5)),
  forall (HW_7: int_Z5_1 = (upd int_Z5_0 result 2)),
  forall (result0: ((pointer) Z5)),
  forall (HW_8: result0 = (shift t 2)),
  forall (HW_9: (valid alloc result0)),
  forall (int_Z5_2: ((memory) Z Z5)),
  forall (HW_10: int_Z5_2 = (upd int_Z5_1 result0 3)),
  (valid alloc s).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_5 : 
  forall (a_Z7: ((memory) Z Z7)),
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  forall (HW_3: (valid alloc t)),
  forall (int_Z5_0: ((memory) Z Z5)),
  forall (HW_4: int_Z5_0 = (upd int_Z5 t 1)),
  forall (result: ((pointer) Z5)),
  forall (HW_5: result = (shift t 1)),
  forall (HW_6: (valid alloc result)),
  forall (int_Z5_1: ((memory) Z Z5)),
  forall (HW_7: int_Z5_1 = (upd int_Z5_0 result 2)),
  forall (result0: ((pointer) Z5)),
  forall (HW_8: result0 = (shift t 2)),
  forall (HW_9: (valid alloc result0)),
  forall (int_Z5_2: ((memory) Z Z5)),
  forall (HW_10: int_Z5_2 = (upd int_Z5_1 result0 3)),
  forall (HW_11: (valid alloc s)),
  forall (a_Z7_0: ((memory) Z Z7)),
  forall (HW_12: a_Z7_0 = (upd a_Z7 s 1)),
  forall (HW_13: (valid alloc s)),
  forall (result1: ((pointer) Z1)),
  forall (HW_14: result1 = (acc b_Z7 s)),
  (valid alloc result1).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_6 : 
  forall (a_Z7: ((memory) Z Z7)),
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  forall (HW_3: (valid alloc t)),
  forall (int_Z5_0: ((memory) Z Z5)),
  forall (HW_4: int_Z5_0 = (upd int_Z5 t 1)),
  forall (result: ((pointer) Z5)),
  forall (HW_5: result = (shift t 1)),
  forall (HW_6: (valid alloc result)),
  forall (int_Z5_1: ((memory) Z Z5)),
  forall (HW_7: int_Z5_1 = (upd int_Z5_0 result 2)),
  forall (result0: ((pointer) Z5)),
  forall (HW_8: result0 = (shift t 2)),
  forall (HW_9: (valid alloc result0)),
  forall (int_Z5_2: ((memory) Z Z5)),
  forall (HW_10: int_Z5_2 = (upd int_Z5_1 result0 3)),
  forall (HW_11: (valid alloc s)),
  forall (a_Z7_0: ((memory) Z Z7)),
  forall (HW_12: a_Z7_0 = (upd a_Z7 s 1)),
  forall (HW_13: (valid alloc s)),
  forall (result1: ((pointer) Z1)),
  forall (HW_14: result1 = (acc b_Z7 s)),
  forall (HW_15: (valid alloc result1)),
  forall (int_Z1_0: ((memory) Z Z1)),
  forall (HW_16: int_Z1_0 = (upd int_Z1 result1 1)),
  forall (HW_17: (valid alloc s)),
  forall (result2: ((pointer) Z1)),
  forall (HW_18: result2 = (acc b_Z7 s)),
  forall (result3: ((pointer) Z1)),
  forall (HW_19: result3 = (shift result2 1)),
  (valid alloc result3).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_7 : 
  forall (a_Z7: ((memory) Z Z7)),
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  forall (HW_3: (valid alloc t)),
  forall (int_Z5_0: ((memory) Z Z5)),
  forall (HW_4: int_Z5_0 = (upd int_Z5 t 1)),
  forall (result: ((pointer) Z5)),
  forall (HW_5: result = (shift t 1)),
  forall (HW_6: (valid alloc result)),
  forall (int_Z5_1: ((memory) Z Z5)),
  forall (HW_7: int_Z5_1 = (upd int_Z5_0 result 2)),
  forall (result0: ((pointer) Z5)),
  forall (HW_8: result0 = (shift t 2)),
  forall (HW_9: (valid alloc result0)),
  forall (int_Z5_2: ((memory) Z Z5)),
  forall (HW_10: int_Z5_2 = (upd int_Z5_1 result0 3)),
  forall (HW_11: (valid alloc s)),
  forall (a_Z7_0: ((memory) Z Z7)),
  forall (HW_12: a_Z7_0 = (upd a_Z7 s 1)),
  forall (HW_13: (valid alloc s)),
  forall (result1: ((pointer) Z1)),
  forall (HW_14: result1 = (acc b_Z7 s)),
  forall (HW_15: (valid alloc result1)),
  forall (int_Z1_0: ((memory) Z Z1)),
  forall (HW_16: int_Z1_0 = (upd int_Z1 result1 1)),
  forall (HW_17: (valid alloc s)),
  forall (result2: ((pointer) Z1)),
  forall (HW_18: result2 = (acc b_Z7 s)),
  forall (result3: ((pointer) Z1)),
  forall (HW_19: result3 = (shift result2 1)),
  forall (HW_20: (valid alloc result3)),
  forall (int_Z1_1: ((memory) Z Z1)),
  forall (HW_21: int_Z1_1 = (upd int_Z1_0 result3 3)),
  forall (HW_22: (valid alloc s)),
  forall (result4: ((pointer) Z1)),
  forall (HW_23: result4 = (acc b_Z7 s)),
  forall (result5: ((pointer) Z1)),
  forall (HW_24: result5 = (shift result4 2)),
  (valid alloc result5).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma invariants_initially_established_impl_po_8 : 
  forall (a_Z7: ((memory) Z Z7)),
  forall (alloc: alloc_table),
  forall (b_Z7: ((memory) ((pointer) Z1) Z7)),
  forall (int_Z1: ((memory) Z Z1)),
  forall (int_Z5: ((memory) Z Z5)),
  forall (s: ((pointer) Z7)),
  forall (t: ((pointer) Z5)),
  forall (HW_1: (valid_range alloc t 0 2) /\ (valid_range alloc s 0 0) /\
                (valid1 b_Z7) /\ (valid1_range b_Z7 3)),
  forall (x: Z),
  forall (HW_2: x = 45),
  forall (HW_3: (valid alloc t)),
  forall (int_Z5_0: ((memory) Z Z5)),
  forall (HW_4: int_Z5_0 = (upd int_Z5 t 1)),
  forall (result: ((pointer) Z5)),
  forall (HW_5: result = (shift t 1)),
  forall (HW_6: (valid alloc result)),
  forall (int_Z5_1: ((memory) Z Z5)),
  forall (HW_7: int_Z5_1 = (upd int_Z5_0 result 2)),
  forall (result0: ((pointer) Z5)),
  forall (HW_8: result0 = (shift t 2)),
  forall (HW_9: (valid alloc result0)),
  forall (int_Z5_2: ((memory) Z Z5)),
  forall (HW_10: int_Z5_2 = (upd int_Z5_1 result0 3)),
  forall (HW_11: (valid alloc s)),
  forall (a_Z7_0: ((memory) Z Z7)),
  forall (HW_12: a_Z7_0 = (upd a_Z7 s 1)),
  forall (HW_13: (valid alloc s)),
  forall (result1: ((pointer) Z1)),
  forall (HW_14: result1 = (acc b_Z7 s)),
  forall (HW_15: (valid alloc result1)),
  forall (int_Z1_0: ((memory) Z Z1)),
  forall (HW_16: int_Z1_0 = (upd int_Z1 result1 1)),
  forall (HW_17: (valid alloc s)),
  forall (result2: ((pointer) Z1)),
  forall (HW_18: result2 = (acc b_Z7 s)),
  forall (result3: ((pointer) Z1)),
  forall (HW_19: result3 = (shift result2 1)),
  forall (HW_20: (valid alloc result3)),
  forall (int_Z1_1: ((memory) Z Z1)),
  forall (HW_21: int_Z1_1 = (upd int_Z1_0 result3 3)),
  forall (HW_22: (valid alloc s)),
  forall (result4: ((pointer) Z1)),
  forall (HW_23: result4 = (acc b_Z7 s)),
  forall (result5: ((pointer) Z1)),
  forall (HW_24: result5 = (shift result4 2)),
  forall (HW_25: (valid alloc result5)),
  forall (int_Z1_2: ((memory) Z Z1)),
  forall (HW_26: int_Z1_2 = (upd int_Z1_1 result5 4)),
  (* File "init.c", line 5, characters 25-34 *) ((acc int_Z5_2 (shift t 1)) =
  2 /\ (acc int_Z1_2 (acc b_Z7 s)) = 1 /\
  (acc int_Z1_2 (shift (acc b_Z7 s) 2)) = 4).
Proof.
intuition.
subst;auto.
apply valid_range_valid_shift with 0 (3-1).
apply H3;auto.
omega.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
subst;auto.
apply valid_range_valid_shift with 0 (3-1).
apply H3;auto.
omega.
Save.

Proof.
intuition;subst;auto.
rewrite acc_upd_neq.
rewrite acc_upd_eq;auto.
apply neq_offset_neq_shift;omega.
rewrite acc_upd_neq.
rewrite acc_upd_neq.
rewrite acc_upd_eq;auto.
replace (shift (s # b_Z7) 1 <> s # b_Z7) with (shift (s # b_Z7) 1 <> shift (s # b_Z7) 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
replace (shift (s # b_Z7) 2 <> s # b_Z7) with (shift (s # b_Z7) 2 <> shift (s # b_Z7) 0).
apply neq_offset_neq_shift;omega.
rewrite shift_zero;auto.
rewrite acc_upd_eq;auto.
Save.
