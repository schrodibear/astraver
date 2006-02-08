
Require Export assigns_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_1 : 
  forall (A752:Set),
  forall (p: ((pointer) A752)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A752)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  (not_assigns alloc intM_p_2 intM_p_2
   (pset_range (pset_singleton p) 0 (size - 1))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_2 : 
  forall (A753:Set),
  forall (p: ((pointer) A753)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  0 <= size.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_3 : 
  forall (A754:Set),
  forall (p: ((pointer) A754)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  size <= size.
Proof.
intuition.
Save.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_4 : 
  forall (A755:Set),
  forall (p: ((pointer) A755)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  p = (shift p (size - size)).
Proof.
intuition.
replace (size-size) with 0.
rewrite shift_zero;auto.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_5 : 
  forall (A756:Set),
  forall (p: ((pointer) A756)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A756)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A756)),
  forall (mutable_p: ((pointer) A756)),
  forall (mutable_size: Z),
  forall (HW_3: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  (valid alloc mutable_p).
Proof.
intuition.
subst mutable_p.
apply valid_range_valid_shift with 0 (size-1);auto.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_6 : 
  forall (A757:Set),
  forall (p: ((pointer) A757)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A757)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A757)),
  forall (mutable_p: ((pointer) A757)),
  forall (mutable_size: Z),
  forall (HW_3: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A757)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A757)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A757)),
  forall (HW_9: mutable_p0 = result),
  (not_assigns alloc intM_p_2 intM_p_2_1
   (pset_range (pset_singleton p) 0 (size - 1))).
Proof.
intuition.
red.
intros.
subst intM_p_2_1.
rewrite acc_upd_neq;auto.
subst mutable_p.
apply pset_range_elim with (pset_singleton p) 0 (size-1);auto.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_7 : 
  forall (A758:Set),
  forall (p: ((pointer) A758)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A758)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A758)),
  forall (mutable_p: ((pointer) A758)),
  forall (mutable_size: Z),
  forall (HW_3: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A758)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A758)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A758)),
  forall (HW_9: mutable_p0 = result),
  0 <= mutable_size0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_8 : 
  forall (A759:Set),
  forall (p: ((pointer) A759)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A759)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A759)),
  forall (mutable_p: ((pointer) A759)),
  forall (mutable_size: Z),
  forall (HW_3: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A759)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A759)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A759)),
  forall (HW_9: mutable_p0 = result),
  mutable_size0 <= size.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_9 : 
  forall (A760:Set),
  forall (p: ((pointer) A760)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A760)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A760)),
  forall (mutable_p: ((pointer) A760)),
  forall (mutable_size: Z),
  forall (HW_3: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A760)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A760)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A760)),
  forall (HW_9: mutable_p0 = result),
  mutable_p0 = (shift p (size - mutable_size0)).
Proof.
intuition.
subst mutable_p0.
subst result.
subst mutable_p.
rewrite shift_shift.
subst mutable_size0.
replace (size - (mutable_size - 1)) with (size - mutable_size + 1);auto.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_10 : 
  forall (A761:Set),
  forall (p: ((pointer) A761)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A761)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A761)),
  forall (mutable_p: ((pointer) A761)),
  forall (mutable_size: Z),
  forall (HW_3: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A761)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A761)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A761)),
  forall (HW_9: mutable_p0 = result),
  (Zwf 0 mutable_size0 mutable_size).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_11 : 
  forall (A762:Set),
  forall (p: ((pointer) A762)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A762)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A762)),
  forall (mutable_p: ((pointer) A762)),
  forall (mutable_size: Z),
  forall (HW_3: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_10: mutable_size = 0),
  (not_assigns alloc intM_p_2 intM_p_2_0
   (pset_range (pset_singleton p) 0 (size - 1))).
Proof.
intuition.
Save.

