
Require Export assigns_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_1 : 
  forall (A713:Set),
  forall (p: ((pointer) A713)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A713)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  (not_assigns alloc intM_p_2 intM_p_2
   (pset_range (pset_singleton p) 0 (size - 1))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_2 : 
  forall (A714:Set),
  forall (p: ((pointer) A714)),
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
  forall (A715:Set),
  forall (p: ((pointer) A715)),
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
  forall (A716:Set),
  forall (p: ((pointer) A716)),
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
  forall (A717:Set),
  forall (p: ((pointer) A717)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A717)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A717)),
  forall (mutable_p: ((pointer) A717)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
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
  forall (A718:Set),
  forall (p: ((pointer) A718)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A718)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A718)),
  forall (mutable_p: ((pointer) A718)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A718)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A718)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A718)),
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
  forall (A719:Set),
  forall (p: ((pointer) A719)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A719)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A719)),
  forall (mutable_p: ((pointer) A719)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A719)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A719)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A719)),
  forall (HW_9: mutable_p0 = result),
  0 <= mutable_size0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_8 : 
  forall (A720:Set),
  forall (p: ((pointer) A720)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A720)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A720)),
  forall (mutable_p: ((pointer) A720)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A720)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A720)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A720)),
  forall (HW_9: mutable_p0 = result),
  mutable_size0 <= size.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_9 : 
  forall (A721:Set),
  forall (p: ((pointer) A721)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A721)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A721)),
  forall (mutable_p: ((pointer) A721)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A721)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A721)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A721)),
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
  forall (A722:Set),
  forall (p: ((pointer) A722)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A722)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A722)),
  forall (mutable_p: ((pointer) A722)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc intM_p_2 intM_p_2_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (intM_p_2_1: ((memory) Z A722)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A722)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A722)),
  forall (HW_9: mutable_p0 = result),
  (Zwf 0 mutable_size0 mutable_size).
Proof.
intuition.
Save.

Proof.
intuition.
Save.

