
Require Export assigns_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_1 : 
  forall (A734:Set),
  forall (p: ((pointer) A734)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A734)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  (not_assigns alloc intM_p_2 intM_p_2
   (pset_range (pset_singleton p) 0 (size - 1))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_2 : 
  forall (A735:Set),
  forall (p: ((pointer) A735)),
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
  forall (A736:Set),
  forall (p: ((pointer) A736)),
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
  forall (A737:Set),
  forall (p: ((pointer) A737)),
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
  forall (A738:Set),
  forall (p: ((pointer) A738)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A738)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A738)),
  forall (mutable_p: ((pointer) A738)),
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
  forall (A739:Set),
  forall (p: ((pointer) A739)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A739)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A739)),
  forall (mutable_p: ((pointer) A739)),
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
  forall (intM_p_2_1: ((memory) Z A739)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A739)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A739)),
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
  forall (A740:Set),
  forall (p: ((pointer) A740)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A740)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A740)),
  forall (mutable_p: ((pointer) A740)),
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
  forall (intM_p_2_1: ((memory) Z A740)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A740)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A740)),
  forall (HW_9: mutable_p0 = result),
  0 <= mutable_size0.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_8 : 
  forall (A741:Set),
  forall (p: ((pointer) A741)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A741)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A741)),
  forall (mutable_p: ((pointer) A741)),
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
  forall (intM_p_2_1: ((memory) Z A741)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A741)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A741)),
  forall (HW_9: mutable_p0 = result),
  mutable_size0 <= size.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_9 : 
  forall (A742:Set),
  forall (p: ((pointer) A742)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A742)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A742)),
  forall (mutable_p: ((pointer) A742)),
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
  forall (intM_p_2_1: ((memory) Z A742)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A742)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A742)),
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
  forall (A743:Set),
  forall (p: ((pointer) A743)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A743)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A743)),
  forall (mutable_p: ((pointer) A743)),
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
  forall (intM_p_2_1: ((memory) Z A743)),
  forall (HW_7: intM_p_2_1 = (upd intM_p_2_0 mutable_p 0)),
  forall (result: ((pointer) A743)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A743)),
  forall (HW_9: mutable_p0 = result),
  (Zwf 0 mutable_size0 mutable_size).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_11 : 
  forall (A744:Set),
  forall (p: ((pointer) A744)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (intM_p_2: ((memory) Z A744)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (alloc = alloc /\
                (not_assigns alloc intM_p_2 intM_p_2
                 (pset_range (pset_singleton p) 0 (size - 1)))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (intM_p_2_0: ((memory) Z A744)),
  forall (mutable_p: ((pointer) A744)),
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

