
Require Export assigns_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_1 : 
  forall (A735:Set),
  forall (p: ((pointer) A735)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (int_Z2: ((memory) Z A735)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  (not_assigns alloc int_Z2 int_Z2
   (pset_range (pset_singleton p) 0 (size - 1))) /\
  (* File "assigns.c", line 8, characters 7-64 *) ((0 <= size /\ size <=
  size) /\ p = (shift p (size - size))).
Proof.
intuition.
replace (size-size) with 0.
rewrite shift_zero.
auto.
omega.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_2 : 
  forall (A736:Set),
  forall (p: ((pointer) A736)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (int_Z2: ((memory) Z A736)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc int_Z2 int_Z2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (int_Z2_0: ((memory) Z A736)),
  forall (mutable_p: ((pointer) A736)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc int_Z2 int_Z2_0
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
(*Why goal*) Lemma erase_impl_po_3 : 
  forall (A737:Set),
  forall (p: ((pointer) A737)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (int_Z2: ((memory) Z A737)),
  forall (HW_1: (* File "assigns.c", line 4, characters 14-51 *) (size >=
                0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc int_Z2 int_Z2
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                size /\ size <= size) /\ p = (shift p (size - size)))),
  forall (int_Z2_0: ((memory) Z A737)),
  forall (mutable_p: ((pointer) A737)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc int_Z2 int_Z2_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File "assigns.c", line 8, characters 7-64 *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift p (size - mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_6: (valid alloc mutable_p)),
  forall (int_Z2_1: ((memory) Z A737)),
  forall (HW_7: int_Z2_1 = (upd int_Z2_0 mutable_p 0)),
  forall (result: ((pointer) A737)),
  forall (HW_8: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) A737)),
  forall (HW_9: mutable_p0 = result),
  ((not_assigns alloc int_Z2 int_Z2_1
    (pset_range (pset_singleton p) 0 (size - 1))) /\
  (* File "assigns.c", line 8, characters 7-64 *) ((0 <= mutable_size0 /\
  mutable_size0 <= size) /\ mutable_p0 = (shift p (size - mutable_size0)))) /\
  (Zwf 0 mutable_size0 mutable_size).
