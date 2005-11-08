(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export assigns_spec_why.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_1 : 
  forall (p: ((pointer) Z1)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (int_Z1: ((memory) Z Z1)),
  forall (HW_1: (* File \"assigns.c\", line 4, characters 14-51:\n *)
                (size >= 0 /\ (valid_range alloc p 0 (size - 1)))),
  (not_assigns alloc int_Z1 int_Z1
   (pset_range (pset_singleton p) 0 (size - 1))) /\
  (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <= size /\ size <=
  size) /\ p = (shift (shift p size) (Zopp size))).
Proof.
intuition; subst; auto.
apply not_assigns_trans with intP0; auto.
rewrite shift_shift; red; intuition.
rewrite acc_upd_neq; auto.
assert (shift p (size + - mutable_size1)<> p0).
apply pset_range_elim with (pset_singleton p) 0 (size-1); auto with *.
auto with *.

autorewrite with caduceus.
replace  (- (mutable_size1 - 1)) with (-mutable_size1+1); auto with *.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_2 : 
  forall (p: ((pointer) Z1)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (int_Z1: ((memory) Z Z1)),
  forall (HW_1: (* File \"assigns.c\", line 4, characters 14-51:\n *)
                (size >= 0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc int_Z1 int_Z1
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <=
                size /\ size <= size) /\
                p = (shift (shift p size) (Zopp size)))),
  forall (int_Z1_0: ((memory) Z Z1)),
  forall (mutable_p: ((pointer) Z1)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc int_Z1 int_Z1_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift (shift p size) (Zopp mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (int_Z1_1: ((memory) Z Z1)),
  forall (HW_6: int_Z1_1 = (upd int_Z1_0 mutable_p 0)),
  forall (result: ((pointer) Z1)),
  forall (HW_7: result = (shift mutable_p 1)),
  forall (mutable_p0: ((pointer) Z1)),
  forall (HW_8: mutable_p0 = result),
  ((not_assigns alloc int_Z1 int_Z1_1
    (pset_range (pset_singleton p) 0 (size - 1))) /\
  (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <=
  mutable_size0 /\ mutable_size0 <= size) /\
  mutable_p0 = (shift (shift p size) (Zopp mutable_size0)))) /\
  (Zwf 0 mutable_size0 mutable_size).
Proof.
intuition.
subst; autorewrite with caduceus.
replace (size + - size) with 0; auto with *.
autorewrite with caduceus; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_3 : 
  forall (p: ((pointer) Z1)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (int_Z1: ((memory) Z Z1)),
  forall (HW_1: (* File \"assigns.c\", line 4, characters 14-51:\n *)
                (size >= 0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc int_Z1 int_Z1
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <=
                size /\ size <= size) /\
                p = (shift (shift p size) (Zopp size)))),
  forall (int_Z1_0: ((memory) Z Z1)),
  forall (mutable_p: ((pointer) Z1)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc int_Z1 int_Z1_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift (shift p size) (Zopp mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_5: mutable_size <> 0),
  forall (HW_9: (forall (int_Z1_1:((memory) Z Z1)),
                 (int_Z1_1 = (upd int_Z1_0 mutable_p 0) ->
                  (forall (result:((pointer) Z1)),
                   (result = (shift mutable_p 1) ->
                    (forall (mutable_p:((pointer) Z1)),
                     (mutable_p = result ->
                      ((not_assigns alloc int_Z1 int_Z1_1
                        (pset_range (pset_singleton p) 0 (size - 1))) /\
                      (* File \"assigns.c\", line 8, characters 7-62:\n *)
                      ((0 <= mutable_size0 /\ mutable_size0 <= size) /\
                      mutable_p = (shift (shift p size) (Zopp mutable_size0)))) /\
                      (Zwf 0 mutable_size0 mutable_size)))))))),
  (valid alloc mutable_p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma erase_impl_po_4 : 
  forall (p: ((pointer) Z1)),
  forall (size: Z),
  forall (alloc: alloc_table),
  forall (int_Z1: ((memory) Z Z1)),
  forall (HW_1: (* File \"assigns.c\", line 4, characters 14-51:\n *)
                (size >= 0 /\ (valid_range alloc p 0 (size - 1)))),
  forall (HW_2: (not_assigns alloc int_Z1 int_Z1
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <=
                size /\ size <= size) /\
                p = (shift (shift p size) (Zopp size)))),
  forall (int_Z1_0: ((memory) Z Z1)),
  forall (mutable_p: ((pointer) Z1)),
  forall (mutable_size: Z),
  forall (HW_3: (not_assigns alloc int_Z1 int_Z1_0
                 (pset_range (pset_singleton p) 0 (size - 1))) /\
                (* File \"assigns.c\", line 8, characters 7-62:\n *) ((0 <=
                mutable_size /\ mutable_size <= size) /\
                mutable_p = (shift (shift p size) (Zopp mutable_size)))),
  forall (mutable_size0: Z),
  forall (HW_4: mutable_size0 = (mutable_size - 1)),
  forall (HW_10: mutable_size = 0),
  (not_assigns alloc int_Z1 int_Z1_0
   (pset_range (pset_singleton p) 0 (size - 1))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

