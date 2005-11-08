(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export ref_glob_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (int_Z6: ((memory) Z Z6)),
  forall (x: ((pointer) Z6)),
  forall (HW_1: (valid_range alloc x 0 0)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_2: int_Z6_0 = (upd int_Z6 x 1)),
  (* File \"ref_glob.c\", line 13, characters 13-19:\n *) (acc int_Z6_0 x) =
  1 /\ (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton x)).
Proof.
intuition.
subst;auto.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z6: ((memory) Z Z6)),
  forall (x: ((pointer) Z6)),
  forall (HW_1: (valid_range alloc x 0 0)),
  forall (HW_3: (forall (int_Z6_0:((memory) Z Z6)),
                 (int_Z6_0 = (upd int_Z6 x 1) ->
                  (* File \"ref_glob.c\", line 13, characters 13-19:\n *)
                  (acc int_Z6_0 x) = 1 /\
                  (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton x))))),
  (valid alloc x).
Proof.
intuition;subst; caduceus.
red.
intros.
rewrite acc_upd_neq;auto.
generalize (pset_singleton_elim _ _ H0);auto.
Qed.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (int_Z6: ((memory) Z Z6)),
  forall (x: ((pointer) Z6)),
  forall (HW_1: (valid_range alloc x 0 0)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_2: (* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                (acc int_Z6_0 x) = 1 /\
                (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton x))),
  (* File \"ref_glob.c\", line 20, characters 13-19:\n *) (acc int_Z6_0 x) =
  1 /\ (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f2_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (int_Z6: ((memory) Z Z6)),
  forall (x: ((pointer) Z6)),
  forall (HW_1: (valid_range alloc x 0 0)),
  forall (HW_3: (forall (int_Z6_0:((memory) Z Z6)),
                 ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                  (acc int_Z6_0 x) = 1 /\
                  (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton x)) ->
                  (* File \"ref_glob.c\", line 20, characters 13-19:\n *)
                  (acc int_Z6_0 x) = 1 /\
                  (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton x))))),
  (* File \"ref_glob.c\", line 2, characters 14-23:\n *) (valid alloc x).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (c1_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (c2_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (int_Z6: ((memory) Z Z6)),
  forall (plas: ((pointer) Z10)),
  forall (HW_1: (* File \"ref_glob.c\", line 30, characters 14-26:\n *)
                (valid alloc plas)),
  forall (result: ((pointer) Z6)),
  forall (HW_2: result = (acc c2_Z10 plas)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_3: int_Z6_0 = (upd int_Z6 result 2)),
  forall (result0: ((pointer) Z6)),
  forall (HW_4: result0 = (acc c1_Z10 plas)),
  forall (int_Z6_1: ((memory) Z Z6)),
  forall (HW_5: (* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                (acc int_Z6_1 result0) = 1 /\
                (not_assigns alloc int_Z6_0 int_Z6_1 (pset_singleton result0))),
  forall (result1: ((pointer) Z6)),
  forall (HW_6: result1 = (acc c2_Z10 plas)),
  forall (int_Z6_2: ((memory) Z Z6)),
  forall (HW_7: (* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                (acc int_Z6_2 result1) = 1 /\
                (not_assigns alloc int_Z6_1 int_Z6_2 (pset_singleton result1))),
  (* File \"ref_glob.c\", line 32, characters 13-43:\n *)
  ((acc int_Z6_2 (acc c1_Z10 plas)) = 1 /\ (acc int_Z6_2 (acc c2_Z10 plas)) =
  1) /\
  (not_assigns alloc int_Z6 int_Z6_2
   (pset_union (pset_singleton (acc c2_Z10 plas))
    (pset_singleton (acc c1_Z10 plas)))).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (c1_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (c2_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (int_Z6: ((memory) Z Z6)),
  forall (plas: ((pointer) Z10)),
  forall (HW_1: (* File \"ref_glob.c\", line 30, characters 14-26:\n *)
                (valid alloc plas)),
  forall (result: ((pointer) Z6)),
  forall (HW_2: result = (acc c2_Z10 plas)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_3: int_Z6_0 = (upd int_Z6 result 2)),
  forall (result0: ((pointer) Z6)),
  forall (HW_4: result0 = (acc c1_Z10 plas)),
  forall (int_Z6_1: ((memory) Z Z6)),
  forall (HW_5: (* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                (acc int_Z6_1 result0) = 1 /\
                (not_assigns alloc int_Z6_0 int_Z6_1 (pset_singleton result0))),
  forall (result1: ((pointer) Z6)),
  forall (HW_6: result1 = (acc c2_Z10 plas)),
  forall (HW_8: (forall (int_Z6_0:((memory) Z Z6)),
                 ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                  (acc int_Z6_0 result1) = 1 /\
                  (not_assigns alloc int_Z6_1 int_Z6_0
                   (pset_singleton result1)) ->
                  (* File \"ref_glob.c\", line 32, characters 13-43:\n *)
                  ((acc int_Z6_0 (acc c1_Z10 plas)) = 1 /\
                  (acc int_Z6_0 (acc c2_Z10 plas)) = 1) /\
                  (not_assigns alloc int_Z6 int_Z6_0
                   (pset_union (pset_singleton (acc c2_Z10 plas))
                    (pset_singleton (acc c1_Z10 plas))))))),
  (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
  (valid alloc result1).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (c1_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (c2_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (int_Z6: ((memory) Z Z6)),
  forall (plas: ((pointer) Z10)),
  forall (HW_1: (* File \"ref_glob.c\", line 30, characters 14-26:\n *)
                (valid alloc plas)),
  forall (result: ((pointer) Z6)),
  forall (HW_2: result = (acc c2_Z10 plas)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_3: int_Z6_0 = (upd int_Z6 result 2)),
  forall (result0: ((pointer) Z6)),
  forall (HW_4: result0 = (acc c1_Z10 plas)),
  forall (int_Z6_1: ((memory) Z Z6)),
  forall (HW_5: (* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                (acc int_Z6_1 result0) = 1 /\
                (not_assigns alloc int_Z6_0 int_Z6_1 (pset_singleton result0))),
  forall (HW_9: (forall (result:((pointer) Z6)),
                 (result = (acc c2_Z10 plas) ->
                  (forall (int_Z6_0:((memory) Z Z6)),
                   ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                    (acc int_Z6_0 result) = 1 /\
                    (not_assigns alloc int_Z6_1 int_Z6_0
                     (pset_singleton result)) ->
                    (* File \"ref_glob.c\", line 32, characters 13-43:\n *)
                    ((acc int_Z6_0 (acc c1_Z10 plas)) = 1 /\
                    (acc int_Z6_0 (acc c2_Z10 plas)) = 1) /\
                    (not_assigns alloc int_Z6 int_Z6_0
                     (pset_union (pset_singleton (acc c2_Z10 plas))
                      (pset_singleton (acc c1_Z10 plas)))))) /\
                  (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                  (valid alloc result)))),
  (valid alloc plas).
Proof.
intuition.
subst.
rewrite H11;auto.
generalize (H2 plas alloc H).
intro.
apply pset_singleton_intro.
generalize (neq_base_addr_neq_shift (plas#c1) (plas#c2) 0 0 H4).
repeat rewrite shift_zero;auto.
subst;auto.
subst.
red.
intros.
rewrite H11;auto.
rewrite H8;auto.
rewrite acc_upd_neq;auto.
intro;subst.
generalize (pset_union_elim1 _  _ _  H6);auto.
apply not_not_in_pset_singleton.
generalize (pset_union_elim2 _  _ _  H6);auto.
generalize (pset_union_elim1 _ _ _ H6);auto.
subst;auto.
subst.
unfold valid1 in H5.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (c1_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (c2_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (int_Z6: ((memory) Z Z6)),
  forall (plas: ((pointer) Z10)),
  forall (HW_1: (* File \"ref_glob.c\", line 30, characters 14-26:\n *)
                (valid alloc plas)),
  forall (result: ((pointer) Z6)),
  forall (HW_2: result = (acc c2_Z10 plas)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_3: int_Z6_0 = (upd int_Z6 result 2)),
  forall (result0: ((pointer) Z6)),
  forall (HW_4: result0 = (acc c1_Z10 plas)),
  forall (HW_10: (forall (int_Z6_1:((memory) Z Z6)),
                  ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                   (acc int_Z6_1 result0) = 1 /\
                   (not_assigns alloc int_Z6_0 int_Z6_1
                    (pset_singleton result0)) ->
                   (forall (result:((pointer) Z6)),
                    (result = (acc c2_Z10 plas) ->
                     (forall (int_Z6_0:((memory) Z Z6)),
                      ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                       (acc int_Z6_0 result) = 1 /\
                       (not_assigns alloc int_Z6_1 int_Z6_0
                        (pset_singleton result)) ->
                       (* File \"ref_glob.c\", line 32, characters 13-43:\n *)
                       ((acc int_Z6_0 (acc c1_Z10 plas)) = 1 /\
                       (acc int_Z6_0 (acc c2_Z10 plas)) = 1) /\
                       (not_assigns alloc int_Z6 int_Z6_0
                        (pset_union (pset_singleton (acc c2_Z10 plas))
                         (pset_singleton (acc c1_Z10 plas)))))) /\
                     (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                     (valid alloc result))) /\
                   (valid alloc plas)))),
  (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
  (valid alloc result0).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (c1_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (c2_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (int_Z6: ((memory) Z Z6)),
  forall (plas: ((pointer) Z10)),
  forall (HW_1: (* File \"ref_glob.c\", line 30, characters 14-26:\n *)
                (valid alloc plas)),
  forall (result: ((pointer) Z6)),
  forall (HW_2: result = (acc c2_Z10 plas)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_3: int_Z6_0 = (upd int_Z6 result 2)),
  forall (HW_11: (forall (result:((pointer) Z6)),
                  (result = (acc c1_Z10 plas) ->
                   (forall (int_Z6_1:((memory) Z Z6)),
                    ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                     (acc int_Z6_1 result) = 1 /\
                     (not_assigns alloc int_Z6_0 int_Z6_1
                      (pset_singleton result)) ->
                     (forall (result:((pointer) Z6)),
                      (result = (acc c2_Z10 plas) ->
                       (forall (int_Z6_0:((memory) Z Z6)),
                        ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                         (acc int_Z6_0 result) = 1 /\
                         (not_assigns alloc int_Z6_1 int_Z6_0
                          (pset_singleton result)) ->
                         (* File \"ref_glob.c\", line 32, characters 13-43:\n *)
                         ((acc int_Z6_0 (acc c1_Z10 plas)) = 1 /\
                         (acc int_Z6_0 (acc c2_Z10 plas)) = 1) /\
                         (not_assigns alloc int_Z6 int_Z6_0
                          (pset_union (pset_singleton (acc c2_Z10 plas))
                           (pset_singleton (acc c1_Z10 plas)))))) /\
                       (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                       (valid alloc result))) /\
                     (valid alloc plas))) /\
                   (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                   (valid alloc result)))),
  (valid alloc plas).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (c1_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (c2_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (int_Z6: ((memory) Z Z6)),
  forall (plas: ((pointer) Z10)),
  forall (HW_1: (* File \"ref_glob.c\", line 30, characters 14-26:\n *)
                (valid alloc plas)),
  forall (result: ((pointer) Z6)),
  forall (HW_2: result = (acc c2_Z10 plas)),
  forall (HW_12: (forall (int_Z6_0:((memory) Z Z6)),
                  (int_Z6_0 = (upd int_Z6 result 2) ->
                   (forall (result:((pointer) Z6)),
                    (result = (acc c1_Z10 plas) ->
                     (forall (int_Z6_1:((memory) Z Z6)),
                      ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                       (acc int_Z6_1 result) = 1 /\
                       (not_assigns alloc int_Z6_0 int_Z6_1
                        (pset_singleton result)) ->
                       (forall (result:((pointer) Z6)),
                        (result = (acc c2_Z10 plas) ->
                         (forall (int_Z6_0:((memory) Z Z6)),
                          ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                           (acc int_Z6_0 result) = 1 /\
                           (not_assigns alloc int_Z6_1 int_Z6_0
                            (pset_singleton result)) ->
                           (* File \"ref_glob.c\", line 32, characters 13-43:\n *)
                           ((acc int_Z6_0 (acc c1_Z10 plas)) = 1 /\
                           (acc int_Z6_0 (acc c2_Z10 plas)) = 1) /\
                           (not_assigns alloc int_Z6 int_Z6_0
                            (pset_union (pset_singleton (acc c2_Z10 plas))
                             (pset_singleton (acc c1_Z10 plas)))))) /\
                         (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                         (valid alloc result))) /\
                       (valid alloc plas))) /\
                     (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                     (valid alloc result))) /\
                   (valid alloc plas)))),
  (valid alloc result).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f4_impl_po_7 : 
  forall (alloc: alloc_table),
  forall (c1_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (c2_Z10: ((memory) ((pointer) Z6) Z10)),
  forall (int_Z6: ((memory) Z Z6)),
  forall (plas: ((pointer) Z10)),
  forall (HW_1: (* File \"ref_glob.c\", line 30, characters 14-26:\n *)
                (valid alloc plas)),
  forall (HW_13: (forall (result:((pointer) Z6)),
                  (result = (acc c2_Z10 plas) ->
                   (forall (int_Z6_0:((memory) Z Z6)),
                    (int_Z6_0 = (upd int_Z6 result 2) ->
                     (forall (result:((pointer) Z6)),
                      (result = (acc c1_Z10 plas) ->
                       (forall (int_Z6_1:((memory) Z Z6)),
                        ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                         (acc int_Z6_1 result) = 1 /\
                         (not_assigns alloc int_Z6_0 int_Z6_1
                          (pset_singleton result)) ->
                         (forall (result:((pointer) Z6)),
                          (result = (acc c2_Z10 plas) ->
                           (forall (int_Z6_0:((memory) Z Z6)),
                            ((* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                             (acc int_Z6_0 result) = 1 /\
                             (not_assigns alloc int_Z6_1 int_Z6_0
                              (pset_singleton result)) ->
                             (* File \"ref_glob.c\", line 32, characters 13-43:\n *)
                             ((acc int_Z6_0 (acc c1_Z10 plas)) = 1 /\
                             (acc int_Z6_0 (acc c2_Z10 plas)) = 1) /\
                             (not_assigns alloc int_Z6 int_Z6_0
                              (pset_union (pset_singleton (acc c2_Z10 plas))
                               (pset_singleton (acc c1_Z10 plas)))))) /\
                           (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                           (valid alloc result))) /\
                         (valid alloc plas))) /\
                       (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                       (valid alloc result))) /\
                     (valid alloc plas))) /\
                   (valid alloc result)))),
  (valid alloc plas).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (p: ((pointer) Z6)),
  forall (alloc: alloc_table),
  forall (int_Z6: ((memory) Z Z6)),
  forall (HW_1: (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                (valid alloc p)),
  forall (int_Z6_0: ((memory) Z Z6)),
  forall (HW_2: int_Z6_0 = (upd int_Z6 p 1)),
  (* File \"ref_glob.c\", line 4, characters 13-20:\n *) (acc int_Z6_0 p) = 1 /\
  (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton p)).
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (p: ((pointer) Z6)),
  forall (alloc: alloc_table),
  forall (int_Z6: ((memory) Z Z6)),
  forall (HW_1: (* File \"ref_glob.c\", line 2, characters 14-23:\n *)
                (valid alloc p)),
  forall (HW_3: (forall (int_Z6_0:((memory) Z Z6)),
                 (int_Z6_0 = (upd int_Z6 p 1) ->
                  (* File \"ref_glob.c\", line 4, characters 13-20:\n *)
                  (acc int_Z6_0 p) = 1 /\
                  (not_assigns alloc int_Z6 int_Z6_0 (pset_singleton p))))),
  (valid alloc p).
Proof.
intuition.
subst; caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (p: ((pointer) Z13)),
  forall (alloc: alloc_table),
  forall (int_Z14: ((memory) Z Z14)),
  forall (int_Z14_Z13: ((memory) ((pointer) Z14) Z13)),
  forall (HW_1: (* File \"ref_glob.c\", line 45, characters 14-38:\n *)
                ((valid alloc p) /\ (valid alloc (acc int_Z14_Z13 p)))),
  forall (result: ((pointer) Z14)),
  forall (HW_2: result = (acc int_Z14_Z13 p)),
  forall (int_Z14_0: ((memory) Z Z14)),
  forall (HW_3: int_Z14_0 = (upd int_Z14 result 2)),
  (* File \"ref_glob.c\", line 47, characters 13-21:\n *)
  (acc int_Z14_0 (acc int_Z14_Z13 p)) = 2 /\
  (not_assigns alloc int_Z14 int_Z14_0 (pset_singleton (acc int_Z14_Z13 p))).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (p: ((pointer) Z13)),
  forall (alloc: alloc_table),
  forall (int_Z14: ((memory) Z Z14)),
  forall (int_Z14_Z13: ((memory) ((pointer) Z14) Z13)),
  forall (HW_1: (* File \"ref_glob.c\", line 45, characters 14-38:\n *)
                ((valid alloc p) /\ (valid alloc (acc int_Z14_Z13 p)))),
  forall (result: ((pointer) Z14)),
  forall (HW_2: result = (acc int_Z14_Z13 p)),
  forall (HW_4: (forall (int_Z14_0:((memory) Z Z14)),
                 (int_Z14_0 = (upd int_Z14 result 2) ->
                  (* File \"ref_glob.c\", line 47, characters 13-21:\n *)
                  (acc int_Z14_0 (acc int_Z14_Z13 p)) = 2 /\
                  (not_assigns alloc int_Z14 int_Z14_0
                   (pset_singleton (acc int_Z14_Z13 p)))))),
  (valid alloc result).
Proof.
intuition;subst;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_3 : 
  forall (p: ((pointer) Z13)),
  forall (alloc: alloc_table),
  forall (int_Z14: ((memory) Z Z14)),
  forall (int_Z14_Z13: ((memory) ((pointer) Z14) Z13)),
  forall (HW_1: (* File \"ref_glob.c\", line 45, characters 14-38:\n *)
                ((valid alloc p) /\ (valid alloc (acc int_Z14_Z13 p)))),
  forall (HW_5: (forall (result:((pointer) Z14)),
                 (result = (acc int_Z14_Z13 p) ->
                  (forall (int_Z14_0:((memory) Z Z14)),
                   (int_Z14_0 = (upd int_Z14 result 2) ->
                    (* File \"ref_glob.c\", line 47, characters 13-21:\n *)
                    (acc int_Z14_0 (acc int_Z14_Z13 p)) = 2 /\
                    (not_assigns alloc int_Z14 int_Z14_0
                     (pset_singleton (acc int_Z14_Z13 p))))) /\
                  (valid alloc result)))),
  (valid alloc p).
Proof.
intuition; subst; caduceus.
red;intros.
rewrite acc_upd_neq;auto.
generalize (pset_singleton_elim _ _ H2);auto.
Save.

