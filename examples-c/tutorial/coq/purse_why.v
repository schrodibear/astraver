
(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export purse_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma credit0_impl_po_1 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 8, characters 14-36 *)
                ((purse_inv balance_global alloc p) /\ s >= 0)),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "purse.c", line 9, characters 14-64: *)
(*Why goal*) Lemma credit0_impl_po_2 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 8, characters 14-36 *)
                ((purse_inv balance_global alloc p) /\ s >= 0)),
  forall (HW_2: (valid alloc p)),
  forall (result: Z),
  forall (HW_3: result = (acc balance_global p)),
  forall (HW_4: (valid alloc p)),
  forall (balance_global0: (memory Z global)),
  forall (HW_5: balance_global0 = (upd balance_global p (result + s))),
  (* File "purse.c", line 9, characters 13-63 *)
  ((purse_inv balance_global0 alloc p) /\ (acc balance_global0 p) =
  ((acc balance_global p) + s)).
Proof.
unfold purse_inv; intuition; subst; caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma credit_impl_po_1 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc p) /\ s >= 0)),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma credit_impl_po_2 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc p) /\ s >= 0)),
  forall (HW_2: (valid alloc p)),
  forall (result: Z),
  forall (HW_3: result = (acc balance_global p)),
  forall (HW_4: (valid alloc p)),
  forall (balance_global0: (memory Z global)),
  forall (HW_5: balance_global0 = (upd balance_global p (result + s))),
  (* File "purse.c", line 38, characters 13-63 *)
  ((purse_inv balance_global0 alloc p) /\ (acc balance_global0 p) =
  ((acc balance_global p) + s)) /\
  (not_assigns alloc balance_global balance_global0 (pset_singleton p)).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
subst; caduceus.
unfold not_assigns; intuition.
rewrite acc_upd_neq; intuition.
subst; intuition.
apply (@pset_singleton_elim _ p0 p0); trivial.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test1_impl_po_1 : 
  forall (p1: (pointer global)),
  forall (p2: (pointer global)),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 53, characters 14-56 *)
                (((purse_inv balance_global alloc p1) /\
                (purse_inv balance_global alloc p2)) /\ ~(p1 = p2))),
  (valid alloc p1).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "purse.c", line 36, characters 15-37: *)
(*Why goal*) Lemma test1_impl_po_2 : 
  forall (p1: (pointer global)),
  forall (p2: (pointer global)),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 53, characters 14-56 *)
                (((purse_inv balance_global alloc p1) /\
                (purse_inv balance_global alloc p2)) /\ ~(p1 = p2))),
  forall (HW_2: (valid alloc p1)),
  forall (balance_global0: (memory Z global)),
  forall (HW_3: balance_global0 = (upd balance_global p1 0)),
  (* File "purse.c", line 36, characters 14-36 *)
  ((purse_inv balance_global0 alloc p2) /\ 100 >= 0).
Proof.
unfold purse_inv; intuition.
subst.
caduceus.
Save.

(* Why obligation from file "purse.c", line 54, characters 14-26: *)
(*Why goal*) Lemma test1_impl_po_3 : 
  forall (p1: (pointer global)),
  forall (p2: (pointer global)),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 53, characters 14-56 *)
                (((purse_inv balance_global alloc p1) /\
                (purse_inv balance_global alloc p2)) /\ ~(p1 = p2))),
  forall (HW_2: (valid alloc p1)),
  forall (balance_global0: (memory Z global)),
  forall (HW_3: balance_global0 = (upd balance_global p1 0)),
  forall (HW_4: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global0 alloc p2) /\ 100 >= 0)),
  forall (balance_global1: (memory Z global)),
  forall (HW_5: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global1 alloc p2) /\
                (acc balance_global1 p2) = ((acc balance_global0 p2) + 100)) /\
                (not_assigns alloc balance_global0 balance_global1
                 (pset_singleton p2))),
  forall (HW_6: (valid alloc p1)),
  forall (result: Z),
  forall (HW_7: result = (acc balance_global1 p1)),
  (* File "purse.c", line 54, characters 13-25 *) result = 0.
Proof.
unfold purse_inv; intuition.
unfold purse_inv; intuition.
subst result.
rewrite H8; intuition.
subst; caduceus.
Save.

(* Why obligation from file "purse.c", line 36, characters 15-37: *)
(*Why goal*) Lemma test2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (result: (pointer global)),
  forall (alloc0: alloc_table),
  forall (HW_1: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc result) /\
                (purse_inv balance_global alloc0 result)) /\
                (alloc_extends alloc alloc0)),
  forall (result0: (pointer global)),
  forall (alloc1: alloc_table),
  forall (HW_2: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc0 result0) /\
                (purse_inv balance_global alloc1 result0)) /\
                (alloc_extends alloc0 alloc1)),
  (* File "purse.c", line 36, characters 14-36 *)
  ((purse_inv balance_global alloc1 result) /\ 100 >= 0).
Proof.
intuition.
red.
red in H2.
intuition.
apply alloc_extends_valid with alloc0;auto.
Save.

(* Why obligation from file "purse.c", line 36, characters 15-37: *)
(*Why goal*) Lemma test2_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (result: (pointer global)),
  forall (alloc0: alloc_table),
  forall (HW_1: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc result) /\
                (purse_inv balance_global alloc0 result)) /\
                (alloc_extends alloc alloc0)),
  forall (result0: (pointer global)),
  forall (alloc1: alloc_table),
  forall (HW_2: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc0 result0) /\
                (purse_inv balance_global alloc1 result0)) /\
                (alloc_extends alloc0 alloc1)),
  forall (HW_3: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc1 result) /\ 100 >= 0)),
  forall (balance_global0: (memory Z global)),
  forall (HW_4: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global0 alloc1 result) /\
                (acc balance_global0 result) =
                ((acc balance_global result) + 100)) /\
                (not_assigns alloc1 balance_global balance_global0
                 (pset_singleton result))),
  (* File "purse.c", line 36, characters 14-36 *)
  ((purse_inv balance_global0 alloc1 result0) /\ 200 >= 0).
Proof.
unfold purse_inv; intuition.
rewrite H11; intuition.
apply pset_singleton_intro.
intuition;subst.
generalize (fresh_not_valid _ _ _ H7);intuition.
(* problem: need to know that p1 <> p2, which
   should be a consequence of
H1 : valid alloc p1
H0 : fresh alloc p2

but there is a bug: we cannot have 
H6 : valid alloc p2
which contradicts H0.
*)

Save.

(* Why obligation from file "purse.c", line 44, characters 15-51: *)
(*Why goal*) Lemma test2_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (result: (pointer global)),
  forall (alloc0: alloc_table),
  forall (HW_1: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc result) /\
                (purse_inv balance_global alloc0 result)) /\
                (alloc_extends alloc alloc0)),
  forall (result0: (pointer global)),
  forall (alloc1: alloc_table),
  forall (HW_2: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc0 result0) /\
                (purse_inv balance_global alloc1 result0)) /\
                (alloc_extends alloc0 alloc1)),
  forall (HW_3: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc1 result) /\ 100 >= 0)),
  forall (balance_global0: (memory Z global)),
  forall (HW_4: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global0 alloc1 result) /\
                (acc balance_global0 result) =
                ((acc balance_global result) + 100)) /\
                (not_assigns alloc1 balance_global balance_global0
                 (pset_singleton result))),
  forall (HW_5: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global0 alloc1 result0) /\ 200 >= 0)),
  forall (balance_global1: (memory Z global)),
  forall (HW_6: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global1 alloc1 result0) /\
                (acc balance_global1 result0) =
                ((acc balance_global0 result0) + 200)) /\
                (not_assigns alloc1 balance_global0 balance_global1
                 (pset_singleton result0))),
  (* File "purse.c", line 44, characters 14-50 *)
  ((purse_inv balance_global1 alloc1 result) /\ 0 <= 50 /\ 50 <=
  (acc balance_global1 result)).
Proof.
unfold purse_inv; intuition.
rewrite H18; intuition.
apply pset_singleton_intro.
intuition;subst.
generalize (fresh_not_valid _ _ _ H7);intuition.
(* again we need p1 <> p2 *)
rewrite H18;intuition.
apply pset_singleton_intro.
intuition;subst.
generalize (fresh_not_valid _ _ _ H7);intuition.
(* again we need p1 <> p2 *)
Save.

(* Why obligation from file "purse.c", line 44, characters 15-51: *)
(*Why goal*) Lemma test2_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (result: (pointer global)),
  forall (alloc0: alloc_table),
  forall (HW_1: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc result) /\
                (purse_inv balance_global alloc0 result)) /\
                (alloc_extends alloc alloc0)),
  forall (result0: (pointer global)),
  forall (alloc1: alloc_table),
  forall (HW_2: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc0 result0) /\
                (purse_inv balance_global alloc1 result0)) /\
                (alloc_extends alloc0 alloc1)),
  forall (HW_3: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc1 result) /\ 100 >= 0)),
  forall (balance_global0: (memory Z global)),
  forall (HW_4: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global0 alloc1 result) /\
                (acc balance_global0 result) =
                ((acc balance_global result) + 100)) /\
                (not_assigns alloc1 balance_global balance_global0
                 (pset_singleton result))),
  forall (HW_5: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global0 alloc1 result0) /\ 200 >= 0)),
  forall (balance_global1: (memory Z global)),
  forall (HW_6: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global1 alloc1 result0) /\
                (acc balance_global1 result0) =
                ((acc balance_global0 result0) + 200)) /\
                (not_assigns alloc1 balance_global0 balance_global1
                 (pset_singleton result0))),
  forall (HW_7: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global1 alloc1 result) /\ 0 <= 50 /\
                50 <= (acc balance_global1 result))),
  forall (balance_global2: (memory Z global)),
  forall (HW_8: (* File "purse.c", line 46, characters 13-63 *)
                ((purse_inv balance_global2 alloc1 result) /\
                (acc balance_global2 result) =
                ((acc balance_global1 result) - 50)) /\
                (not_assigns alloc1 balance_global1 balance_global2
                 (pset_singleton result))),
  (* File "purse.c", line 44, characters 14-50 *)
  ((purse_inv balance_global2 alloc1 result0) /\ 0 <= 100 /\ 100 <=
  (acc balance_global2 result0)).
Proof.
unfold purse_inv; intuition.
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (result: (pointer global)),
  forall (alloc0: alloc_table),
  forall (HW_1: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc result) /\
                (purse_inv balance_global alloc0 result)) /\
                (alloc_extends alloc alloc0)),
  forall (result0: (pointer global)),
  forall (alloc1: alloc_table),
  forall (HW_2: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc0 result0) /\
                (purse_inv balance_global alloc1 result0)) /\
                (alloc_extends alloc0 alloc1)),
  forall (HW_3: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc1 result) /\ 100 >= 0)),
  forall (balance_global0: (memory Z global)),
  forall (HW_4: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global0 alloc1 result) /\
                (acc balance_global0 result) =
                ((acc balance_global result) + 100)) /\
                (not_assigns alloc1 balance_global balance_global0
                 (pset_singleton result))),
  forall (HW_5: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global0 alloc1 result0) /\ 200 >= 0)),
  forall (balance_global1: (memory Z global)),
  forall (HW_6: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global1 alloc1 result0) /\
                (acc balance_global1 result0) =
                ((acc balance_global0 result0) + 200)) /\
                (not_assigns alloc1 balance_global0 balance_global1
                 (pset_singleton result0))),
  forall (HW_7: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global1 alloc1 result) /\ 0 <= 50 /\
                50 <= (acc balance_global1 result))),
  forall (balance_global2: (memory Z global)),
  forall (HW_8: (* File "purse.c", line 46, characters 13-63 *)
                ((purse_inv balance_global2 alloc1 result) /\
                (acc balance_global2 result) =
                ((acc balance_global1 result) - 50)) /\
                (not_assigns alloc1 balance_global1 balance_global2
                 (pset_singleton result))),
  forall (HW_9: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global2 alloc1 result0) /\ 0 <= 100 /\
                100 <= (acc balance_global2 result0))),
  forall (balance_global3: (memory Z global)),
  forall (HW_10: (* File "purse.c", line 46, characters 13-63 *)
                 ((purse_inv balance_global3 alloc1 result0) /\
                 (acc balance_global3 result0) =
                 ((acc balance_global2 result0) - 100)) /\
                 (not_assigns alloc1 balance_global2 balance_global3
                  (pset_singleton result0))),
  (valid alloc1 result).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (result: (pointer global)),
  forall (alloc0: alloc_table),
  forall (HW_1: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc result) /\
                (purse_inv balance_global alloc0 result)) /\
                (alloc_extends alloc alloc0)),
  forall (result0: (pointer global)),
  forall (alloc1: alloc_table),
  forall (HW_2: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc0 result0) /\
                (purse_inv balance_global alloc1 result0)) /\
                (alloc_extends alloc0 alloc1)),
  forall (HW_3: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc1 result) /\ 100 >= 0)),
  forall (balance_global0: (memory Z global)),
  forall (HW_4: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global0 alloc1 result) /\
                (acc balance_global0 result) =
                ((acc balance_global result) + 100)) /\
                (not_assigns alloc1 balance_global balance_global0
                 (pset_singleton result))),
  forall (HW_5: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global0 alloc1 result0) /\ 200 >= 0)),
  forall (balance_global1: (memory Z global)),
  forall (HW_6: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global1 alloc1 result0) /\
                (acc balance_global1 result0) =
                ((acc balance_global0 result0) + 200)) /\
                (not_assigns alloc1 balance_global0 balance_global1
                 (pset_singleton result0))),
  forall (HW_7: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global1 alloc1 result) /\ 0 <= 50 /\
                50 <= (acc balance_global1 result))),
  forall (balance_global2: (memory Z global)),
  forall (HW_8: (* File "purse.c", line 46, characters 13-63 *)
                ((purse_inv balance_global2 alloc1 result) /\
                (acc balance_global2 result) =
                ((acc balance_global1 result) - 50)) /\
                (not_assigns alloc1 balance_global1 balance_global2
                 (pset_singleton result))),
  forall (HW_9: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global2 alloc1 result0) /\ 0 <= 100 /\
                100 <= (acc balance_global2 result0))),
  forall (balance_global3: (memory Z global)),
  forall (HW_10: (* File "purse.c", line 46, characters 13-63 *)
                 ((purse_inv balance_global3 alloc1 result0) /\
                 (acc balance_global3 result0) =
                 ((acc balance_global2 result0) - 100)) /\
                 (not_assigns alloc1 balance_global2 balance_global3
                  (pset_singleton result0))),
  forall (HW_11: (valid alloc1 result)),
  forall (result1: Z),
  forall (HW_12: result1 = (acc balance_global3 result)),
  (valid alloc1 result0).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma test2_impl_po_7 : 
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (result: (pointer global)),
  forall (alloc0: alloc_table),
  forall (HW_1: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc result) /\
                (purse_inv balance_global alloc0 result)) /\
                (alloc_extends alloc alloc0)),
  forall (result0: (pointer global)),
  forall (alloc1: alloc_table),
  forall (HW_2: (* File "purse.c", line 65, characters 30-67 *)
                ((fresh alloc0 result0) /\
                (purse_inv balance_global alloc1 result0)) /\
                (alloc_extends alloc0 alloc1)),
  forall (HW_3: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global alloc1 result) /\ 100 >= 0)),
  forall (balance_global0: (memory Z global)),
  forall (HW_4: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global0 alloc1 result) /\
                (acc balance_global0 result) =
                ((acc balance_global result) + 100)) /\
                (not_assigns alloc1 balance_global balance_global0
                 (pset_singleton result))),
  forall (HW_5: (* File "purse.c", line 36, characters 14-36 *)
                ((purse_inv balance_global0 alloc1 result0) /\ 200 >= 0)),
  forall (balance_global1: (memory Z global)),
  forall (HW_6: (* File "purse.c", line 38, characters 13-63 *)
                ((purse_inv balance_global1 alloc1 result0) /\
                (acc balance_global1 result0) =
                ((acc balance_global0 result0) + 200)) /\
                (not_assigns alloc1 balance_global0 balance_global1
                 (pset_singleton result0))),
  forall (HW_7: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global1 alloc1 result) /\ 0 <= 50 /\
                50 <= (acc balance_global1 result))),
  forall (balance_global2: (memory Z global)),
  forall (HW_8: (* File "purse.c", line 46, characters 13-63 *)
                ((purse_inv balance_global2 alloc1 result) /\
                (acc balance_global2 result) =
                ((acc balance_global1 result) - 50)) /\
                (not_assigns alloc1 balance_global1 balance_global2
                 (pset_singleton result))),
  forall (HW_9: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global2 alloc1 result0) /\ 0 <= 100 /\
                100 <= (acc balance_global2 result0))),
  forall (balance_global3: (memory Z global)),
  forall (HW_10: (* File "purse.c", line 46, characters 13-63 *)
                 ((purse_inv balance_global3 alloc1 result0) /\
                 (acc balance_global3 result0) =
                 ((acc balance_global2 result0) - 100)) /\
                 (not_assigns alloc1 balance_global2 balance_global3
                  (pset_singleton result0))),
  forall (HW_11: (valid alloc1 result)),
  forall (result1: Z),
  forall (HW_12: result1 = (acc balance_global3 result)),
  forall (HW_13: (valid alloc1 result0)),
  forall (result2: Z),
  forall (HW_14: result2 = (acc balance_global3 result0)),
  (* File "purse.c", line 69, characters 13-27 *) (result1 + result2) = 150 /\
  (alloc_extends alloc alloc1).
Proof.
intuition.
subst.
assert (result0 <> result).
red in H2.
intuition;subst.
generalize (fresh_not_valid _ _ _ H6);intuition.
rewrite H27.
rewrite H25; intuition.
rewrite H23.
rewrite H19; intuition.
rewrite H17.
rewrite H13; intuition.
rewrite H12.
rewrite H8;intuition.
Admitted.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma withdraw0_impl_po_1 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 15, characters 14-50 *)
                ((purse_inv balance_global alloc p) /\ 0 <= s /\ s <=
                (acc balance_global p))),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "purse.c", line 16, characters 14-64: *)
(*Why goal*) Lemma withdraw0_impl_po_2 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 15, characters 14-50 *)
                ((purse_inv balance_global alloc p) /\ 0 <= s /\ s <=
                (acc balance_global p))),
  forall (HW_2: (valid alloc p)),
  forall (result: Z),
  forall (HW_3: result = (acc balance_global p)),
  forall (HW_4: (valid alloc p)),
  forall (balance_global0: (memory Z global)),
  forall (HW_5: balance_global0 = (upd balance_global p (result - s))),
  (* File "purse.c", line 16, characters 13-63 *)
  ((purse_inv balance_global0 alloc p) /\ (acc balance_global0 p) =
  ((acc balance_global p) - s)).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma withdraw_impl_po_1 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global alloc p) /\ 0 <= s /\ s <=
                (acc balance_global p))),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma withdraw_impl_po_2 : 
  forall (p: (pointer global)),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance_global: (memory Z global)),
  forall (HW_1: (* File "purse.c", line 44, characters 14-50 *)
                ((purse_inv balance_global alloc p) /\ 0 <= s /\ s <=
                (acc balance_global p))),
  forall (HW_2: (valid alloc p)),
  forall (result: Z),
  forall (HW_3: result = (acc balance_global p)),
  forall (HW_4: (valid alloc p)),
  forall (balance_global0: (memory Z global)),
  forall (HW_5: balance_global0 = (upd balance_global p (result - s))),
  (* File "purse.c", line 46, characters 13-63 *)
  ((purse_inv balance_global0 alloc p) /\ (acc balance_global0 p) =
  ((acc balance_global p) - s)) /\
  (not_assigns alloc balance_global balance_global0 (pset_singleton p)).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
(* needs a tactic to prove an assigns clause *)
Admitted.
