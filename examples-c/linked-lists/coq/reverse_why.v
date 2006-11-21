(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export List.

(* should go in List *)
Lemma app_rev_cons :
 forall (A:Set) (l1 l2:list A) (x:A),
   app (rev l1) (cons x l2) = app (rev (cons x l1)) l2.
Proof.
intros; simpl.
rewrite app_ass; auto.
Qed.

Require Export reverse_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma rev_impl_po_1 : 
  forall (p0: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (tl_global: ((memory) ((pointer) global) global)),
  forall (HW_1: (* File "reverse.c", line 7, characters 14-25 *)
                (is_list tl_global alloc p0)),
  (well_founded length_order).
Proof.
unfold length_order; intuition.
apply (length_order_wf global). 
Qed.




(* Why obligation from file "reverse.c", line 14, characters 10-195: *)
(*Why goal*) Lemma rev_impl_po_2 : 
  forall (p0: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (tl_global: ((memory) ((pointer) global) global)),
  forall (HW_1: (* File "reverse.c", line 7, characters 14-25 *)
                (is_list tl_global alloc p0)),
  (* File "reverse.c", line 14, characters 9-194 *)
  (exists lp:plist,
   (exists lr:plist, (((llist tl_global alloc null lp) /\
    (llist tl_global alloc p0 lr)) /\ (disjoint lp lr)) /\
    (forall (l:plist),
     ((llist tl_global alloc p0 l) -> (app (rev lr) lp) = (rev l))))).
Proof.
exists nil.
inversion_clear HW_1.
exists x.
unfold is_list, app,nil; intuition.
constructor.
apply disjoint_nil2.
rewrite <- app_nil_end; auto.
rewrite (llist_function  H H0); auto.
Qed.



(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma rev_impl_po_3 : 
  forall (p0: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (tl_global: ((memory) ((pointer) global) global)),
  forall (HW_1: (* File "reverse.c", line 7, characters 14-25 *)
                (is_list tl_global alloc p0)),
  forall (HW_2: (* File "reverse.c", line 14, characters 9-194 *)
                (exists lp:plist,
                 (exists lr:plist, (((llist tl_global alloc null lp) /\
                  (llist tl_global alloc p0 lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl_global alloc p0 l) ->
                    (app (rev lr) lp) = (rev l)))))),
  forall (p: ((pointer) global)),
  forall (r: ((pointer) global)),
  forall (tl_global0: ((memory) ((pointer) global) global)),
  forall (HW_3: (* File "reverse.c", line 14, characters 9-194 *)
                (exists lp:plist,
                 (exists lr:plist, (((llist tl_global0 alloc p lp) /\
                  (llist tl_global0 alloc r lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl_global alloc p0 l) ->
                    (app (rev lr) lp) = (rev l)))))),
  forall (HW_4: ~(r = null)),
  (valid alloc r).
Proof.
intuition.
inversion_clear HW_3.
inversion_clear H.
intuition.
inversion H3; intuition.
Qed.



(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma rev_impl_po_4 : 
  forall (p0: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (tl_global: ((memory) ((pointer) global) global)),
  forall (HW_1: (* File "reverse.c", line 7, characters 14-25 *)
                (is_list tl_global alloc p0)),
  forall (HW_2: (* File "reverse.c", line 14, characters 9-194 *)
                (exists lp:plist,
                 (exists lr:plist, (((llist tl_global alloc null lp) /\
                  (llist tl_global alloc p0 lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl_global alloc p0 l) ->
                    (app (rev lr) lp) = (rev l)))))),
  forall (p: ((pointer) global)),
  forall (r: ((pointer) global)),
  forall (tl_global0: ((memory) ((pointer) global) global)),
  forall (HW_3: (* File "reverse.c", line 14, characters 9-194 *)
                (exists lp:plist,
                 (exists lr:plist, (((llist tl_global0 alloc p lp) /\
                  (llist tl_global0 alloc r lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl_global alloc p0 l) ->
                    (app (rev lr) lp) = (rev l)))))),
  forall (HW_4: ~(r = null)),
  forall (HW_5: (valid alloc r)),
  forall (result: ((pointer) global)),
  forall (HW_6: result = (acc tl_global0 r)),
  forall (r0: ((pointer) global)),
  forall (HW_7: r0 = result),
  forall (HW_8: (valid alloc r)),
  forall (tl_global1: ((memory) ((pointer) global) global)),
  forall (HW_9: tl_global1 = (upd tl_global0 r p)),
  forall (p1: ((pointer) global)),
  forall (HW_10: p1 = r),
  (* File "reverse.c", line 14, characters 9-194 *)
  (exists lp:plist,
   (exists lr:plist, (((llist tl_global1 alloc p1 lp) /\
    (llist tl_global1 alloc r0 lr)) /\ (disjoint lp lr)) /\
    (forall (l:plist),
     ((llist tl_global alloc p0 l) -> (app (rev lr) lp) = (rev l))))) /\
  (length_order (length tl_global1 alloc r0) (length tl_global0 alloc r)).
Proof.
intros; subst; intuition.
(* case 1 : preservation of loop invariant *)
elim HW_3; clear HW_3; intuition.
elim H; clear H; intuition.
inversion H3.
absurd (r = null); intuition.
exists (r :: x); exists l; subst; intuition.
(* subgoal 1.1 *)
unfold llist,lpath; apply Path_cons; intuition.
 rewrite acc_upd_eq; auto.
apply llist_pset_same; auto.
unfold disjoint,caduceus_lists.disjoint in H2; intuition.
apply (H7 r); auto.
auto with *.
(* subgoal 1.2 *)
unfold llist,lpath; apply llist_pset_same; auto.
apply llist_not_starting with alloc (acc tl_global0); auto.
(* subgoal 1.3 *)
unfold disjoint; apply disjoint_cons; auto.
apply llist_not_starting with alloc (acc tl_global0); auto.
(* subgoal 1.4 *)
unfold rev,app in *|-*; rewrite app_rev_cons.
apply H1; auto.
(* case 2 : variant decreases *)
unfold length_order, length.
exists alloc.
elim HW_3; clear HW_3; intuition.
elim H; clear H; intuition.
inversion H3; intuition.
exists l; exists x0; intuition.
apply llist_pset_same; auto.
apply llist_not_starting with alloc (acc tl_global0); auto.
rewrite <- H7; simpl; omega.
Qed.


(* Why obligation from file "reverse.c", line 8, characters 14-78: *)
(*Why goal*) Lemma rev_impl_po_5 : 
  forall (p0: ((pointer) global)),
  forall (alloc: alloc_table),
  forall (tl_global: ((memory) ((pointer) global) global)),
  forall (HW_1: (* File "reverse.c", line 7, characters 14-25 *)
                (is_list tl_global alloc p0)),
  forall (HW_2: (* File "reverse.c", line 14, characters 9-194 *)
                (exists lp:plist,
                 (exists lr:plist, (((llist tl_global alloc null lp) /\
                  (llist tl_global alloc p0 lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl_global alloc p0 l) ->
                    (app (rev lr) lp) = (rev l)))))),
  forall (p: ((pointer) global)),
  forall (r: ((pointer) global)),
  forall (tl_global0: ((memory) ((pointer) global) global)),
  forall (HW_3: (* File "reverse.c", line 14, characters 9-194 *)
                (exists lp:plist,
                 (exists lr:plist, (((llist tl_global0 alloc p lp) /\
                  (llist tl_global0 alloc r lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist tl_global alloc p0 l) ->
                    (app (rev lr) lp) = (rev l)))))),
  forall (HW_11: r = null),
  forall (l0: plist),
  forall (HW_12: (llist tl_global alloc p0 l0)),
  (* File "reverse.c", line 8, characters 13-77 *)
  (llist tl_global0 alloc p (rev l0)).
Proof.
intros; subst; intuition.
(* post-condition *)
elim HW_3; clear HW_3; intuition.
elim H; clear H; intuition.
inversion H3; clear H3; intuition.
subst.
rewrite <- H1; auto.
Qed.

