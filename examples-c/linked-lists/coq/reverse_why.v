(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_why.
Require Export LinkedLists.

(* Definition eq_list := (@eq (list pointer)). *)

(* Why obligation from file "why/reverse.why", characters 166-709 *)
Lemma rev_impl_po_1 : 
  forall (p0: pointer),
  forall (alloc: alloc),
  forall (tl: ((memory) pointer)),
  forall (Pre9: (is_list alloc tl p0)),
  forall (p: pointer),
  forall (Post6: p = p0),
  forall (r: pointer),
  forall (Post5: r = p),
  forall (p2: pointer),
  forall (Post1: p2 = null),
  (well_founded ll_order).
Proof.
intuition.
Save.

(* should go in PolyList *)
Lemma app_rev_cons :
 forall (A:Set) (l1 l2:list A) (x:A),
   app (rev l1) (cons x l2) = app (rev (cons x l1)) l2.
Proof.
intros; simpl.
rewrite app_ass; auto.
Qed.


(* Why obligation from file "why/reverse.why", characters 172-226 *)
Lemma rev_impl_po_2 : 
  forall (p0: pointer),
  forall (alloc: alloc),
  forall (tl: ((memory) pointer)),
  forall (Pre9: (is_list alloc tl p0)),
  forall (p: pointer),
  forall (Post6: p = p0),
  forall (r: pointer),
  forall (Post5: r = p),
  forall (p2: pointer),
  forall (Post1: p2 = null),
  forall (Variant1: StorePointerPair),
  forall (p3: pointer),
  forall (r1: pointer),
  forall (tl0: ((memory) pointer)),
  forall (Pre8: Variant1 = (store_pointer_pair alloc tl0 r1)),
  forall (Pre7: (exists lp:plist,
                 (exists lr:plist, (((llist alloc tl0 p3 lp) /\
                  (llist alloc tl0 r1 lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist alloc tl p0 l) -> (app (rev lr) lp) = (rev l)))))),
  forall (Test2: true = true),
  forall (caduceus_1: pointer),
  forall (Post2: caduceus_1 = r1),
  forall (result1: bool),
  forall (Post18: (if result1 then ~(caduceus_1 = null)
                   else caduceus_1 = null)),
  (if result1
   then (forall (result:pointer),
         (result = r1 ->
          (forall (r:pointer),
           (r = (acc tl0 r1) ->
            (forall (tl1:((memory) pointer)),
             (tl1 = (upd tl0 result p3) ->
              (forall (p:pointer),
               (p = result ->
                (exists lp:plist,
                 (exists lr:plist, (((llist alloc tl1 p lp) /\
                  (llist alloc tl1 r lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist alloc tl p0 l) -> (app (rev lr) lp) = (rev l))))) /\
                (ll_order (store_pointer_pair alloc tl1 r)
                 (store_pointer_pair alloc tl0 r1)))))) /\
            (valid alloc result))) /\
          (valid alloc r1)))
   else (exists l0:plist, (llist alloc tl0 p3 l0) /\
         (llist alloc tl p0 (rev l0)))).
Proof.
destruct result1; intuition.
elim Pre7; clear Pre7; intuition.
elim H3; clear H3; intuition.
inversion H7.
subst caduceus_1.
absurd (r1 = null); intuition.
exists (cons r1 x); exists l; subst; intuition.
unfold llist; apply Path_cons; intuition.
 rewrite acc_upd_eq; auto.
apply llist_pset_same; auto.
unfold disjoint in H6; intuition.
apply (H0 r1); auto.
auto with *.
apply llist_pset_same; auto.
apply llist_not_starting with alloc tl0; auto.
apply disjoint_cons.
auto.
apply llist_not_starting with alloc tl0; auto.
rewrite app_rev_cons.
apply H5; auto.
unfold ll_order, store_pointer_pair.
exists alloc.
elim Pre7; clear Pre7; intuition.
elim H3; clear H3; intuition.
subst.
inversion H7; intuition.
exists l; exists x0; intuition.
apply llist_pset_same; auto.
apply llist_not_starting with alloc tl0; auto.
rewrite <- H2; simpl; omega.
(* valid alloc result *)
subst.
elim Pre7; clear Pre7; intuition.
elim H; clear H; intuition.
inversion H3; auto.
absurd (r1=null); auto.
subst.
elim Pre7; clear Pre7; intuition.
elim H; clear H; intuition.
inversion H3; auto.
absurd (r1=null); auto.
subst.
elim Pre7; clear Pre7; intuition.
elim H; clear H; intuition.
elim (is_list_llist alloc tl p0 Pre9); intros l0 Hl0.
subst.
exists (rev l0); intuition.
assert (x0 = nil).
inversion_clear H3; intuition.
inversion_clear H. elim H3; auto.
subst x0.
generalize (H1 l0 Hl0); simpl; intro.
rewrite <- H; auto.
rewrite rev_involutive; auto.
Save.

(* Why obligation from file "why/reverse.why", characters 166-709 *)
Lemma rev_impl_po_3 : 
  forall (p0: pointer),
  forall (alloc: alloc),
  forall (tl: ((memory) pointer)),
  forall (Pre9: (is_list alloc tl p0)),
  forall (p: pointer),
  forall (Post6: p = p0),
  forall (r: pointer),
  forall (Post5: r = p),
  forall (p2: pointer),
  forall (Post1: p2 = null),
  forall (Variant1: StorePointerPair),
  forall (p3: pointer),
  forall (r1: pointer),
  forall (tl0: ((memory) pointer)),
  forall (Pre8: Variant1 = (store_pointer_pair alloc tl0 r1)),
  forall (Pre7: (exists lp:plist,
                 (exists lr:plist, (((llist alloc tl0 p3 lp) /\
                  (llist alloc tl0 r1 lr)) /\ (disjoint lp lr)) /\
                  (forall (l:plist),
                   ((llist alloc tl p0 l) -> (app (rev lr) lp) = (rev l)))))),
  forall (Test2: true = true),
  forall (p4: pointer),
  forall (r2: pointer),
  forall (tl1: ((memory) pointer)),
  forall (Post7: (exists lp:plist,
                  (exists lr:plist, (((llist alloc tl1 p4 lp) /\
                   (llist alloc tl1 r2 lr)) /\ (disjoint lp lr)) /\
                   (forall (l:plist),
                    ((llist alloc tl p0 l) -> (app (rev lr) lp) = (rev l))))) /\
                 (ll_order (store_pointer_pair alloc tl1 r2)
                  (store_pointer_pair alloc tl0 r1))),
  (ll_order (store_pointer_pair alloc tl1 r2) Variant1).
Proof.
intros; subst; intuition.
Save.

(* Why obligation from file "why/reverse.why", characters 256-538 *)
Lemma rev_impl_po_4 : 
  forall (p0: pointer),
  forall (alloc: alloc),
  forall (tl: ((memory) pointer)),
  forall (Pre9: (is_list alloc tl p0)),
  forall (p: pointer),
  forall (Post6: p = p0),
  forall (r: pointer),
  forall (Post5: r = p),
  forall (p2: pointer),
  forall (Post1: p2 = null),
  (exists lp:plist,
   (exists lr:plist, (((llist alloc tl p2 lp) /\ (llist alloc tl r lr)) /\
    (disjoint lp lr)) /\
    (forall (l:plist), ((llist alloc tl p0 l) -> (app (rev lr) lp) = (rev l))))).
Proof.
intros; subst.
exists (nil (A:=pointer)).
elim (is_list_llist alloc tl p0 Pre9); intros l Hl; exists l.
intuition.
rewrite (llist_function _ _ _ _ _ _ Hl H).
rewrite <- app_nil_end; auto.
Save.

