
Require Why.

Require Export LinkedLists.

(* Why obligation from file "rev.mlw", characters 1173-1631 *)
Lemma rev_po_1 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (r: pointer)
  (Post7: r = p)
  (p2: pointer)
  (Post1: p2 = null)
  (well_founded ll_order).
Proof.
Auto.
Save.

(* should go in PolyList *)
Lemma app_rev_cons : 
  (A:Set)(l1,l2:(list A))(x:A)
  (app (rev l1) (cons x l2)) = (app (rev (cons x l1)) l2).
Proof.
Intros; Simpl.
Rewrite app_ass; Auto.
Save.


(* Why obligation from file "rev.mlw", characters 1534-1622 *)
Lemma rev_po_2 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (r: pointer)
  (Post7: r = p)
  (p2: pointer)
  (Post1: p2 = null)
  (Variant1: StorePointerPair)
  (Ltl0: pointer_store)
  (p3: pointer)
  (r1: pointer)
  (Pre3: Variant1 = (store_pointer_pair Ltl0 r1))
  (Pre2: (EX lp:plist |
          (EX lr:plist | (llist Ltl0 p3 lp) /\ (llist Ltl0 r1 lr) /\
           (disjoint lp lr) /\
           ((l:plist) ((llist Ltl p0 l) -> (app (rev lr) lp) = (rev l))))))
  (Test2: ~(r1 = null))
  (q: pointer)
  (Post5: q = r1)
  (r2: pointer)
  (Post2: r2 = (pget Ltl0 r1))
  (Ltl1: pointer_store)
  (Post3: Ltl1 = (pset Ltl0 q p3))
  (p4: pointer)
  (Post4: p4 = q)
  (EX lp:plist |
   (EX lr:plist | (llist Ltl1 p4 lp) /\ (llist Ltl1 r2 lr) /\
    (disjoint lp lr) /\
    ((l:plist) ((llist Ltl p0 l) -> (app (rev lr) lp) = (rev l))))) /\
  (ll_order (store_pointer_pair Ltl1 r2) (store_pointer_pair Ltl0 r1)).
Proof.
Intuition.
Elim Pre2; Clear Pre2; Intuition.
Elim H; Clear H; Intuition.
Subst.
Inversion H.
Absurd r1=null; Intuition.
Exists (cons r1 x); Exists l; Subst; Intuition.
Unfold llist; Apply Path_cons; Intuition.
Rewrite PointerStore.get_set_same; Auto.
Apply llist_pset_same; Auto.
Unfold disjoint in H1; Intuition.
Apply (H7 r1); Auto.
Rewrite <- H6; Auto with *.
Apply llist_pset_same; Auto.
Apply llist_not_starting with Ltl0; Auto.
Apply disjoint_cons.
Rewrite H6; Auto.
Apply llist_not_starting with Ltl0; Auto.
Rewrite app_rev_cons.
Rewrite H6; Apply H3; Auto.
Unfold ll_order store_pointer_pair.
Elim Pre2; Clear Pre2; Intuition.
Elim H; Clear H; Intuition.
Subst.
Inversion H; Intuition.
Exists l; Exists x0; Intuition.
Apply llist_pset_same; Auto.
Apply llist_not_starting with Ltl0; Auto.
Rewrite <- H6; Simpl; Omega.
Save.

(* Why obligation from file "rev.mlw", characters 1173-1631 *)
Lemma rev_po_3 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (r: pointer)
  (Post7: r = p)
  (p2: pointer)
  (Post1: p2 = null)
  (Variant1: StorePointerPair)
  (Ltl0: pointer_store)
  (p3: pointer)
  (r1: pointer)
  (Pre3: Variant1 = (store_pointer_pair Ltl0 r1))
  (Pre2: (EX lp:plist |
          (EX lr:plist | (llist Ltl0 p3 lp) /\ (llist Ltl0 r1 lr) /\
           (disjoint lp lr) /\
           ((l:plist) ((llist Ltl p0 l) -> (app (rev lr) lp) = (rev l))))))
  (Test2: ~(r1 = null))
  (Ltl1: pointer_store)
  (p4: pointer)
  (r2: pointer)
  (Post9: (EX lp:plist |
           (EX lr:plist | (llist Ltl1 p4 lp) /\ (llist Ltl1 r2 lr) /\
            (disjoint lp lr) /\
            ((l:plist) ((llist Ltl p0 l) -> (app (rev lr) lp) = (rev l))))) /\
          (ll_order (store_pointer_pair Ltl1 r2) (store_pointer_pair Ltl0 r1)))
  (ll_order (store_pointer_pair Ltl1 r2) Variant1).
Proof.
Intros; Subst Variant1; Intuition.
Save.

(* Why obligation from file "rev.mlw", characters 1222-1445 *)
Lemma rev_po_4 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (r: pointer)
  (Post7: r = p)
  (p2: pointer)
  (Post1: p2 = null)
  (EX lp:plist |
   (EX lr:plist | (llist Ltl p2 lp) /\ (llist Ltl r lr) /\
    (disjoint lp lr) /\
    ((l:plist) ((llist Ltl p0 l) -> (app (rev lr) lp) = (rev l))))).
Proof.
Intros; Subst.
Exists (nil pointer).
Elim (is_list_llist Ltl p0 Pre4); Intros l Hl; Exists l.
Intuition.
Rewrite (llist_function ? ? ? ? Hl H).
Intuition.
Save.

(* Why obligation from file "rev.mlw", characters 1637-1639 *)
Lemma rev_po_5 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (r: pointer)
  (Post7: r = p)
  (p2: pointer)
  (Post1: p2 = null)
  (Ltl0: pointer_store)
  (p3: pointer)
  (r1: pointer)
  (Post6: (EX lp:plist |
           (EX lr:plist | (llist Ltl0 p3 lp) /\ (llist Ltl0 r1 lr) /\
            (disjoint lp lr) /\
            ((l:plist) ((llist Ltl p0 l) -> (app (rev lr) lp) = (rev l))))) /\
          r1 = null)
  (EX l:plist | (llist Ltl0 p3 l) /\
   ((l0:plist) ((llist Ltl p0 l0) -> l = (rev l0)))).
Proof.
Intuition.
Elim H; Clear H; Intros lp H; Elim H; Clear H; Intro lr; Intuition.
Exists lp; Intuition.
Subst r1.
Inversion H.
Rewrite <- (H4 l0); Auto.
Rewrite <- H5; Trivial.
Subst.
Inversion H0.
Save.


