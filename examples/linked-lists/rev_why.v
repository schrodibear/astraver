
Require Why.

Require LinkedLists.

(* Why obligation from file "rev.mlw", characters 1212-1684 *)
Lemma rev_po_1 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (EX l:plist | (list_of Ltl p0 l)))
  (result: pointer)
  (Post8: result = p0)
  (result0: pointer)
  (Post7: result0 = result)
  (p1: pointer)
  (Post1: p1 = null)
  (well_founded tl_order).
Proof.
Intros; Exact tl_order_wf.
Save.

(* Why obligation from file "rev.mlw", characters 1567-1675 *)
Lemma rev_po_2 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (EX l:plist | (list_of Ltl p0 l)))
  (result: pointer)
  (Post8: result = p0)
  (result0: pointer)
  (Post7: result0 = result)
  (p1: pointer)
  (Post1: p1 = null)
  (Variant1: Triple)
  (Ltl0: pointer_store)
  (p2: pointer)
  (r0: pointer)
  (Pre3: Variant1 = (triple Lhd Ltl0 r0))
  (Pre2: (EX lp:plist |
          (EX lr:plist | (list_of Ltl0 p2 lp) /\ (list_of Ltl0 r0 lr) /\
           (disjoint lp lr) /\
           ((l:plist) ((list_of Ltl0 p0 l) -> (app (rev lr) lp) = (rev l))))))
  (Test2: ~(r0 = null))
  (result3: pointer)
  (Post5: result3 = r0)
  (r1: pointer)
  (Post2: r1 = (access_pointer Ltl0 r0))
  (Ltl1: pointer_store)
  (Post3: Ltl1 = (update_pointer Ltl0 result3 p2))
  (p3: pointer)
  (Post4: p3 = result3)
  (EX lp:plist |
   (EX lr:plist | (list_of Ltl1 p3 lp) /\ (list_of Ltl1 r1 lr) /\
    (disjoint lp lr) /\
    ((l:plist) ((list_of Ltl1 p0 l) -> (app (rev lr) lp) = (rev l))))) /\
  (tl_order (triple Lhd Ltl1 r1) (triple Lhd Ltl0 r0)).
Proof.
Intuition.
Elim Pre2; Clear Pre2; Intuition.
Elim H; Clear H; Intuition.
Subst.
Inversion H.
Absurd r0=null; Intuition.
Exists (cons r0 x); Exists l; Subst; Intuition.
Apply List_of_cons; Intuition.
Unfold access_pointer; Unfold 2 update_pointer.
Rewrite pupdate_paccess_same; Auto.
Apply list_of_update_same; Auto.
Unfold disjoint in H1; Intuition.
Apply (H7 r0); Auto.
Rewrite <- H6; Auto with *.
Apply list_of_update_same; Auto.


Save.

(* Why obligation from file "rev.mlw", characters 1212-1684 *)
Lemma rev_po_3 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (EX l:plist | (list_of Ltl p0 l)))
  (result: pointer)
  (Post8: result = p0)
  (result0: pointer)
  (Post7: result0 = result)
  (p1: pointer)
  (Post1: p1 = null)
  (Variant1: Triple)
  (Ltl0: pointer_store)
  (p2: pointer)
  (r0: pointer)
  (Pre3: Variant1 = (triple Lhd Ltl0 r0))
  (Pre2: (EX lp:plist |
          (EX lr:plist | (list_of Ltl0 p2 lp) /\ (list_of Ltl0 r0 lr) /\
           (disjoint lp lr) /\
           ((l:plist) ((list_of Ltl0 p0 l) -> (app (rev lr) lp) = (rev l))))))
  (Test2: ~(r0 = null))
  (Ltl1: pointer_store)
  (p3: pointer)
  (r1: pointer)
  (Post9: (EX lp:plist |
           (EX lr:plist | (list_of Ltl1 p3 lp) /\ (list_of Ltl1 r1 lr) /\
            (disjoint lp lr) /\
            ((l:plist) ((list_of Ltl1 p0 l) -> (app (rev lr) lp) = (rev l))))) /\
          (tl_order (triple Lhd Ltl1 r1) (triple Lhd Ltl0 r0)))
  (tl_order (triple Lhd Ltl1 r1) Variant1).
Proof.
Destruct result3; Intuition.
Save.

(* Why obligation from file "rev.mlw", characters 1261-1485 *)
Lemma rev_po_4 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (EX l:plist | (list_of Ltl p0 l)))
  (result: pointer)
  (Post8: result = p0)
  (result0: pointer)
  (Post7: result0 = result)
  (p1: pointer)
  (Post1: p1 = null)
  (EX lp:plist |
   (EX lr:plist | (list_of Ltl p1 lp) /\ (list_of Ltl result0 lr) /\
    (disjoint lp lr) /\
    ((l:plist) ((list_of Ltl p0 l) -> (app (rev lr) lp) = (rev l))))).
Proof.
Intuition; Discriminate H3 Orelse Clear H3.
Subst.
Inversion H0; Subst; Intuition.
Apply List_cons; Intuition.
Unfold access_pointer update_pointer.
Rewrite pupdate_paccess_same.
Apply is_valid_update.
Save.


Proof.
Intuition.
Discriminate H1.
Discriminate H1.
Inversion Pre2.
Rewrite H in H0; Intuition.
Case (eq_null_dec p2); Intro.
Clear Post2; Subst p2; Auto.
Subst p2; Auto.
Unfold triple tl_order.
Inversion Pre2; Intuition.
Absurd p1=null; Auto.
Save.


(* Why obligation from file "rev.mlw", characters 1690-1692 *)
Lemma rev_po_5 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (EX l:plist | (list_of Ltl p0 l)))
  (result: pointer)
  (Post8: result = p0)
  (result0: pointer)
  (Post7: result0 = result)
  (p1: pointer)
  (Post1: p1 = null)
  (Ltl0: pointer_store)
  (p2: pointer)
  (r0: pointer)
  (Post6: (EX lp:plist |
           (EX lr:plist | (list_of Ltl0 p2 lp) /\ (list_of Ltl0 r0 lr) /\
            (disjoint lp lr) /\
            ((l:plist) ((list_of Ltl0 p0 l) -> (app (rev lr) lp) = (rev l))))) /\
          r0 = null)
  (EX l:plist | (list_of Ltl0 p2 l) /\
   ((l0:plist) ((list_of Ltl0 p0 l0) -> l = (rev l0)))).
Proof.
(* FILL PROOF HERE *)
Save.

