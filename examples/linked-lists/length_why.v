
Require Why.

Require LinkedLists.

(* Why obligation from file "length.mlw", characters 1072-1241 *)
Lemma length_po_1 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (is_list Lhd Ltl p0))
  (result: pointer)
  (Post8: result = p0)
  (result0: Z)
  (Post7: result0 = `0`)
  (well_founded tl_order).
Proof.
Intros; Exact tl_order_wf.
Save.

(* Why obligation from file "length.mlw", characters 1078-1094 *)
Lemma length_po_2 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (is_list Lhd Ltl p0))
  (result: pointer)
  (Post8: result = p0)
  (result0: Z)
  (Post7: result0 = `0`)
  (Variant1: Triple)
  (p1: pointer)
  (Pre3: Variant1 = (triple Lhd Ltl p1))
  (Pre2: (is_list Lhd Ltl p1))
  (Test2: p1 = null)
  (result2: bool)
  (Post3: result2 = false)
  (if result2 then p1 = null /\ true = false \/ ~(p1 = null) /\ true = true
   else p1 = null /\ false = false \/ ~(p1 = null) /\ false = true).
Proof.
Destruct result2; Intuition.
Save.

(* Why obligation from file "length.mlw", characters 1078-1094 *)
Lemma length_po_3 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (is_list Lhd Ltl p0))
  (result: pointer)
  (Post8: result = p0)
  (result0: Z)
  (Post7: result0 = `0`)
  (Variant1: Triple)
  (p1: pointer)
  (Pre3: Variant1 = (triple Lhd Ltl p1))
  (Pre2: (is_list Lhd Ltl p1))
  (Test1: ~(p1 = null))
  (result2: bool)
  (Post4: result2 = true)
  (if result2 then p1 = null /\ true = false \/ ~(p1 = null) /\ true = true
   else p1 = null /\ false = false \/ ~(p1 = null) /\ false = true).
Proof.
Destruct result2; Intuition.
Save.

(* Why obligation from file "length.mlw", characters 1072-1241 *)
Lemma length_po_4 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (is_list Lhd Ltl p0))
  (result: pointer)
  (Post8: result = p0)
  (result0: Z)
  (Post7: result0 = `0`)
  (Variant1: Triple)
  (n0: Z)
  (p1: pointer)
  (Pre3: Variant1 = (triple Lhd Ltl p1))
  (Pre2: (is_list Lhd Ltl p1))
  (Test4: p1 = null /\ true = false \/ ~(p1 = null) /\ true = true)
  (n1: Z)
  (Post1: n1 = `n0 + 1`)
  (p2: pointer)
  (Post2: p2 = (access_pointer Ltl p1))
  (is_list Lhd Ltl p2) /\ (tl_order (triple Lhd Ltl p2) (triple Lhd Ltl p1)).
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

(* Why obligation from file "length.mlw", characters 1072-1241 *)
Lemma length_po_5 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (is_list Lhd Ltl p0))
  (result: pointer)
  (Post8: result = p0)
  (result0: Z)
  (Post7: result0 = `0`)
  (Variant1: Triple)
  (p1: pointer)
  (Pre3: Variant1 = (triple Lhd Ltl p1))
  (Pre2: (is_list Lhd Ltl p1))
  (Test4: p1 = null /\ true = false \/ ~(p1 = null) /\ true = true)
  (p2: pointer)
  (Post10: (is_list Lhd Ltl p2) /\
           (tl_order (triple Lhd Ltl p2) (triple Lhd Ltl p1)))
  (tl_order (triple Lhd Ltl p2) Variant1).
Proof.
Intros; Rewrite Pre3; Intuition.
Save.

(* Why obligation from file "length.mlw", characters 1114-1134 *)
Lemma length_po_6 : 
  (p0: pointer)
  (Lhd: int_store)
  (Ltl: pointer_store)
  (Pre4: (is_list Lhd Ltl p0))
  (result: pointer)
  (Post8: result = p0)
  (result0: Z)
  (Post7: result0 = `0`)
  (is_list Lhd Ltl result).
Proof.
Intros; Subst result; Intuition.
Save.

