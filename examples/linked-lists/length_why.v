
Require Why.

Require LinkedLists.

(* Why obligation from file "length.mlw", characters 1039-1200 *)
Lemma length_po_1 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (n: Z)
  (Post7: n = `0`)
  (well_founded ll_order).
Proof.
Intros; Exact ll_order_wf.
Save.

(* Why obligation from file "length.mlw", characters 1045-1061 *)
Lemma length_po_2 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (n: Z)
  (Post7: n = `0`)
  (Variant1: StorePointerPair)
  (p2: pointer)
  (Pre3: Variant1 = (store_pointer_pair Ltl p2))
  (Pre2: (is_list Ltl p2))
  (Test2: p2 = null)
  (result0: bool)
  (Post3: result0 = false)
  (if result0 then p2 = null /\ true = false \/ ~(p2 = null) /\ true = true
   else p2 = null /\ false = false \/ ~(p2 = null) /\ false = true).
Proof.
Destruct result0; Intuition.
Save.

(* Why obligation from file "length.mlw", characters 1045-1061 *)
Lemma length_po_3 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (n: Z)
  (Post7: n = `0`)
  (Variant1: StorePointerPair)
  (p2: pointer)
  (Pre3: Variant1 = (store_pointer_pair Ltl p2))
  (Pre2: (is_list Ltl p2))
  (Test1: ~(p2 = null))
  (result0: bool)
  (Post4: result0 = true)
  (if result0 then p2 = null /\ true = false \/ ~(p2 = null) /\ true = true
   else p2 = null /\ false = false \/ ~(p2 = null) /\ false = true).
Proof.
Destruct result0; Intuition.
Save.

(* Why obligation from file "length.mlw", characters 1039-1200 *)
Lemma length_po_4 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (n: Z)
  (Post7: n = `0`)
  (Variant1: StorePointerPair)
  (n1: Z)
  (p2: pointer)
  (Pre3: Variant1 = (store_pointer_pair Ltl p2))
  (Pre2: (is_list Ltl p2))
  (Test4: p2 = null /\ true = false \/ ~(p2 = null) /\ true = true)
  (n2: Z)
  (Post1: n2 = `n1 + 1`)
  (p3: pointer)
  (Post2: p3 = (pget Ltl p2))
  (is_list Ltl p3) /\
  (ll_order (store_pointer_pair Ltl p3) (store_pointer_pair Ltl p2)).
Proof.
Intuition.
Discriminate H1.
Discriminate H1.
Inversion Pre2.
Rewrite H in H0; Intuition.
Case (eq_null_dec p3); Intro.
Clear Post2; Subst p3; Auto.
Subst p3; Auto.
Unfold store_pointer_pair ll_order.
Generalize (is_list_llist ? ? Pre2).
Intros (l, Hl).
Inversion Hl; Intuition.
Exists l0; Exists l; Subst; Intuition.
Rewrite <- H4; Simpl; Omega.
Save.

(* Why obligation from file "length.mlw", characters 1039-1200 *)
Lemma length_po_5 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (n: Z)
  (Post7: n = `0`)
  (Variant1: StorePointerPair)
  (p2: pointer)
  (Pre3: Variant1 = (store_pointer_pair Ltl p2))
  (Pre2: (is_list Ltl p2))
  (Test4: p2 = null /\ true = false \/ ~(p2 = null) /\ true = true)
  (p3: pointer)
  (Post10: (is_list Ltl p3) /\
           (ll_order (store_pointer_pair Ltl p3) (store_pointer_pair Ltl p2)))
  (ll_order (store_pointer_pair Ltl p3) Variant1).
Proof.
Intros; Rewrite Pre3; Intuition.
Save.

(* Why obligation from file "length.mlw", characters 1081-1096 *)
Lemma length_po_6 : 
  (p0: pointer)
  (Ltl: pointer_store)
  (Pre4: (is_list Ltl p0))
  (p: pointer)
  (Post8: p = p0)
  (n: Z)
  (Post7: n = `0`)
  (is_list Ltl p).
Proof.
Intros; Subst p; Intuition.
Save.

