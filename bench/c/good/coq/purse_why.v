(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.
(* Add LoadPath "../../../../lib/coq". *)
Load caduceus_tactics.

(* Why obligation from file "why/purse.why", characters 151-236 *)
Lemma credit_impl_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre4: (purse_inv alloc balance p) /\ s >= 0),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 131-237 *)
Lemma credit_impl_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre4: (purse_inv alloc balance p) /\ s >= 0),
  forall (Pre3: (valid alloc p)),
  forall (aux_1: Z),
  forall (Post3: aux_1 = ((acc balance p) + s)),
  forall (Pre1: (valid alloc p)),
  forall (balance0: ((memory) Z)),
  forall (Post5: balance0 = (upd balance p aux_1)),
  ((purse_inv alloc balance0 p) /\ (acc balance0 p) =
  ((acc balance p) + s)) /\ (assigns alloc balance balance0 (pointer_loc p)).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
Save.

(* Why obligation from file "why/purse.why", characters 582-604 *)
Lemma test1_impl_po_1 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre8: ((purse_inv alloc balance p1) /\
                (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  (valid alloc p1).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 610-636 *)
Lemma test1_impl_po_2 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre8: ((purse_inv alloc balance p1) /\
                (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  forall (Pre7: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post6: balance0 = (upd balance p1 0)),
  (purse_inv alloc balance0 p2) /\ 100 >= 0.
Proof.
unfold purse_inv; intuition.
subst;caduceus.
Save.

(* Why obligation from file "why/purse.why", characters 464-788 *)
Lemma test1_impl_po_3 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre8: ((purse_inv alloc balance p1) /\
                (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  forall (Pre7: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post6: balance0 = (upd balance p1 0)),
  forall (Pre6: (purse_inv alloc balance0 p2) /\ 100 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post8: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                 ((acc balance0 p2) + 100)) /\
                 (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre5: (valid alloc p1)),
  forall (result1: Z),
  forall (Post5: result1 = (acc balance1 p1)),
  result1 = 0 /\
  (assigns alloc balance balance1
   (union_loc (pointer_loc p2) (pointer_loc p1))).
Proof.
unfold purse_inv; intuition.
subst result1.
rewrite H8; intuition.
subst balance0; caduceus.
unfold assigns; intuition.
assert (p<>p2).
apply unchanged_pointer_elim.
apply unchanged_union_elim1 with (pointer_loc p1).
assumption.
rewrite H8; intuition.
subst balance0.
assert (p<>p1).
apply unchanged_pointer_elim.
apply unchanged_union_elim2 with (pointer_loc p2).
assumption.
caduceus.
Save.


(* Why obligation from file "why/purse.why", characters 987-1013 *)
Lemma test2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post11: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post10: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  (purse_inv alloc balance p1) /\ 100 >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "why/purse.why", characters 1024-1050 *)
Lemma test2_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post11: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post10: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre14: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                  ((acc balance p1) + 100)) /\
                  (assigns alloc balance balance0 (pointer_loc p1))),
  (purse_inv alloc balance0 p2) /\ 200 >= 0.
Proof.
unfold purse_inv; intuition.
rewrite H9;intuition.
apply unchanged_pointer_intro; auto.
Admitted.

(* Why obligation from file "why/purse.why", characters 1061-1088 *)
Lemma test2_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post11: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post10: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre14: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                  ((acc balance p1) + 100)) /\
                  (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre13: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post19: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <= (acc balance1 p1).
Proof.
unfold purse_inv; intuition.
rewrite H16;intuition.
apply unchanged_pointer_intro; auto.
Admitted.

(* Why obligation from file "why/purse.why", characters 1099-1127 *)
Lemma test2_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post11: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post10: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre14: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                  ((acc balance p1) + 100)) /\
                  (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre13: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post19: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre12: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post21: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <= (acc balance2 p2).
Proof.
unfold purse_inv; intuition.
rewrite H24;intuition.
apply unchanged_pointer_intro; auto.
Admitted.

(* Why obligation from file "why/purse.why", characters 1138-1227 *)
Lemma test2_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post11: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post10: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre14: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                  ((acc balance p1) + 100)) /\
                  (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre13: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post19: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre12: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post21: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  forall (Pre11: (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <=
                 (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post23: ((purse_inv alloc balance3 p2) /\ (acc balance3 p2) =
                  ((acc balance2 p2) - 100)) /\
                  (assigns alloc balance2 balance3 (pointer_loc p2))),
  (valid alloc p1).
Proof.
intuition.
Admitted.

(* Why obligation from file "why/purse.why", characters 1138-1227 *)
Lemma test2_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post11: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post10: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre14: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                  ((acc balance p1) + 100)) /\
                  (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre13: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post19: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre12: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post21: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  forall (Pre11: (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <=
                 (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post23: ((purse_inv alloc balance3 p2) /\ (acc balance3 p2) =
                  ((acc balance2 p2) - 100)) /\
                  (assigns alloc balance2 balance3 (pointer_loc p2))),
  forall (Pre9: (valid alloc p1)),
  (valid alloc p2).
Proof.
intuition.
Admitted.

(* Why obligation from file "why/purse.why", characters 972-1236 *)
Lemma test2_impl_po_7 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post11: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post10: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre14: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                  ((acc balance p1) + 100)) /\
                  (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre13: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post19: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre12: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post21: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  forall (Pre11: (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <=
                 (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post23: ((purse_inv alloc balance3 p2) /\ (acc balance3 p2) =
                  ((acc balance2 p2) - 100)) /\
                  (assigns alloc balance2 balance3 (pointer_loc p2))),
  forall (Pre9: (valid alloc p1)),
  forall (Pre10: (valid alloc p2)),
  forall (result3: Z),
  forall (Post9: result3 = ((acc balance3 p1) + (acc balance3 p2))),
  result3 = 150.
Proof.
intuition.
subst result3.
rewrite H23;intuition.
rewrite H25.
rewrite H21.
rewrite H17; intuition.
rewrite H15.
rewrite H11; intuition.
rewrite H10.
rewrite H6.
Admitted.

(* Why obligation from file "why/purse.why", characters 1479-1564 *)
Lemma withdraw_impl_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre4: (purse_inv alloc balance p) /\ 0 <= s /\ s <= (acc balance p)),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 1459-1565 *)
Lemma withdraw_impl_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre4: (purse_inv alloc balance p) /\ 0 <= s /\ s <= (acc balance p)),
  forall (Pre3: (valid alloc p)),
  forall (aux_1: Z),
  forall (Post3: aux_1 = ((acc balance p) - s)),
  forall (Pre1: (valid alloc p)),
  forall (balance0: ((memory) Z)),
  forall (Post5: balance0 = (upd balance p aux_1)),
  ((purse_inv alloc balance0 p) /\ (acc balance0 p) =
  ((acc balance p) - s)) /\ (assigns alloc balance balance0 (pointer_loc p)).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
Save.
