
(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/purse.why", characters 166-184 *)
Lemma credit0_impl_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= 0),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 210-234 *)
Lemma credit0_impl_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= 0),
  forall (Pre3: (valid alloc p)),
  forall (caduceus_1: Z),
  forall (Post2: caduceus_1 = (acc balance p)),
  (forall (balance0:((memory) Z)),
   (balance0 = (upd balance p (caduceus_1 + s)) ->
    (purse_inv alloc balance0 p) /\ (acc balance0 p) = ((acc balance p) + s))) /\
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
Save.

(* Why obligation from file "why/purse.why", characters 507-525 *)
Lemma credit_impl_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= 0),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 551-575 *)
Lemma credit_impl_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= 0),
  forall (Pre3: (valid alloc p)),
  forall (caduceus_1: Z),
  forall (Post2: caduceus_1 = (acc balance p)),
  (forall (balance0:((memory) Z)),
   (balance0 = (upd balance p (caduceus_1 + s)) ->
    ((purse_inv alloc balance0 p) /\ (acc balance0 p) =
    ((acc balance p) + s)) /\
    (assigns alloc balance balance0 (pointer_loc p)))) /\
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
Save.

(* Why obligation from file "why/purse.why", characters 909-932 *)
Lemma test0_impl_po_1 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre10: (purse_inv alloc balance p1) /\ (purse_inv alloc balance p2)),
  (valid alloc p1).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 945-973 *)
Lemma test0_impl_po_2 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre10: (purse_inv alloc balance p1) /\ (purse_inv alloc balance p2)),
  forall (Pre9: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post2: balance0 = (upd balance p1 0)),
  (purse_inv alloc balance0 p2) /\ 100 >= 0.
Proof.
unfold purse_inv; intuition.
subst.
(* problem: we do not know whether p1<>p2 *)
Admitted.

(* Why obligation from file "why/purse.why", characters 937-998 *)
Lemma test0_impl_po_3 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre10: (purse_inv alloc balance p1) /\ (purse_inv alloc balance p2)),
  forall (Pre9: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post2: balance0 = (upd balance p1 0)),
  forall (Pre8: (purse_inv alloc balance0 p2) /\ 100 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post5: (purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                 ((acc balance0 p2) + 100)),
  forall (Pre7: (valid alloc p1)),
  forall (result1: Z),
  forall (Post7: result1 = (acc balance1 p1)),
  result1 = 0.
Proof.
intuition.
subst.
(* problem: we have no info relating balance1
and balance0, an assigns clause is needed *)
Admitted.

(* Why obligation from file "why/purse.why", characters 1215-1238 *)
Lemma test1_impl_po_1 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre10: ((purse_inv alloc balance p1) /\
                 (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  (valid alloc p1).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 1251-1278 *)
Lemma test1_impl_po_2 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre10: ((purse_inv alloc balance p1) /\
                 (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  forall (Pre9: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post2: balance0 = (upd balance p1 0)),
  (purse_inv alloc balance0 p2) /\ 100 >= 0.
Proof.
unfold purse_inv; intuition.
subst; caduceus.
Save.

(* Why obligation from file "why/purse.why", characters 1243-1303 *)
Lemma test1_impl_po_3 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre10: ((purse_inv alloc balance p1) /\
                 (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  forall (Pre9: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post2: balance0 = (upd balance p1 0)),
  forall (Pre8: (purse_inv alloc balance0 p2) /\ 100 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post5: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                 ((acc balance0 p2) + 100)) /\
                 (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre7: (valid alloc p1)),
  forall (result1: Z),
  forall (Post7: result1 = (acc balance1 p1)),
  result1 = 0.
Proof.
unfold purse_inv; intuition.
subst result1.
rewrite H8; intuition.
subst balance0; caduceus.
Save.

(* Why obligation from file "why/purse.why", characters 1498-1525 *)
Lemma test2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  (purse_inv alloc balance p1) /\ 100 >= 0.
Proof.
intuition.
Save.

(* Why obligation from file "why/purse.why", characters 1541-1568 *)
Lemma test2_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                 ((acc balance p1) + 100)) /\
                 (assigns alloc balance balance0 (pointer_loc p1))),
  (purse_inv alloc balance0 p2) /\ 200 >= 0.
Proof.
unfold purse_inv; intuition.
rewrite H9; intuition.
(* problem: need to know that p1 <> p2, which
   should be a consequence of
H1 : valid alloc p1
H0 : fresh alloc p2

but there is a bug: we cannot have 
H6 : valid alloc p2
which contradicts H0.
*)
Admitted.

(* Why obligation from file "why/purse.why", characters 1586-1614 *)
Lemma test2_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                 ((acc balance p1) + 100)) /\
                 (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <= (acc balance1 p1).
Proof.
unfold purse_inv; intuition.
rewrite H16; intuition.
(* again we need p1 <> p2 *)
Admitted.

(* Why obligation from file "why/purse.why", characters 1634-1663 *)
Lemma test2_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                 ((acc balance p1) + 100)) /\
                 (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <= (acc balance2 p2).
Proof.
unfold purse_inv; intuition.
Admitted.

(* Why obligation from file "why/purse.why", characters 1688-1707 *)
Lemma test2_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                 ((acc balance p1) + 100)) /\
                 (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  forall (Pre15: (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <=
                 (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance3 p2) /\ (acc balance3 p2) =
                  ((acc balance2 p2) - 100)) /\
                  (assigns alloc balance2 balance3 (pointer_loc p2))),
  (valid alloc p1).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 1739-1758 *)
Lemma test2_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                 ((acc balance p1) + 100)) /\
                 (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  forall (Pre15: (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <=
                 (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance3 p2) /\ (acc balance3 p2) =
                  ((acc balance2 p2) - 100)) /\
                  (assigns alloc balance2 balance3 (pointer_loc p2))),
  forall (Pre14: (valid alloc p1)),
  forall (caduceus_1: Z),
  forall (Post20: caduceus_1 = (acc balance3 p1)),
  (valid alloc p2).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 1717-1759 *)
Lemma test2_impl_po_7 : 
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: ((purse_inv alloc balance0 p1) /\ (acc balance0 p1) =
                 ((acc balance p1) + 100)) /\
                 (assigns alloc balance balance0 (pointer_loc p1))),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: ((purse_inv alloc balance1 p2) /\ (acc balance1 p2) =
                  ((acc balance0 p2) + 200)) /\
                  (assigns alloc balance0 balance1 (pointer_loc p2))),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 0 <= 50 /\ 50 <=
                 (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: ((purse_inv alloc balance2 p1) /\ (acc balance2 p1) =
                  ((acc balance1 p1) - 50)) /\
                  (assigns alloc balance1 balance2 (pointer_loc p1))),
  forall (Pre15: (purse_inv alloc balance2 p2) /\ 0 <= 100 /\ 100 <=
                 (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post17: ((purse_inv alloc balance3 p2) /\ (acc balance3 p2) =
                  ((acc balance2 p2) - 100)) /\
                  (assigns alloc balance2 balance3 (pointer_loc p2))),
  forall (Pre14: (valid alloc p1)),
  forall (caduceus_1: Z),
  forall (Post20: caduceus_1 = (acc balance3 p1)),
  forall (Pre13: (valid alloc p2)),
  forall (aux_1: Z),
  forall (Post23: aux_1 = (acc balance3 p2)),
  (caduceus_1 + aux_1) = 150.
Proof.
intuition.
subst.
rewrite H25.
rewrite H23; intuition.
rewrite H21.
rewrite H17; intuition.
rewrite H15.
rewrite H11; intuition.
rewrite H10.
Admitted.

(* Why obligation from file "why/purse.why", characters 2025-2043 *)
Lemma withdraw0_impl_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ 0 <= s /\ s <= (acc balance p)),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 2069-2093 *)
Lemma withdraw0_impl_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ 0 <= s /\ s <= (acc balance p)),
  forall (Pre3: (valid alloc p)),
  forall (caduceus_1: Z),
  forall (Post2: caduceus_1 = (acc balance p)),
  (forall (balance0:((memory) Z)),
   (balance0 = (upd balance p (caduceus_1 - s)) ->
    (purse_inv alloc balance0 p) /\ (acc balance0 p) = ((acc balance p) - s))) /\
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst;caduceus.
Save.

(* Why obligation from file "why/purse.why", characters 2405-2423 *)
Lemma withdraw_impl_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ 0 <= s /\ s <= (acc balance p)),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 2449-2473 *)
Lemma withdraw_impl_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc_table),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ 0 <= s /\ s <= (acc balance p)),
  forall (Pre3: (valid alloc p)),
  forall (caduceus_1: Z),
  forall (Post2: caduceus_1 = (acc balance p)),
  (forall (balance0:((memory) Z)),
   (balance0 = (upd balance p (caduceus_1 - s)) ->
    ((purse_inv alloc balance0 p) /\ (acc balance0 p) =
    ((acc balance p) - s)) /\
    (assigns alloc balance balance0 (pointer_loc p)))) /\
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
subst; caduceus.
subst; caduceus.
(* needs a tactic to prove an assigns clause *)
Admitted.

