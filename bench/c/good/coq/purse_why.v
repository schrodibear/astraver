(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export Why.
Require Export caduceus_spec_why.

(* Why obligation from file "why/purse.why", characters 159-177 *)
Lemma credit_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= 0),
  (valid alloc p).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 203-226 *)
Lemma credit_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= 0),
  forall (Pre3: (valid alloc p)),
  forall (caduceus1: Z),
  forall (Post2: caduceus1 = (acc balance p)),
  (forall (balance0:((memory) Z)),
   (balance0 = (upd balance p (caduceus1 + s)) ->
    (purse_inv alloc balance0 p) /\ (acc balance0 p) = ((acc balance p) + s))) /\
  (valid alloc p).
Proof.
unfold purse_inv; intuition;
subst; rewrite acc_upd_eq; omega.
Save.

(* Why obligation from file "why/purse.why", characters 506-529 *)
Lemma test1_po_1 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (Pre10: ((purse_inv alloc balance p1) /\
                 (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  (valid alloc p1).
Proof.
unfold purse_inv; intuition.
Save.

(* Why obligation from file "why/purse.why", characters 542-559 *)
Lemma test1_po_2 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (Pre10: ((purse_inv alloc balance p1) /\
                 (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  forall (Pre9: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post2: balance0 = (upd balance p1 0)),
  (purse_inv alloc balance0 p2) /\ 100 >= 0.
Proof.
unfold purse_inv; intuition; subst.

Save.

(* Why obligation from file "why/purse.why", characters 534-584 *)
Lemma test1_po_3 : 
  forall (p1: pointer),
  forall (p2: pointer),
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (Pre10: ((purse_inv alloc balance p1) /\
                 (purse_inv alloc balance p2)) /\ ~(p1 = p2)),
  forall (Pre9: (valid alloc p1)),
  forall (balance0: ((memory) Z)),
  forall (Post2: balance0 = (upd balance p1 0)),
  forall (Pre8: (purse_inv alloc balance0 p2) /\ 100 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post5: (purse_inv alloc balance1 p2) /\
                 (acc balance1 p2) = ((acc balance0 p2) + 100)),
  forall (Pre7: (valid alloc p1)),
  forall (result1: Z),
  forall (Post7: result1 = (acc balance1 p1)),
  result1 = 0.
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 789-807 *)
Lemma withdraw_po_1 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= (acc balance p)),
  (valid alloc p).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 833-856 *)
Lemma withdraw_po_2 : 
  forall (p: pointer),
  forall (s: Z),
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (Pre6: (purse_inv alloc balance p) /\ s >= (acc balance p)),
  forall (Pre3: (valid alloc p)),
  forall (caduceus2: Z),
  forall (Post2: caduceus2 = (acc balance p)),
  (forall (balance0:((memory) Z)),
   (balance0 = (upd balance p (caduceus2 - s)) ->
    (purse_inv alloc balance0 p) /\ (acc balance0 p) = ((acc balance p) - s))) /\
  (valid alloc p).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 1114-1131 *)
Lemma test2_po_1 : 
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  (purse_inv alloc balance p1) /\ 100 >= 0.
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 1147-1164 *)
Lemma test2_po_2 : 
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: (purse_inv alloc balance0 p1) /\
                 (acc balance0 p1) = ((acc balance p1) + 100)),
  (purse_inv alloc balance0 p2) /\ 200 >= 0.
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 1182-1200 *)
Lemma test2_po_3 : 
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: (purse_inv alloc balance0 p1) /\
                 (acc balance0 p1) = ((acc balance p1) + 100)),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: (purse_inv alloc balance1 p2) /\
                  (acc balance1 p2) = ((acc balance0 p2) + 200)),
  (purse_inv alloc balance1 p1) /\ 50 >= (acc balance1 p1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 1220-1239 *)
Lemma test2_po_4 : 
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: (purse_inv alloc balance0 p1) /\
                 (acc balance0 p1) = ((acc balance p1) + 100)),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: (purse_inv alloc balance1 p2) /\
                  (acc balance1 p2) = ((acc balance0 p2) + 200)),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 50 >= (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: (purse_inv alloc balance2 p1) /\
                  (acc balance2 p1) = ((acc balance1 p1) - 50)),
  (purse_inv alloc balance2 p2) /\ 100 >= (acc balance2 p2).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 1263-1282 *)
Lemma test2_po_5 : 
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: (purse_inv alloc balance0 p1) /\
                 (acc balance0 p1) = ((acc balance p1) + 100)),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: (purse_inv alloc balance1 p2) /\
                  (acc balance1 p2) = ((acc balance0 p2) + 200)),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 50 >= (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: (purse_inv alloc balance2 p1) /\
                  (acc balance2 p1) = ((acc balance1 p1) - 50)),
  forall (Pre15: (purse_inv alloc balance2 p2) /\ 100 >= (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post17: (purse_inv alloc balance3 p2) /\
                  (acc balance3 p2) = ((acc balance2 p2) - 100)),
  (valid alloc p1).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 1313-1332 *)
Lemma test2_po_6 : 
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: (purse_inv alloc balance0 p1) /\
                 (acc balance0 p1) = ((acc balance p1) + 100)),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: (purse_inv alloc balance1 p2) /\
                  (acc balance1 p2) = ((acc balance0 p2) + 200)),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 50 >= (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: (purse_inv alloc balance2 p1) /\
                  (acc balance2 p1) = ((acc balance1 p1) - 50)),
  forall (Pre15: (purse_inv alloc balance2 p2) /\ 100 >= (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post17: (purse_inv alloc balance3 p2) /\
                  (acc balance3 p2) = ((acc balance2 p2) - 100)),
  forall (Pre14: (valid alloc p1)),
  forall (caduceus3: Z),
  forall (Post20: caduceus3 = (acc balance3 p1)),
  (valid alloc p2).
Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/purse.why", characters 1292-1333 *)
Lemma test2_po_7 : 
  forall (alloc: alloc),
  forall (balance: ((memory) Z)),
  forall (p1: pointer),
  forall (Post2: (fresh alloc p1) /\ (purse_inv alloc balance p1)),
  forall (p2: pointer),
  forall (Post5: (fresh alloc p2) /\ (purse_inv alloc balance p2)),
  forall (Pre18: (purse_inv alloc balance p1) /\ 100 >= 0),
  forall (balance0: ((memory) Z)),
  forall (Post8: (purse_inv alloc balance0 p1) /\
                 (acc balance0 p1) = ((acc balance p1) + 100)),
  forall (Pre17: (purse_inv alloc balance0 p2) /\ 200 >= 0),
  forall (balance1: ((memory) Z)),
  forall (Post11: (purse_inv alloc balance1 p2) /\
                  (acc balance1 p2) = ((acc balance0 p2) + 200)),
  forall (Pre16: (purse_inv alloc balance1 p1) /\ 50 >= (acc balance1 p1)),
  forall (balance2: ((memory) Z)),
  forall (Post14: (purse_inv alloc balance2 p1) /\
                  (acc balance2 p1) = ((acc balance1 p1) - 50)),
  forall (Pre15: (purse_inv alloc balance2 p2) /\ 100 >= (acc balance2 p2)),
  forall (balance3: ((memory) Z)),
  forall (Post17: (purse_inv alloc balance3 p2) /\
                  (acc balance3 p2) = ((acc balance2 p2) - 100)),
  forall (Pre14: (valid alloc p1)),
  forall (caduceus3: Z),
  forall (Post20: caduceus3 = (acc balance3 p1)),
  forall (Pre13: (valid alloc p2)),
  forall (aux_1: Z),
  forall (Post23: aux_1 = (acc balance3 p2)),
  (caduceus3 + aux_1) = 150.
Proof.
(* FILL PROOF HERE *)
Save.

