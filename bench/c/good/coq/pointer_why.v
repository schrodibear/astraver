(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import caduceus_why.

(* Why obligation from file "why/pointer.why", characters 280-325 *)
Lemma array1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (Pre4: (valid_index alloc t 2) /\ (valid_range alloc t 0 5)),
  forall (p1: pointer),
  forall (Post1: p1 = (shift t 2)),
  forall (caduceus: pointer),
  forall (Post8: caduceus = p1),
  forall (p2: pointer),
  forall (Post6: p2 = (shift caduceus 1)),
  forall (result1: pointer),
  forall (Post7: result1 = caduceus),
  (forall (result:Z),
   (result = 1 ->
    (forall (intP0:((memory) Z)),
     (intP0 = (upd intP result1 result) ->
      (forall (result0:Z), (result0 = result -> result0 = 1)))) /\
    (valid alloc result1))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 624-660 *)
Lemma f2_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post8: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  (valid alloc caduceus1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 668-723 *)
Lemma f2_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post8: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  forall (Pre6: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post6: caduceus2 = ((acc intP0 caduceus1) + 1)),
  forall (Pre5: (valid alloc caduceus1)),
  forall (intP1: ((memory) Z)),
  forall (Post13: intP1 = (upd intP0 caduceus1 caduceus2)),
  forall (result1: Z),
  forall (Post5: result1 = caduceus2),
  (acc intP1 x) = 1 /\ result1 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 936-958 *)
Lemma f_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post8: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  (valid alloc caduceus1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 966-1035 *)
Lemma f_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post8: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  forall (Pre6: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post6: caduceus2 = (acc intP0 caduceus1)),
  forall (Pre5: (valid alloc caduceus1)),
  forall (intP1: ((memory) Z)),
  forall (Post13: intP1 = (upd intP0 caduceus1 (1 + caduceus2))),
  forall (result1: Z),
  forall (Post5: result1 = caduceus2),
  ((acc intP1 x) = 1 /\ result1 = 0) /\
  (assigns alloc intP intP1 (pointer_loc x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1190-1279 *)
Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (r: pointer),
  forall (Pre3: (valid alloc r)),
  forall (intP0: ((memory) Z)),
  forall (result: Z),
  forall (Post2: ((acc intP0 r) = 1 /\ result = 0) /\
                 (assigns alloc intP intP0 (pointer_loc r))),
  (acc intP0 r) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1357-1376 *)
Lemma h_impl_po_1 : 
  1 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1445-1472 *)
Lemma h_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intPP: ((memory) pointer)),
  forall (Pre11: 1 >= 1),
  forall (alloc0: alloc_table),
  forall (z: pointer),
  forall (Post8: (valid alloc0 z) /\ (offset z) = 0 /\
                 (block_length alloc0 z) = 1 /\
                 (valid_range alloc0 z 0 (1 - 1)) /\ (fresh alloc z) /\
                 (on_stack alloc0 z) /\ (alloc_stack z alloc alloc0)),
  forall (Pre6: (valid alloc0 z)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (acc intPP z)),
  (valid alloc0 caduceus_2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1408-1472 *)
Lemma h_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (intPP: ((memory) pointer)),
  forall (Pre11: 1 >= 1),
  forall (alloc0: alloc_table),
  forall (z: pointer),
  forall (Post8: (valid alloc0 z) /\ (offset z) = 0 /\
                 (block_length alloc0 z) = 1 /\
                 (valid_range alloc0 z 0 (1 - 1)) /\ (fresh alloc z) /\
                 (on_stack alloc0 z) /\ (alloc_stack z alloc alloc0)),
  forall (Pre6: (valid alloc0 z)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = (acc intPP z)),
  forall (Pre5: (valid alloc0 caduceus_2)),
  forall (intP0: ((memory) Z)),
  forall (Post12: intP0 = (upd intP caduceus_2 0)),
  (forall (result:Z),
   (forall (intP:((memory) Z)),
    (((acc intP z) = 1 /\ result = 0) /\
     (assigns alloc0 intP0 intP (pointer_loc z)) ->
     (forall (result0:Z), (result0 = (result + (acc intP z)) -> result0 = 1)) /\
     (valid alloc0 z)))) /\
  (valid alloc0 z).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1781-1799 *)
Lemma struct1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (Pre9: (valid alloc s) /\ (valid_range alloc s 0 1)),
  forall (Pre8: (valid alloc s)),
  forall (p: pointer),
  forall (Post7: p = (acc x s)),
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1831-1855 *)
Lemma struct1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (Pre9: (valid alloc s) /\ (valid_range alloc s 0 1)),
  forall (Pre8: (valid alloc s)),
  forall (p: pointer),
  forall (Post7: p = (acc x s)),
  forall (Pre7: (valid alloc p)),
  forall (intP0: ((memory) Z)),
  forall (Post11: intP0 = (upd intP p 1)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = s),
  (valid alloc caduceus_1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1808-1855 *)
Lemma struct1_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (x: ((memory) pointer)),
  forall (y: ((memory) Z)),
  forall (Pre9: (valid alloc s) /\ (valid_range alloc s 0 1)),
  forall (Pre8: (valid alloc s)),
  forall (p: pointer),
  forall (Post7: p = (acc x s)),
  forall (Pre7: (valid alloc p)),
  forall (intP0: ((memory) Z)),
  forall (Post11: intP0 = (upd intP p 1)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = s),
  forall (Pre5: (valid alloc caduceus_1)),
  forall (y0: ((memory) Z)),
  forall (Post13: y0 = (upd y caduceus_1 2)),
  (forall (result:Z), (result = (acc intP0 p) -> result >= 1)) /\
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

