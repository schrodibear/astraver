(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import caduceus_why.

(* Why obligation from file "why/pointer.why", characters 429-477 *)
Lemma array1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre4: (valid_index alloc t 2) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (alloc0: alloc_table),
  forall (Post10: (alloc_extends alloc alloc0)),
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
    (valid alloc0 result1))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 866-903 *)
Lemma f2_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre8: (valid alloc x) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post9: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  (valid alloc caduceus1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 910-968 *)
Lemma f2_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre8: (valid alloc x) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post9: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  forall (Pre6: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post6: caduceus2 = ((acc intP0 caduceus1) + 1)),
  forall (Pre5: (valid alloc caduceus1)),
  forall (intP1: ((memory) Z)),
  forall (Post14: intP1 = (upd intP0 caduceus1 caduceus2)),
  forall (result1: Z),
  forall (Post5: result1 = caduceus2),
  (acc intP1 x) = 1 /\ result1 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1293-1316 *)
Lemma f_impl_po_1 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre8: (valid alloc x) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post9: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  (valid alloc caduceus1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1323-1395 *)
Lemma f_impl_po_2 : 
  forall (x: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre8: (valid alloc x) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (Pre7: (valid alloc x)),
  forall (intP0: ((memory) Z)),
  forall (Post9: intP0 = (upd intP x 0)),
  forall (caduceus1: pointer),
  forall (Post7: caduceus1 = x),
  forall (Pre6: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post6: caduceus2 = (acc intP0 caduceus1)),
  forall (Pre5: (valid alloc caduceus1)),
  forall (intP1: ((memory) Z)),
  forall (Post14: intP1 = (upd intP0 caduceus1 (1 + caduceus2))),
  forall (result1: Z),
  forall (Post5: result1 = caduceus2),
  ((acc intP1 x) = 1 /\ result1 = 0) /\
  (assigns alloc intP intP1 (pointer_loc x)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1553-1751 *)
Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (r: pointer),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre3: (valid alloc r) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (intP0: ((memory) Z)),
  forall (result: Z),
  forall (Post2: ((acc intP0 r) = 1 /\ result = 0) /\
                 (assigns alloc intP intP0 (pointer_loc r))),
  (acc intP0 r) = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 1967-1986 *)
Lemma struct1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre8: (valid alloc s) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (p: pointer),
  forall (Post7: p = s),
  (valid alloc p).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 2025-2050 *)
Lemma struct1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (t: pointer),
  forall (Pre8: (valid alloc s) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (p: pointer),
  forall (Post7: p = s),
  forall (Pre7: (valid alloc p)),
  forall (intP0: ((memory) Z)),
  forall (Post10: intP0 = (upd intP p 1)),
  forall (caduceus_1: pointer),
  forall (Post5: caduceus_1 = s),
  (valid alloc caduceus_1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/pointer.why", characters 2002-2050 *)
Lemma struct1_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (s: pointer),
  forall (t: pointer),
  forall (y: ((memory) Z)),
  forall (Pre8: (valid alloc s) /\ (valid_range alloc t 0 4) /\
                ~((base_addr s) = (base_addr t)) /\ (valid alloc s)),
  forall (p: pointer),
  forall (Post7: p = s),
  forall (Pre7: (valid alloc p)),
  forall (intP0: ((memory) Z)),
  forall (Post10: intP0 = (upd intP p 1)),
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

