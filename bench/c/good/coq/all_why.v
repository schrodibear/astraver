(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/all.why", characters 123-266 *)
Lemma f2_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  x0 = 1.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 305-448 *)
Lemma f3_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (Post1: x0 = (x + 1)),
  x0 = 1.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 565-611 *)
Lemma f4_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (caduceus: Z),
  forall (Post6: caduceus = x),
  forall (x0: Z),
  forall (Post4: x0 = (caduceus + 1)),
  forall (result0: Z),
  forall (Post5: result0 = caduceus),
  x0 = 1 /\ result0 = 0.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 737-771 *)
Lemma f5_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (x0: Z),
  forall (Post3: x0 = (x + 1)),
  forall (result0: Z),
  forall (Post4: result0 = x0),
  x0 = 1 /\ result0 = 1.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1193-1336 *)
Lemma f6_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x = 1),
  forall (x0: Z),
  forall (Post1: x0 = (x + 2)),
  x0 = 3.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1444-1444 *)
Lemma f7a_impl_po_1 : 
  forall (x: Z),
  forall (Test2: x = 0),
  x = 0 /\ 1 = 1 \/ x <> 0 /\ 1 = 2.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1451-1451 *)
Lemma f7a_impl_po_2 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (Test1: x <> 0),
  x = 0 /\ 2 = 1 \/ x <> 0 /\ 2 = 2.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1376-1471 *)
Lemma f7a_impl_po_3 : 
  forall (x: Z),
  forall (Pre1: x = 0),
  forall (y0: Z),
  forall (Post1: x = 0 /\ y0 = 1 \/ x <> 0 /\ y0 = 2),
  y0 = 1.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1580-1580 *)
Lemma f7b_impl_po_1 : 
  forall (x: Z),
  forall (Pre1: x <> 0),
  forall (Test2: x = 0),
  x = 0 /\ 1 = 1 \/ x <> 0 /\ 1 = 2.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1587-1587 *)
Lemma f7b_impl_po_2 : 
  forall (x: Z),
  forall (Test1: x <> 0),
  x = 0 /\ 2 = 1 \/ x <> 0 /\ 2 = 2.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1511-1607 *)
Lemma f7b_impl_po_3 : 
  forall (x: Z),
  forall (Pre1: x <> 0),
  forall (y0: Z),
  forall (Post1: x = 0 /\ y0 = 1 \/ x <> 0 /\ y0 = 2),
  y0 = 2.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 1780-1781 *)
Lemma t1_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (Pre3: (acc intP (shift t 0)) = 1 /\ (valid_range alloc t 0 2)),
  (forall (result:pointer),
   (result = (shift t 0) ->
    (forall (result0:Z),
     (result0 = (acc intP result) -> result0 = (acc intP (shift t 0)))) /\
    (valid alloc result))).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "why/all.why", characters 1646-1831 *)
Lemma t1_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (Pre3: (acc intP (shift t 0)) = 1 /\ (valid_range alloc t 0 2)),
  forall (y0: Z),
  forall (Post1: y0 = (acc intP (shift t 0))),
  y0 = 1.
Proof.
intuition.
Save.

(* Why obligation from file "why/all.why", characters 2138-2311 *)
Lemma t2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (x: Z),
  forall (Pre4: (x = 0 /\ (acc intP (shift t 0)) = 1) /\
                (valid_range alloc t 0 2)),
  forall (caduceus_1: pointer),
  forall (Post12: caduceus_1 = t),
  forall (caduceus: Z),
  forall (Post11: caduceus = x),
  forall (x0: Z),
  forall (Post9: x0 = (caduceus + 1)),
  forall (result0: Z),
  forall (Post10: result0 = caduceus),
  (forall (result:pointer),
   (result = (shift caduceus_1 result0) ->
    ((forall (result0:Z), (result0 = (acc intP result) -> result0 = 1)) /\
    (valid alloc result)) /\ (valid alloc result))).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "why/all.why", characters 2581-2699 *)
Lemma t3_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (x: Z),
  forall (Pre4: (x = 0 /\ (acc intP (shift t 1)) = 1) /\
                (valid_range alloc t 0 2)),
  forall (caduceus_1: pointer),
  forall (Post10: caduceus_1 = t),
  forall (x0: Z),
  forall (Post8: x0 = (x + 1)),
  forall (result0: Z),
  forall (Post9: result0 = x0),
  (forall (result:pointer),
   (result = (shift caduceus_1 result0) ->
    ((forall (result0:Z), (result0 = (acc intP result) -> result0 = 1)) /\
    (valid alloc result)) /\ (valid alloc result))).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "why/all.why", characters 2972-2994 *)
Lemma t4_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (x: Z),
  forall (Pre4: (x = 2 /\ (acc intP (shift t 2)) = 3) /\
                (valid_range alloc t 0 2)),
  forall (caduceus1: pointer),
  forall (Post8: caduceus1 = (shift t x)),
  (valid alloc caduceus1).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "why/all.why", characters 3118-3312 *)
Lemma t4_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (x: Z),
  forall (Pre4: (x = 2 /\ (acc intP (shift t 2)) = 3) /\
                (valid_range alloc t 0 2)),
  forall (caduceus1: pointer),
  forall (Post8: caduceus1 = (shift t x)),
  forall (Pre3: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post7: caduceus2 = (acc intP caduceus1)),
  forall (caduceus: Z),
  forall (Post6: caduceus = x),
  forall (x0: Z),
  forall (Post4: x0 = (caduceus + 1)),
  forall (result0: Z),
  forall (Post5: result0 = caduceus),
  (forall (result:Z),
   (result = (caduceus2 + result0) ->
    (forall (intP0:((memory) Z)),
     (intP0 = (upd intP caduceus1 result) -> x0 = 3 /\
      (acc intP0 (shift t 2)) = 5)) /\
    (valid alloc caduceus1))).
Proof.
intuition; subst; auto.
rewrite acc_upd; omega.
Save.

