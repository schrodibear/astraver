(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/separation3.why", characters 207-284 *)
Lemma f2_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (c: ((memory) pointer)),
  forall (l: pointer),
  forall (q: ((memory) pointer)),
  forall (r: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre13: (valid_range alloc l 0 1) /\ (valid_range alloc s0 0 1) /\
                 (separation_l_s0 alloc b c q r s0 l)),
  (valid alloc s0).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/separation3.why", characters 292-319 *)
Lemma f2_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (c: ((memory) pointer)),
  forall (l: pointer),
  forall (q: ((memory) pointer)),
  forall (r: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre13: (valid_range alloc l 0 1) /\ (valid_range alloc s0 0 1) /\
                 (separation_l_s0 alloc b c q r s0 l)),
  forall (Pre4: (valid alloc s0)),
  forall (caduceus_4: pointer),
  forall (Post3: caduceus_4 = (shift (acc b s0) 2)),
  (valid alloc caduceus_4).
Proof.
intuition; subst.
generalize (valid_S_b_pointer alloc b s0).
unfold valid_S_b; intuition.
Save.

(* Why obligation from file "why/separation3.why", characters 190-319 *)
Lemma f2_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (c: ((memory) pointer)),
  forall (intP: ((memory) Z)),
  forall (l: pointer),
  forall (p: ((memory) pointer)),
  forall (q: ((memory) pointer)),
  forall (r: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre13: (valid_range alloc l 0 1) /\ (valid_range alloc s0 0 1) /\
                 (separation_l_s0 alloc b c q r s0 l)),
  forall (Pre4: (valid alloc s0)),
  forall (caduceus_4: pointer),
  forall (Post3: caduceus_4 = (shift (acc b s0) 2)),
  forall (Pre3: (valid alloc caduceus_4)),
  forall (intP0: ((memory) Z)),
  forall (Post8: intP0 = (upd intP caduceus_4 1)),
  (forall (result:pointer),
   (result = l ->
    (forall (p0:((memory) pointer)),
     (p0 = (upd p result s0) ->
      (((((forall (result:Z),
           (result = (acc intP0 (shift (acc b (acc p0 l)) 2)) -> result = 1)) /\
      (valid alloc l)) /\ (valid alloc (acc p0 l))) /\
      (valid alloc (acc p0 l))) /\
      (valid alloc (shift (acc b (acc p0 l)) 2))) /\
      (valid alloc (shift (acc b (acc p0 l)) 2)))) /\
    (valid alloc result))).
Proof.
intuition; subst; try caduceus.
valid.
Save.

(* Why obligation from file "why/separation3.why", characters 623-700 *)
Lemma f3_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (s0: pointer),
  forall (Pre12: (valid_range alloc s0 0 1)),
  (valid alloc s0).
Proof.
intuition.
Save.

(* Why obligation from file "why/separation3.why", characters 708-735 *)
Lemma f3_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre12: (valid_range alloc s0 0 1)),
  forall (Pre4: (valid alloc s0)),
  forall (caduceus_5: pointer),
  forall (Post3: caduceus_5 = (shift (acc b s0) 2)),
  (valid alloc caduceus_5).
Proof.
intuition; subst.
generalize (valid_S_b_pointer alloc b s0); unfold valid_S_b; intuition.
Save.

(* Why obligation from file "why/separation3.why", characters 606-735 *)
Lemma f3_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (c: ((memory) pointer)),
  forall (intP: ((memory) Z)),
  forall (s0: pointer),
  forall (Pre12: (valid_range alloc s0 0 1)),
  forall (Pre4: (valid alloc s0)),
  forall (caduceus_5: pointer),
  forall (Post3: caduceus_5 = (shift (acc b s0) 2)),
  forall (Pre3: (valid alloc caduceus_5)),
  forall (intP0: ((memory) Z)),
  forall (Post8: intP0 = (upd intP caduceus_5 1)),
  (forall (result:pointer),
   (result = (shift (acc c s0) 2) ->
    (forall (intP:((memory) Z)),
     (intP = (upd intP0 result 2) ->
      (((forall (result:Z),
         (result = (acc intP (shift (acc b s0) 2)) -> result = 1)) /\
      (valid alloc s0)) /\ (valid alloc (shift (acc b s0) 2))) /\
      (valid alloc (shift (acc b s0) 2)))) /\
    (valid alloc result))) /\
  (valid alloc s0).
Proof.
intuition; subst; caduceus; auto.
rewrite acc_upd_neq.
caduceus.
generalize (valid_S_pointer alloc b c s0); unfold internal_separation_S.
intuition.
generalize (neq_base_addr_neq_shift (s0#c) (s0#b) 2 2).
intuition.
generalize (valid_S_c_pointer alloc c s0); unfold valid_S_c; intuition.
Save.

(* Why obligation from file "why/separation3.why", characters 1193-1217 *)
Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (c: ((memory) pointer)),
  forall (l: pointer),
  forall (q: ((memory) pointer)),
  forall (r: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre9: (valid_range alloc l 0 1) /\ (valid_range alloc s0 0 1) /\
                (separation_l_s0 alloc b c q r s0 l)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = s0),
  (valid alloc caduceus_2).
Proof.
intuition; subst; valid.
Save.

(* Why obligation from file "why/separation3.why", characters 1169-1217 *)
Lemma f_impl_po_2 : 
  forall (a: ((memory) Z)),
  forall (alloc: alloc_table),
  forall (b: ((memory) pointer)),
  forall (c: ((memory) pointer)),
  forall (l: pointer),
  forall (q: ((memory) pointer)),
  forall (r: ((memory) pointer)),
  forall (s0: pointer),
  forall (Pre9: (valid_range alloc l 0 1) /\ (valid_range alloc s0 0 1) /\
                (separation_l_s0 alloc b c q r s0 l)),
  forall (caduceus_2: pointer),
  forall (Post3: caduceus_2 = s0),
  forall (Pre3: (valid alloc caduceus_2)),
  forall (a0: ((memory) Z)),
  forall (Post8: a0 = (upd a caduceus_2 1)),
  (forall (result:pointer),
   (result = (acc q l) ->
    (forall (a:((memory) Z)),
     (a = (upd a0 result 2) ->
      (forall (result:Z), (result = (acc a s0) -> result = 1)) /\
      (valid alloc s0))) /\
    (valid alloc result))) /\
  (valid alloc l).
Proof.
intuition; subst; caduceus.
rewrite acc_upd_neq; caduceus.
red in H2.
rewrite <- (shift_zero (l#q)).
rewrite <- (shift_zero s0).
apply neq_base_addr_neq_shift; intuition.
generalize (valid_L_q_pointer alloc q l).
cut (valid alloc l).
unfold valid_L_q; intuition.
valid.
Save.

