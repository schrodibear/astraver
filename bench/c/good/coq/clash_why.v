(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/clash.why", characters 344-379 *)
Lemma f1_impl_po_1 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (toto: ((memory) Z)),
  forall (Pre4: ((valid alloc ma_structure) /\ (valid alloc ma_structure)) /\
                (forall (anonymous_0:pointer),
                 ((valid alloc anonymous_0) ->
                  (valid_anonymous_0_toto (acc toto anonymous_0))))),
  forall (toto_0_1: Z),
  forall (Post1: toto_0_1 = 0),
  (valid alloc ma_structure).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", characters 323-381 *)
Lemma f1_impl_po_2 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (toto: ((memory) Z)),
  forall (Pre4: ((valid alloc ma_structure) /\ (valid alloc ma_structure)) /\
                (forall (anonymous_0:pointer),
                 ((valid alloc anonymous_0) ->
                  (valid_anonymous_0_toto (acc toto anonymous_0))))),
  forall (toto_0_1: Z),
  forall (Post1: toto_0_1 = 0),
  forall (Pre3: (valid alloc ma_structure)),
  forall (toto0: ((memory) Z)),
  forall (Post8: toto0 = (upd toto ma_structure toto_0_1)),
  (not_assigns alloc toto toto0 (pset_singleton ma_structure)) /\
  (forall (anonymous_0:pointer),
   ((valid alloc anonymous_0) ->
    (valid_anonymous_0_toto (acc toto0 anonymous_0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/clash.why", characters 1643-1662 *)
Lemma f2_impl_po_1 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (fst: ((memory) Z)),
  forall (substruct: ((memory) pointer)),
  forall (Pre11: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                 (valid alloc (acc substruct ma_structure))) /\
                 (forall (anonymous_1:pointer),
                  ((valid alloc anonymous_1) ->
                   (valid_anonymous_1_fst (acc fst anonymous_1)))) /\
                 (forall (anonymous_1:pointer),
                  (forall (anonymous_2:pointer),
                   (~(anonymous_1 = anonymous_2) ->
                    ~((base_addr anonymous_1) = (base_addr (acc substruct
                                                            anonymous_2)))))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (valid_anonymous_2_substruct alloc
                    (acc substruct anonymous_2)))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (internal_separation_anonymous_2 alloc substruct
                    anonymous_2)))),
  1 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", characters 1747-1777 *)
Lemma f2_impl_po_2 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (fst: ((memory) Z)),
  forall (substruct: ((memory) pointer)),
  forall (Pre11: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                 (valid alloc (acc substruct ma_structure))) /\
                 (forall (anonymous_1:pointer),
                  ((valid alloc anonymous_1) ->
                   (valid_anonymous_1_fst (acc fst anonymous_1)))) /\
                 (forall (anonymous_1:pointer),
                  (forall (anonymous_2:pointer),
                   (~(anonymous_1 = anonymous_2) ->
                    ~((base_addr anonymous_1) = (base_addr (acc substruct
                                                            anonymous_2)))))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (valid_anonymous_2_substruct alloc
                    (acc substruct anonymous_2)))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (internal_separation_anonymous_2 alloc substruct
                    anonymous_2)))),
  forall (Pre10: 1 >= 1),
  forall (alloc0: alloc_table),
  forall (substruct_0: pointer),
  forall (Post9: (valid alloc0 substruct_0) /\ (offset substruct_0) = 0 /\
                 (block_length alloc0 substruct_0) = 1 /\
                 (valid_range alloc0 substruct_0 0 (1 - 1)) /\
                 (fresh alloc substruct_0) /\
                 (on_stack alloc0 substruct_0) /\
                 (alloc_stack substruct_0 alloc alloc0)),
  forall (Pre9: (valid alloc0 substruct_0)),
  forall (fst0: ((memory) Z)),
  forall (Post13: fst0 = (upd fst substruct_0 0)),
  (valid alloc0 ma_structure).
Proof.
intuition.
apply alloc_stack_valid with substruct_0 alloc; auto.

Save.

(* Why obligation from file "why/clash.why", characters 1788-1837 *)
Lemma f2_impl_po_3 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (fst: ((memory) Z)),
  forall (substruct: ((memory) pointer)),
  forall (Pre11: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                 (valid alloc (acc substruct ma_structure))) /\
                 (forall (anonymous_1:pointer),
                  ((valid alloc anonymous_1) ->
                   (valid_anonymous_1_fst (acc fst anonymous_1)))) /\
                 (forall (anonymous_1:pointer),
                  (forall (anonymous_2:pointer),
                   (~(anonymous_1 = anonymous_2) ->
                    ~((base_addr anonymous_1) = (base_addr (acc substruct
                                                            anonymous_2)))))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (valid_anonymous_2_substruct alloc
                    (acc substruct anonymous_2)))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (internal_separation_anonymous_2 alloc substruct
                    anonymous_2)))),
  forall (Pre10: 1 >= 1),
  forall (alloc0: alloc_table),
  forall (substruct_0: pointer),
  forall (Post9: (valid alloc0 substruct_0) /\ (offset substruct_0) = 0 /\
                 (block_length alloc0 substruct_0) = 1 /\
                 (valid_range alloc0 substruct_0 0 (1 - 1)) /\
                 (fresh alloc substruct_0) /\
                 (on_stack alloc0 substruct_0) /\
                 (alloc_stack substruct_0 alloc alloc0)),
  forall (Pre9: (valid alloc0 substruct_0)),
  forall (fst0: ((memory) Z)),
  forall (Post13: fst0 = (upd fst substruct_0 0)),
  forall (Pre8: (valid alloc0 ma_structure)),
  forall (caduceus_1: pointer),
  forall (Post6: caduceus_1 = (acc substruct ma_structure)),
  forall (Pre7: (valid alloc0 substruct_0)),
  forall (aux_1: Z),
  forall (Post5: aux_1 = (acc fst0 substruct_0)),
  (valid alloc0 caduceus_1).
Proof.
intuition.
subst; apply alloc_stack_valid with substruct_0 alloc; auto.
Save.

(* Why obligation from file "why/clash.why", characters 1788-1837 *)
Lemma f2_impl_po_4 : 
  forall (ma_structure: pointer),
  forall (alloc: alloc_table),
  forall (fst: ((memory) Z)),
  forall (substruct: ((memory) pointer)),
  forall (Pre11: ((valid alloc ma_structure) /\ (valid alloc ma_structure) /\
                 (valid alloc (acc substruct ma_structure))) /\
                 (forall (anonymous_1:pointer),
                  ((valid alloc anonymous_1) ->
                   (valid_anonymous_1_fst (acc fst anonymous_1)))) /\
                 (forall (anonymous_1:pointer),
                  (forall (anonymous_2:pointer),
                   (~(anonymous_1 = anonymous_2) ->
                    ~((base_addr anonymous_1) = (base_addr (acc substruct
                                                            anonymous_2)))))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (valid_anonymous_2_substruct alloc
                    (acc substruct anonymous_2)))) /\
                 (forall (anonymous_2:pointer),
                  ((valid alloc anonymous_2) ->
                   (internal_separation_anonymous_2 alloc substruct
                    anonymous_2)))),
  forall (Pre10: 1 >= 1),
  forall (alloc0: alloc_table),
  forall (substruct_0: pointer),
  forall (Post9: (valid alloc0 substruct_0) /\ (offset substruct_0) = 0 /\
                 (block_length alloc0 substruct_0) = 1 /\
                 (valid_range alloc0 substruct_0 0 (1 - 1)) /\
                 (fresh alloc substruct_0) /\
                 (on_stack alloc0 substruct_0) /\
                 (alloc_stack substruct_0 alloc alloc0)),
  forall (Pre9: (valid alloc0 substruct_0)),
  forall (fst0: ((memory) Z)),
  forall (Post13: fst0 = (upd fst substruct_0 0)),
  forall (Pre8: (valid alloc0 ma_structure)),
  forall (caduceus_1: pointer),
  forall (Post6: caduceus_1 = (acc substruct ma_structure)),
  forall (Pre7: (valid alloc0 substruct_0)),
  forall (aux_1: Z),
  forall (Post5: aux_1 = (acc fst0 substruct_0)),
  forall (Pre5: (valid alloc0 caduceus_1)),
  forall (fst1: ((memory) Z)),
  forall (Post17: fst1 = (upd fst0 caduceus_1 aux_1)),
  (not_assigns alloc fst fst1 (pset_singleton (acc substruct ma_structure))) /\
  (forall (anonymous_1:pointer),
   ((valid alloc0 anonymous_1) ->
    (valid_anonymous_1_fst (acc fst1 anonymous_1)))).
Proof.
intros.
unfold not_assigns.
split.
intros.
subst.
caduceus.
rewrite acc_upd_neq;generalize (pset_singleton_elim p (ma_structure # substruct) H0);auto.
intro.
rewrite acc_upd_neq;auto.
inversion_clear Post9.
inversion_clear H3.
inversion_clear H5.
inversion_clear H6.
inversion_clear H7.
inversion_clear H8.
generalize (fresh_not_valid _ _ H6 0).
intros.
intro.
rewrite shift_zero in H8.
apply H8;subst;auto.
intros;
unfold valid_anonymous_1_fst;auto.
Save.



(* Why obligation from file "why/clash.why", characters 2221-2244 *)
Lemma f_impl_po_1 : 
  forall (x: Z),
  forall (Test2: x = 0),
  forall (y_0_1: Z),
  forall (Post4: y_0_1 = 1),
  forall (result1: Z),
  forall (Post5: result1 = y_0_1),
  ((x = 0 -> result1 = 1)) /\ ((x <> 0 -> result1 = 2)).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", characters 2304-2327 *)
Lemma f_impl_po_2 : 
  forall (x: Z),
  forall (Test1: x <> 0),
  forall (y_0_1: Z),
  forall (Post1: y_0_1 = 2),
  forall (result1: Z),
  forall (Post2: result1 = y_0_1),
  ((x = 0 -> result1 = 1)) /\ ((x <> 0 -> result1 = 2)).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", characters 2538-2561 *)
Lemma g_impl_po_1 : 
  forall (y: Z),
  forall (y_0_1: Z),
  forall (Post1: y_0_1 = 0),
  forall (result0: Z),
  forall (Post2: result0 = y_0_1),
  result0 = 0 /\ y = y.
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", characters 2836-2859 *)
Lemma h_impl_po_1 : 
  forall (x: Z),
  forall (y_0_1: Z),
  forall (Post1: y_0_1 = 2),
  forall (Test2: x = 0),
  forall (y_1_1: Z),
  forall (Post3: y_1_1 = 1),
  forall (result2: Z),
  forall (Post4: result2 = y_1_1),
  ((x = 0 -> result2 = 1)) /\ ((x <> 0 -> result2 = 2)).
Proof.
intuition.
Save.

(* Why obligation from file "why/clash.why", characters 2878-2879 *)
Lemma h_impl_po_2 : 
  forall (x: Z),
  forall (y_0_1: Z),
  forall (Post1: y_0_1 = 2),
  forall (Test1: x <> 0),
  forall (result1: Z),
  forall (Post2: result1 = y_0_1),
  ((x = 0 -> result1 = 1)) /\ ((x <> 0 -> result1 = 2)).
Proof.
intuition.
Save.

