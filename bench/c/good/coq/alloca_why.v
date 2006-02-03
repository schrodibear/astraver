(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export alloca_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  3 >= 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (A818:Set), forall (A819:Set), forall (A820:Set), forall (A821:Set),
  forall (A822:Set), forall (A823:Set), forall (A824:Set),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) global)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_4: intM_global0 = (upd intM_global result 1)),
  forall (result0: ((pointer) global)),
  forall (HW_5: result0 = (shift result 1)),
  forall (intM_global1: ((memory) Z global)),
  forall (HW_6: intM_global1 = (upd intM_global0 result0 2)),
  forall (result1: ((pointer) global)),
  forall (HW_7: result1 = (shift result 2)),
  forall (intM_global2: ((memory) Z global)),
  forall (HW_8: intM_global2 = (upd intM_global1 result1 3)),
  forall (result2: ((pointer) global)),
  forall (HW_9: result2 = (shift result 2)),
  forall (result3: Z),
  forall (HW_10: result3 = (acc intM_global2 result2)),
  (* File "alloca.c", line 3, characters 13-25 *) result3 = 3.
Proof.
intuition.
Save.

Proof.
intuition.
subst;caduceus.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst.
caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  3 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (A825:Set), forall (A826:Set), forall (A827:Set), forall (A828:Set),
  forall (A829:Set), forall (A830:Set), forall (A831:Set),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  forall (HW_2: 3 >= 1),
  forall (result: ((pointer) global)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 3 /\
                (valid_range alloc0 result 0 (3 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_4: intM_global0 = (upd intM_global result 1)),
  forall (result0: ((pointer) global)),
  forall (HW_5: result0 = (shift result 1)),
  forall (intM_global1: ((memory) Z global)),
  forall (HW_6: intM_global1 = (upd intM_global0 result0 2)),
  forall (result1: ((pointer) global)),
  forall (HW_7: result1 = (shift result 2)),
  forall (intM_global2: ((memory) Z global)),
  forall (HW_8: intM_global2 = (upd intM_global1 result1 3)),
  forall (result2: ((pointer) global)),
  forall (HW_9: result2 = (shift result 2)),
  forall (result3: Z),
  forall (HW_10: result3 = (acc intM_global2 result2)),
  (* File "alloca.c", line 9, characters 13-25 *) result3 = 3.
Proof.
intuition.
Save.

Proof.
intuition;subst;caduceus;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (u: ((pointer) global)),
  forall (HW_1: (* File "alloca.c", line 17, characters 14-24 *)
                (acc intM_global (shift u 2)) = 12 /\
                (valid_range alloc u 0 3)),
  4 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma h_impl_po_2 : 
  forall (A832:Set), forall (A833:Set), forall (A834:Set), forall (A835:Set),
  forall (A836:Set), forall (A837:Set), forall (A838:Set),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (u: ((pointer) global)),
  forall (HW_1: (* File "alloca.c", line 17, characters 14-24 *)
                (acc intM_global (shift u 2)) = 12 /\
                (valid_range alloc u 0 3)),
  forall (HW_2: 4 >= 1),
  forall (result: ((pointer) global)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 4 /\
                (valid_range alloc0 result 0 (4 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_4: intM_global0 = (upd intM_global result 1)),
  forall (result0: ((pointer) global)),
  forall (HW_5: result0 = (shift result 1)),
  forall (intM_global1: ((memory) Z global)),
  forall (HW_6: intM_global1 = (upd intM_global0 result0 2)),
  forall (result1: ((pointer) global)),
  forall (HW_7: result1 = (shift result 2)),
  forall (intM_global2: ((memory) Z global)),
  forall (HW_8: intM_global2 = (upd intM_global1 result1 3)),
  forall (result2: ((pointer) global)),
  forall (HW_9: result2 = (shift result 3)),
  forall (intM_global3: ((memory) Z global)),
  forall (HW_10: intM_global3 = (upd intM_global2 result2 4)),
  forall (result3: ((pointer) global)),
  forall (HW_11: result3 = (shift u 2)),
  forall (result4: Z),
  forall (HW_12: result4 = (acc intM_global3 result3)),
  (* File "alloca.c", line 18, characters 13-26 *) result4 = 12.
Proof.
intuition.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst.
apply valid_range_valid_shift with 0 3.
apply alloc_stack_valid_range with Z3 result alloc;auto.
omega.
Save.

Proof.
intuition.
subst;caduceus;auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma two_local_arrays_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  4 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma two_local_arrays_impl_po_2 : 
  forall (A839:Set), forall (A840:Set), forall (A841:Set), forall (A842:Set),
  forall (A843:Set), forall (A844:Set), forall (A845:Set),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  forall (HW_2: 4 >= 1),
  forall (result: ((pointer) global)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 4 /\
                (valid_range alloc0 result 0 (4 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_4: intM_global0 = (upd intM_global result 1)),
  forall (result0: ((pointer) global)),
  forall (HW_5: result0 = (shift result 1)),
  forall (intM_global1: ((memory) Z global)),
  forall (HW_6: intM_global1 = (upd intM_global0 result0 2)),
  forall (result1: ((pointer) global)),
  forall (HW_7: result1 = (shift result 2)),
  forall (intM_global2: ((memory) Z global)),
  forall (HW_8: intM_global2 = (upd intM_global1 result1 3)),
  forall (result2: ((pointer) global)),
  forall (HW_9: result2 = (shift result 3)),
  forall (intM_global3: ((memory) Z global)),
  forall (HW_10: intM_global3 = (upd intM_global2 result2 4)),
  5 >= 1.
Proof.
intuition.
Save.


(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma two_local_arrays_impl_po_3 : 
  forall (A846:Set), forall (A847:Set), forall (A848:Set), forall (A849:Set),
  forall (A850:Set), forall (A851:Set), forall (A852:Set),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  forall (HW_2: 4 >= 1),
  forall (result: ((pointer) global)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 4 /\
                (valid_range alloc0 result 0 (4 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_4: intM_global0 = (upd intM_global result 1)),
  forall (result0: ((pointer) global)),
  forall (HW_5: result0 = (shift result 1)),
  forall (intM_global1: ((memory) Z global)),
  forall (HW_6: intM_global1 = (upd intM_global0 result0 2)),
  forall (result1: ((pointer) global)),
  forall (HW_7: result1 = (shift result 2)),
  forall (intM_global2: ((memory) Z global)),
  forall (HW_8: intM_global2 = (upd intM_global1 result1 3)),
  forall (result2: ((pointer) global)),
  forall (HW_9: result2 = (shift result 3)),
  forall (intM_global3: ((memory) Z global)),
  forall (HW_10: intM_global3 = (upd intM_global2 result2 4)),
  forall (HW_11: 5 >= 1),
  forall (result3: ((pointer) global)),
  forall (alloc1: alloc_table),
  forall (HW_12: (valid alloc1 result3) /\ (offset result3) = 0 /\
                 (block_length alloc1 result3) = 5 /\
                 (valid_range alloc1 result3 0 (5 - 1)) /\
                 (fresh alloc0 result3) /\ (on_stack alloc1 result3) /\
                 (alloc_stack result3 alloc0 alloc1)),
  forall (intM_global4: ((memory) Z global)),
  forall (HW_13: intM_global4 = (upd intM_global3 result3 0)),
  forall (result4: ((pointer) global)),
  forall (HW_14: result4 = (shift result3 1)),
  forall (intM_global5: ((memory) Z global)),
  forall (HW_15: intM_global5 = (upd intM_global4 result4 0)),
  forall (result5: ((pointer) global)),
  forall (HW_16: result5 = (shift result3 2)),
  forall (result6: ((pointer) global)),
  forall (HW_17: result6 = (shift result 2)),
  forall (result7: Z),
  forall (HW_18: result7 = (acc intM_global5 result6)),
  forall (intM_global6: ((memory) Z global)),
  forall (HW_19: intM_global6 = (upd intM_global5 result5 result7)),
  forall (result8: ((pointer) global)),
  forall (HW_20: result8 = (shift result3 3)),
  forall (intM_global7: ((memory) Z global)),
  forall (HW_21: intM_global7 = (upd intM_global6 result8 0)),
  forall (result9: ((pointer) global)),
  forall (HW_22: result9 = (shift result3 2)),
  forall (result10: Z),
  forall (HW_23: result10 = (acc intM_global7 result9)),
  (* File "alloca.c", line 24, characters 13-25 *) result10 = 3.
Proof.
intuition;subst;caduceus.
apply valid_range_valid_shift with 0 (4-1);auto.
omega.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
apply alloc_stack_valid with Z5 result3 alloc0;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma two_local_arrays_not_alias_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  5 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma two_local_arrays_not_alias_impl_po_2 : 
  forall (A853:Set), forall (A854:Set), forall (A855:Set), forall (A856:Set),
  forall (A857:Set), forall (A858:Set), forall (A859:Set),
  forall (alloc: alloc_table),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  forall (HW_2: 5 >= 1),
  forall (result: ((pointer) global)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 5 /\
                (valid_range alloc0 result 0 (5 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  6 >= 1.
Proof.
intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma two_local_arrays_not_alias_impl_po_3 : 
  forall (A860:Set), forall (A861:Set), forall (A862:Set), forall (A863:Set),
  forall (A864:Set), forall (A865:Set), forall (A866:Set),
  forall (alloc: alloc_table),
  forall (intM_global: ((memory) Z global)),
  forall (u: ((pointer) global)),
  forall (HW_1: (valid_range alloc u 0 3)),
  forall (HW_2: 5 >= 1),
  forall (result: ((pointer) global)),
  forall (alloc0: alloc_table),
  forall (HW_3: (valid alloc0 result) /\ (offset result) = 0 /\
                (block_length alloc0 result) = 5 /\
                (valid_range alloc0 result 0 (5 - 1)) /\
                (fresh alloc result) /\ (on_stack alloc0 result) /\
                (alloc_stack result alloc alloc0)),
  forall (HW_4: 6 >= 1),
  forall (result0: ((pointer) global)),
  forall (alloc1: alloc_table),
  forall (HW_5: (valid alloc1 result0) /\ (offset result0) = 0 /\
                (block_length alloc1 result0) = 6 /\
                (valid_range alloc1 result0 0 (6 - 1)) /\
                (fresh alloc0 result0) /\ (on_stack alloc1 result0) /\
                (alloc_stack result0 alloc0 alloc1)),
  forall (result1: ((pointer) global)),
  forall (HW_6: result1 = (shift result 4)),
  forall (intM_global0: ((memory) Z global)),
  forall (HW_7: intM_global0 = (upd intM_global result1 3)),
  forall (result2: ((pointer) global)),
  forall (HW_8: result2 = (shift result0 4)),
  forall (intM_global1: ((memory) Z global)),
  forall (HW_9: intM_global1 = (upd intM_global0 result2 1)),
  forall (result3: ((pointer) global)),
  forall (HW_10: result3 = (shift result 4)),
  forall (result4: Z),
  forall (HW_11: result4 = (acc intM_global1 result3)),
  (* File "alloca.c", line 31, characters 13-25 *) result4 = 3.
Proof.
intuition;subst.
apply valid_range_valid_shift with 0 (5-1);auto.
apply alloc_stack_valid_range with Z7 result0 alloc0;auto.
omega.
Save.

Proof.
intuition;subst;auto.
Save.

Proof.
intuition.
subst;auto.
Save.

Proof.
intuition.
subst;caduceus.
Save.

