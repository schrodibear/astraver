(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/ifs.why", characters 454-1161 *)
Lemma V4A_impl_po_1 : 
  forall (Parametre: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (Pre35: (valid alloc Parametre) /\ (valid_range alloc Ch_Pn 0 4) /\
                 (separation_SPMEP_Ch_Pn Ch_Pn SPMEP) /\
                 (valid_range alloc SPMEP 0 4)),
  forall (Pre9: (valid alloc Parametre)),
  forall (caduceus_19: pointer),
  forall (Post4: caduceus_19 = (shift (acc VC Parametre) 0)),
  (valid alloc (shift Ch_Pn 0)).
Proof.
intuition.
Save.

(* Why obligation from file "why/ifs.why", characters 454-1161 *)
Lemma V4A_impl_po_2 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\ (valid_range alloc Ch_Pn 0 4) /\
                 (separation_SPMEP_Ch_Pn Ch_Pn SPMEP) /\
                 (valid_range alloc SPMEP 0 4)),
  forall (Pre9: (valid alloc Parametre)),
  forall (caduceus_19: pointer),
  forall (Post4: caduceus_19 = (shift (acc VC Parametre) 0)),
  forall (Pre4: (valid alloc (shift Ch_Pn 0))),
  ((acc intP (shift Ch_Pn 0)) = 0 -> (valid alloc (shift Pn_Bac 0)) /\
   (valid alloc (shift Pn_Bac 0))).
Proof.
intuition;rewrite shift_zero.
Admitted.

(* Why obligation from file "why/ifs.why", characters 454-1161 *)
Lemma V4A_impl_po_3 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\ (valid_range alloc Ch_Pn 0 4) /\
                 (separation_SPMEP_Ch_Pn Ch_Pn SPMEP) /\
                 (valid_range alloc SPMEP 0 4)),
  forall (Pre9: (valid alloc Parametre)),
  forall (caduceus_19: pointer),
  forall (Post4: caduceus_19 = (shift (acc VC Parametre) 0)),
  forall (Pre4: (valid alloc (shift Ch_Pn 0))),
  forall (Pre5: ((acc intP (shift Ch_Pn 0)) = 0 ->
                 (valid alloc (shift Pn_Bac 0)) /\
                 (valid alloc (shift Pn_Bac 0)))),
  ((acc intP (shift Ch_Pn 0)) = 0 /\ (acc intP (shift Pn_Bac 0)) = 0 ->
   (valid alloc (shift SPMEP 0)) /\ (valid alloc (shift SPMEP 0))).
Proof.
intuition;unfold valid_range_SPMEP in H0;
apply valid_range_valid_shift with 0 4;auto;
omega.
Save.

(* Why obligation from file "why/ifs.why", characters 427-1162 *)
Lemma V4A_impl_po_4 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\ (valid_range alloc Ch_Pn 0 4) /\
                 (separation_SPMEP_Ch_Pn Ch_Pn SPMEP) /\
                 (valid_range alloc SPMEP 0 4)),
  forall (Pre9: (valid alloc Parametre)),
  forall (caduceus_19: pointer),
  forall (Post4: caduceus_19 = (shift (acc VC Parametre) 0)),
  forall (Pre4: (valid alloc (shift Ch_Pn 0))),
  forall (Pre5: ((acc intP (shift Ch_Pn 0)) = 0 ->
                 (valid alloc (shift Pn_Bac 0)) /\
                 (valid alloc (shift Pn_Bac 0)))),
  forall (Pre6: ((acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) = 0 ->
                 (valid alloc (shift SPMEP 0)) /\
                 (valid alloc (shift SPMEP 0)))),
  forall (aux_4: Z),
  forall (Post3: (((acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) = 0) /\
                 (acc intP (shift SPMEP 0)) = 0) /\ aux_4 = 1 \/
                 (((acc intP (shift Ch_Pn 0)) <> 0 \/
                 (acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) <> 0) \/
                 ((acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) = 0) /\
                 (acc intP (shift SPMEP 0)) <> 0) /\ aux_4 = 0),
  (valid alloc caduceus_19).
Proof.
intuition; subst; auto;rewrite shift_zero;auto;
generalize (valid_anonymous_0_CPRE_VC_pointer alloc VC Parametre H);
unfold valid_anonymous_0_CPRE_VC;tauto.
Save.

(* Why obligation from file "why/ifs.why", characters 427-1162 *)
Lemma V4A_impl_po_5 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (Param4_Pn: ((memory) Z)),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\ (valid_range alloc Ch_Pn 0 4) /\
                 (separation_SPMEP_Ch_Pn Ch_Pn SPMEP) /\
                 (valid_range alloc SPMEP 0 4)),
  forall (Pre9: (valid alloc Parametre)),
  forall (caduceus_19: pointer),
  forall (Post4: caduceus_19 = (shift (acc VC Parametre) 0)),
  forall (Pre4: (valid alloc (shift Ch_Pn 0))),
  forall (Pre5: ((acc intP (shift Ch_Pn 0)) = 0 ->
                 (valid alloc (shift Pn_Bac 0)) /\
                 (valid alloc (shift Pn_Bac 0)))),
  forall (Pre6: ((acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) = 0 ->
                 (valid alloc (shift SPMEP 0)) /\
                 (valid alloc (shift SPMEP 0)))),
  forall (aux_4: Z),
  forall (Post3: (((acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) = 0) /\
                 (acc intP (shift SPMEP 0)) = 0) /\ aux_4 = 1 \/
                 (((acc intP (shift Ch_Pn 0)) <> 0 \/
                 (acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) <> 0) \/
                 ((acc intP (shift Ch_Pn 0)) = 0 /\
                 (acc intP (shift Pn_Bac 0)) = 0) /\
                 (acc intP (shift SPMEP 0)) <> 0) /\ aux_4 = 0),
  forall (Pre1: (valid alloc caduceus_19)),
  forall (intP0: ((memory) Z)),
  forall (Post17: intP0 = (upd intP caduceus_19 aux_4)),
  (forall (result:pointer),
   (result = (shift (acc VC Parametre) 1) ->
    ((((forall (result0:Z),
        ((((acc intP0 (shift Ch_Pn 1)) = 0 /\ (acc intP0 (shift Pn_Bac 1)) =
         0) /\ (acc intP0 (shift SPMEP 1)) = 0) /\ result0 = 1 \/
         (((acc intP0 (shift Ch_Pn 1)) <> 0 \/ (acc intP0 (shift Ch_Pn 1)) =
         0 /\ (acc intP0 (shift Pn_Bac 1)) <> 0) \/
         ((acc intP0 (shift Ch_Pn 1)) = 0 /\ (acc intP0 (shift Pn_Bac 1)) =
         0) /\ (acc intP0 (shift SPMEP 1)) <> 0) /\ result0 = 0 ->
         (forall (intP:((memory) Z)),
          (intP = (upd intP0 result result0) ->
           (forall (result:pointer),
            (result = (shift (acc VC Parametre) 2) ->
             ((((forall (result0:Z),
                 ((((acc intP (shift Ch_Pn 2)) = 0 /\
                  (acc intP (shift Pn_Bac 2)) = 0) /\
                  (acc intP (shift SPMEP 2)) = 0) /\ result0 = 1 \/
                  (((acc intP (shift Ch_Pn 2)) <> 0 \/
                  (acc intP (shift Ch_Pn 2)) = 0 /\
                  (acc intP (shift Pn_Bac 2)) <> 0) \/
                  ((acc intP (shift Ch_Pn 2)) = 0 /\
                  (acc intP (shift Pn_Bac 2)) = 0) /\
                  (acc intP (shift SPMEP 2)) <> 0) /\ result0 = 0 ->
                  (forall (intP0:((memory) Z)),
                   (intP0 = (upd intP result result0) ->
                    (forall (result:pointer),
                     (result = (shift (acc VC Parametre) 3) ->
                      ((forall (result0:Z),
                        (((acc Param4_Pn Parametre) = 0 /\
                         (acc intP0 (shift Pn_Bac 3)) = 0) /\ result0 = 1 \/
                         ((acc Param4_Pn Parametre) <> 0 \/
                         (acc Param4_Pn Parametre) = 0 /\
                         (acc intP0 (shift Pn_Bac 3)) <> 0) /\ result0 = 0 ->
                         (forall (intP:((memory) Z)),
                          (intP = (upd intP0 result result0) -> True)) /\
                         (valid alloc result))) /\
                      (valid alloc Parametre)) /\
                      (((acc Param4_Pn Parametre) = 0 ->
                        (valid alloc (shift Pn_Bac 3)) /\
                        (valid alloc (shift Pn_Bac 3)))))) /\
                    (valid alloc Parametre))) /\
                  (valid alloc result))) /\
             (valid alloc (shift Ch_Pn 2))) /\
             (valid alloc (shift Ch_Pn 2))) /\
             (((acc intP (shift Ch_Pn 2)) = 0 ->
               (valid alloc (shift Pn_Bac 2)) /\
               (valid alloc (shift Pn_Bac 2))))) /\
             (((acc intP (shift Ch_Pn 2)) = 0 /\
               (acc intP (shift Pn_Bac 2)) = 0 ->
               (valid alloc (shift SPMEP 2)) /\ (valid alloc (shift SPMEP 2)))))) /\
           (valid alloc Parametre))) /\
         (valid alloc result))) /\
    (valid alloc (shift Ch_Pn 1))) /\ (valid alloc (shift Ch_Pn 1))) /\
    (((acc intP0 (shift Ch_Pn 1)) = 0 -> (valid alloc (shift Pn_Bac 1)) /\
      (valid alloc (shift Pn_Bac 1))))) /\
    (((acc intP0 (shift Ch_Pn 1)) = 0 /\ (acc intP0 (shift Pn_Bac 1)) = 0 ->
      (valid alloc (shift SPMEP 1)) /\ (valid alloc (shift SPMEP 1)))))) /\
  (valid alloc Parametre).
Proof.
Admitted.



