(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/ifs.why", characters 430-1137 *)
Lemma V4A_impl_po_1 : 
  forall (Parametre: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (Pre35: (valid alloc Parametre) /\
                 (separation_SPMEP_Ch_Pn SPMEP Ch_Pn) /\
                 (valid_Ch_Pn Ch_Pn alloc) /\ (valid_SPMEP SPMEP alloc)),
  forall (Pre9: (valid alloc Parametre)),
  forall (caduceus_19: pointer),
  forall (Post4: caduceus_19 = (shift (acc VC Parametre) 0)),
  (valid alloc (shift Ch_Pn 0)).
Proof.
unfold valid_Ch_Pn .
intuition.
Save.

(* Why obligation from file "why/ifs.why", characters 430-1137 *)
Lemma V4A_impl_po_2 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\
                 (separation_SPMEP_Ch_Pn SPMEP Ch_Pn) /\
                 (valid_Ch_Pn Ch_Pn alloc) /\ (valid_SPMEP SPMEP alloc)),
  forall (Pre9: (valid alloc Parametre)),
  forall (caduceus_19: pointer),
  forall (Post4: caduceus_19 = (shift (acc VC Parametre) 0)),
  forall (Pre4: (valid alloc (shift Ch_Pn 0))),
  ((acc intP (shift Ch_Pn 0)) = 0 -> (valid alloc (shift Pn_Bac 0)) /\
   (valid alloc (shift Pn_Bac 0))).
Proof.
intuition.
Admitted.

(* Why obligation from file "why/ifs.why", characters 430-1137 *)
Lemma V4A_impl_po_3 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\
                 (separation_SPMEP_Ch_Pn SPMEP Ch_Pn) /\
                 (valid_Ch_Pn Ch_Pn alloc) /\ (valid_SPMEP SPMEP alloc)),
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
unfold valid_SPMEP.
intuition.
Save.

(* Why obligation from file "why/ifs.why", characters 403-1138 *)
Lemma V4A_impl_po_4 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\
                 (separation_SPMEP_Ch_Pn SPMEP Ch_Pn) /\
                 (valid_Ch_Pn Ch_Pn alloc) /\ (valid_SPMEP SPMEP alloc)),
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
intuition; subst; auto.
Admitted.

(* Why obligation from file "why/ifs.why", characters 403-1138 *)
Lemma V4A_impl_po_5 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (Param4_Pn: ((memory) Z)),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre35: (valid alloc Parametre) /\
                 (separation_SPMEP_Ch_Pn SPMEP Ch_Pn) /\
                 (valid_Ch_Pn Ch_Pn alloc) /\ (valid_SPMEP SPMEP alloc)),
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

(* Why obligation from file "why/ifs.why", characters 3716-3743 *)
Lemma invariants_initially_established_impl_po_1 : 
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (alloc: alloc_table),
  forall (Pre25: (separation_SPMEP_Ch_Pn SPMEP Ch_Pn) /\
                 (valid_Ch_Pn Ch_Pn alloc) /\ (valid_SPMEP SPMEP alloc)),
  forall (caduceus_8: pointer),
  forall (Post3: caduceus_8 = (shift Ch_Pn 0)),
  (valid alloc caduceus_8).
Proof.
intuition.
subst.
red in H1.
apply valid_range_valid_shift with 0 3;auto;omega.
Save.

(* Why obligation from file "why/ifs.why", characters 3676-3743 *)
Lemma invariants_initially_established_impl_po_2 : 
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre25: (separation_SPMEP_Ch_Pn SPMEP Ch_Pn) /\
                 (valid_Ch_Pn Ch_Pn alloc) /\ (valid_SPMEP SPMEP alloc)),
  forall (caduceus_8: pointer),
  forall (Post3: caduceus_8 = (shift Ch_Pn 0)),
  forall (Pre3: (valid alloc caduceus_8)),
  forall (intP0: ((memory) Z)),
  forall (Post25: intP0 = (upd intP caduceus_8 0)),
  (forall (result:pointer),
   (result = (shift Ch_Pn 1) ->
    (forall (intP:((memory) Z)),
     (intP = (upd intP0 result 0) ->
      (forall (result:pointer),
       (result = (shift Ch_Pn 2) ->
        (forall (intP0:((memory) Z)),
         (intP0 = (upd intP result 0) ->
          (forall (result:pointer),
           (result = (shift Ch_Pn 3) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP0 result 0) ->
              (forall (result:pointer),
               (result = (shift SPMEP 0) ->
                (forall (intP0:((memory) Z)),
                 (intP0 = (upd intP result 0) ->
                  (forall (result:pointer),
                   (result = (shift SPMEP 1) ->
                    (forall (intP:((memory) Z)),
                     (intP = (upd intP0 result 0) ->
                      (forall (result:pointer),
                       (result = (shift SPMEP 2) ->
                        (forall (intP0:((memory) Z)),
                         (intP0 = (upd intP result 0) ->
                          (forall (result:pointer),
                           (result = (shift SPMEP 3) ->
                            (forall (intP:((memory) Z)),
                             (intP = (upd intP0 result 0) -> True)) /\
                            (valid alloc result))))) /\
                        (valid alloc result))))) /\
                    (valid alloc result))))) /\
                (valid alloc result))))) /\
            (valid alloc result))))) /\
        (valid alloc result))))) /\
    (valid alloc result))).
Proof.
intuition;
subst;
red in H2;red in H1;apply valid_range_valid_shift with 0 3;auto;omega.
Save.

