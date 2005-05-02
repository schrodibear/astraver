(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/ifs.why", characters 886-906 *)
Lemma V4A_impl_po_1 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (Pre34: ((valid alloc Parametre) /\
                 (valid_range alloc Pn_Bac 0 4)) /\ (separation2 VC VC) /\
                 (valid_range alloc Ch_Pn 0 4) /\
                 ~((base_addr SPMEP) = (base_addr Ch_Pn)) /\
                 (valid1_range VC 4) /\
                 (forall (index_0:pointer), (forall (index_1:pointer), True)) /\
                 (forall (index_8:pointer), (forall (index_9:pointer), True)) /\
                 (valid_range alloc SPMEP 0 4) /\ (valid1 VC) /\
                 (forall (index_16:pointer),
                  (forall (index_17:pointer), True))),
  (valid alloc Parametre).
Proof.
intuition.
Save.

(* Why obligation from file "why/ifs.why", characters 941-1432 *)
Lemma V4A_impl_po_2 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (Pre34: ((valid alloc Parametre) /\
                 (valid_range alloc Pn_Bac 0 4)) /\ (separation2 VC VC) /\
                 (valid_range alloc Ch_Pn 0 4) /\
                 ~((base_addr SPMEP) = (base_addr Ch_Pn)) /\
                 (valid1_range VC 4) /\
                 (forall (index_0:pointer), (forall (index_1:pointer), True)) /\
                 (forall (index_8:pointer), (forall (index_9:pointer), True)) /\
                 (valid_range alloc SPMEP 0 4) /\ (valid1 VC) /\
                 (forall (index_16:pointer),
                  (forall (index_17:pointer), True))),
  forall (Pre8: (valid alloc Parametre)),
  forall (caduceus_18: pointer),
  forall (Post4: caduceus_18 = (acc VC Parametre)),
  (valid alloc Ch_Pn).
Proof.
intuition.
Save.

(* Why obligation from file "why/ifs.why", characters 941-1432 *)
Lemma V4A_impl_po_3 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre34: ((valid alloc Parametre) /\
                 (valid_range alloc Pn_Bac 0 4)) /\ (separation2 VC VC) /\
                 (valid_range alloc Ch_Pn 0 4) /\
                 ~((base_addr SPMEP) = (base_addr Ch_Pn)) /\
                 (valid1_range VC 4) /\
                 (forall (index_0:pointer), (forall (index_1:pointer), True)) /\
                 (forall (index_8:pointer), (forall (index_9:pointer), True)) /\
                 (valid_range alloc SPMEP 0 4) /\ (valid1 VC) /\
                 (forall (index_16:pointer),
                  (forall (index_17:pointer), True))),
  forall (Pre8: (valid alloc Parametre)),
  forall (caduceus_18: pointer),
  forall (Post4: caduceus_18 = (acc VC Parametre)),
  forall (Pre3: (valid alloc Ch_Pn)),
  ((acc intP Ch_Pn) = 0 -> (valid alloc Pn_Bac)).
Proof.
intuition;unfold valid_range_SPMEP in H0;
apply valid_range_valid_shift with 0 4;auto;
omega.
Save.

(* Why obligation from file "why/ifs.why", characters 941-1432 *)
Lemma V4A_impl_po_4 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre34: ((valid alloc Parametre) /\
                 (valid_range alloc Pn_Bac 0 4)) /\ (separation2 VC VC) /\
                 (valid_range alloc Ch_Pn 0 4) /\
                 ~((base_addr SPMEP) = (base_addr Ch_Pn)) /\
                 (valid1_range VC 4) /\
                 (forall (index_0:pointer), (forall (index_1:pointer), True)) /\
                 (forall (index_8:pointer), (forall (index_9:pointer), True)) /\
                 (valid_range alloc SPMEP 0 4) /\ (valid1 VC) /\
                 (forall (index_16:pointer),
                  (forall (index_17:pointer), True))),
  forall (Pre8: (valid alloc Parametre)),
  forall (caduceus_18: pointer),
  forall (Post4: caduceus_18 = (acc VC Parametre)),
  forall (Pre3: (valid alloc Ch_Pn)),
  forall (Pre4: ((acc intP Ch_Pn) = 0 -> (valid alloc Pn_Bac))),
  ((acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) = 0 -> (valid alloc SPMEP)).
Proof.
intuition; subst; auto;rewrite shift_zero;auto;
generalize (valid_anonymous_0_CPRE_VC_pointer alloc VC Parametre H);
unfold valid_anonymous_0_CPRE_VC;tauto.
Save.

(* Why obligation from file "why/ifs.why", characters 914-1433 *)
Lemma V4A_impl_po_5 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre34: ((valid alloc Parametre) /\
                 (valid_range alloc Pn_Bac 0 4)) /\ (separation2 VC VC) /\
                 (valid_range alloc Ch_Pn 0 4) /\
                 ~((base_addr SPMEP) = (base_addr Ch_Pn)) /\
                 (valid1_range VC 4) /\
                 (forall (index_0:pointer), (forall (index_1:pointer), True)) /\
                 (forall (index_8:pointer), (forall (index_9:pointer), True)) /\
                 (valid_range alloc SPMEP 0 4) /\ (valid1 VC) /\
                 (forall (index_16:pointer),
                  (forall (index_17:pointer), True))),
  forall (Pre8: (valid alloc Parametre)),
  forall (caduceus_18: pointer),
  forall (Post4: caduceus_18 = (acc VC Parametre)),
  forall (Pre3: (valid alloc Ch_Pn)),
  forall (Pre4: ((acc intP Ch_Pn) = 0 -> (valid alloc Pn_Bac))),
  forall (Pre5: ((acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) = 0 ->
                 (valid alloc SPMEP))),
  forall (aux_1: Z),
  forall (Post3: (((acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) = 0) /\
                 (acc intP SPMEP) = 0) /\ aux_1 = 1 \/ (((acc intP Ch_Pn) <>
                 0 \/ (acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) <> 0) \/
                 ((acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) = 0) /\
                 (acc intP SPMEP) <> 0) /\ aux_1 = 0),
  (valid alloc caduceus_18).
Proof.
intuition;subst;unfold valid1 in H8;intuition.
Save.


(* Why obligation from file "why/ifs.why", characters 914-1433 *)
Lemma V4A_impl_po_6 : 
  forall (Parametre: pointer),
  forall (Pn_Bac: pointer),
  forall (Ch_Pn: pointer),
  forall (Param4_Pn: ((memory) Z)),
  forall (SPMEP: pointer),
  forall (VC: ((memory) pointer)),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre34: ((valid alloc Parametre) /\
                 (valid_range alloc Pn_Bac 0 4)) /\ (separation2 VC VC) /\
                 (valid_range alloc Ch_Pn 0 4) /\
                 ~((base_addr SPMEP) = (base_addr Ch_Pn)) /\
                 (valid1_range VC 4) /\
                 (forall (index_0:pointer), (forall (index_1:pointer), True)) /\
                 (forall (index_8:pointer), (forall (index_9:pointer), True)) /\
                 (valid_range alloc SPMEP 0 4) /\ (valid1 VC) /\
                 (forall (index_16:pointer),
                  (forall (index_17:pointer), True))),
  forall (Pre8: (valid alloc Parametre)),
  forall (caduceus_18: pointer),
  forall (Post4: caduceus_18 = (acc VC Parametre)),
  forall (Pre3: (valid alloc Ch_Pn)),
  forall (Pre4: ((acc intP Ch_Pn) = 0 -> (valid alloc Pn_Bac))),
  forall (Pre5: ((acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) = 0 ->
                 (valid alloc SPMEP))),
  forall (aux_1: Z),
  forall (Post3: (((acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) = 0) /\
                 (acc intP SPMEP) = 0) /\ aux_1 = 1 \/ (((acc intP Ch_Pn) <>
                 0 \/ (acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) <> 0) \/
                 ((acc intP Ch_Pn) = 0 /\ (acc intP Pn_Bac) = 0) /\
                 (acc intP SPMEP) <> 0) /\ aux_1 = 0),
  forall (Pre1: (valid alloc caduceus_18)),
  forall (intP0: ((memory) Z)),
  forall (Post17: intP0 = (upd intP caduceus_18 aux_1)),
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
                          (intP = (upd intP0 result result0) ->
                           (forall (index_0:pointer),
                            (forall (index_1:pointer), True)) /\
                           (forall (index_8:pointer),
                            (forall (index_9:pointer), True)) /\
                           (forall (index_16:pointer),
                            (forall (index_17:pointer), True)))) /\
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
intuition;subst;
unfold valid1_range in H4;
generalize (H4 Parametre alloc H1);
auto with *.
Save.
