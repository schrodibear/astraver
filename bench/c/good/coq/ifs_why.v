(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export ifs_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma V4A_impl_po_1 : 
  forall (A783:Set), forall (A784:Set),
  forall (Parametre: ((pointer) A783)),
  forall (Pn_Bac: ((pointer) A784)),
  forall (Ch_Pn: ((pointer) Ch_Pn_15)),
  forall (SPMEP: ((pointer) SPMEP_16)),
  forall (VC_Parametre_17: ((memory) ((pointer) VC_1) A783)),
  forall (alloc: alloc_table),
  forall (HW_1: (* File "ifs.c", line 16, characters 14-61 *)
                ((valid alloc Parametre) /\ (valid_range alloc Pn_Bac 0 4)) /\
                (valid_range alloc Ch_Pn 0 3) /\
                (valid_range alloc SPMEP 0 3) /\
                (valid1_range VC_Parametre_17 4) /\ (valid1 VC_Parametre_17)),
  (valid alloc Parametre).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.
