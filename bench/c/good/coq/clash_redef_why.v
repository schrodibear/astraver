(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export clash_redef_spec_why.



(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f3_impl_po_1 : 
  forall (p1: ((pointer) Z13)),
  forall (p2_0: ((pointer) Z15)),
  forall (alloc: alloc_table),
  forall (p2_Z13: ((memory) ((pointer) Z15) Z13)),
  forall (HW_1: (* File "clash_redef.c", line 7, characters 14-24 *)
                (valid alloc p1)),
  forall (p2_Z13_0: ((memory) ((pointer) Z15) Z13)),
  forall (HW_2: p2_Z13_0 = (upd p2_Z13 p1 p2_0)),
  (* File "clash_redef.c", line 8, characters 13-25 *) 0 = 0.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f3_impl_po_2 : 
  forall (p1: ((pointer) Z13)),
  forall (p2_0: ((pointer) Z15)),
  forall (alloc: alloc_table),
  forall (p2_Z13: ((memory) ((pointer) Z15) Z13)),
  forall (HW_1: (* File "clash_redef.c", line 7, characters 14-24 *)
                (valid alloc p1)),
  forall (HW_3: (forall (p2_Z13_0:((memory) ((pointer) Z15) Z13)),
                 (p2_Z13_0 = (upd p2_Z13 p1 p2_0) ->
                  (* File "clash_redef.c", line 8, characters 13-25 *) 0 = 0))),
  (valid alloc p1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

