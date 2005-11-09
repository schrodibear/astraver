(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (t2: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (x_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z10 t2) = 0)),
  (valid alloc t2).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (t2: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (x_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z10 t2) = 0)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_Z10 t2)),
  (valid alloc t2).
Proof.
intuition; subst; caduceus; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (t2: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (x_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z10 t2) = 0)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_Z10 t2)),
  forall (HW_4: (valid alloc t2)),
  forall (x_Z10_0: ((memory) Z Z10)),
  forall (HW_5: x_Z10_0 = (upd x_Z10 t2 (result + 1))),
  (valid alloc t2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (t2: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (x_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z10 t2) = 0)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_Z10 t2)),
  forall (HW_4: (valid alloc t2)),
  forall (x_Z10_0: ((memory) Z Z10)),
  forall (HW_5: x_Z10_0 = (upd x_Z10 t2 (result + 1))),
  forall (HW_6: (valid alloc t2)),
  forall (result0: Z),
  forall (HW_7: result0 = (acc x_Z10_0 t2)),
  (valid alloc t2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_5 : 
  forall (t2: ((pointer) Z10)),
  forall (alloc: alloc_table),
  forall (x_Z10: ((memory) Z Z10)),
  forall (y_Z10: ((memory) Z Z10)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z10 t2) = 0)),
  forall (HW_2: (valid alloc t2)),
  forall (result: Z),
  forall (HW_3: result = (acc x_Z10 t2)),
  forall (HW_4: (valid alloc t2)),
  forall (x_Z10_0: ((memory) Z Z10)),
  forall (HW_5: x_Z10_0 = (upd x_Z10 t2 (result + 1))),
  forall (HW_6: (valid alloc t2)),
  forall (result0: Z),
  forall (HW_7: result0 = (acc x_Z10_0 t2)),
  forall (HW_8: (valid alloc t2)),
  forall (x_Z10_1: ((memory) Z Z10)),
  forall (HW_9: x_Z10_1 = (upd x_Z10_0 t2 (1 + result0))),
  (* File "struct.c", line 9, characters 13-63 *) ((result0 = 1 /\
  (acc x_Z10_1 t2) = 2) /\ (acc y_Z10 t2) = (acc y_Z10 t2)) /\
  (not_assigns alloc x_Z10 x_Z10_1 (pset_singleton t2)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z13)),
  forall (s: ((pointer) Z13)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z13)),
  forall (HW_3: ps0 = s),
  (valid alloc s).
Proof.
 intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z13)),
  forall (s: ((pointer) Z13)),
  forall (t_Z13: ((memory) ((pointer) Z4) Z13)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z13)),
  forall (HW_3: ps0 = s),
  forall (HW_4: (valid alloc s)),
  forall (result: ((pointer) Z4)),
  forall (HW_5: result = (acc t_Z13 s)),
  forall (p: ((pointer) Z4)),
  forall (HW_6: p = result),
  (valid alloc ps0).
Proof.
 intuition.
subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z13)),
  forall (s: ((pointer) Z13)),
  forall (t_Z13: ((memory) ((pointer) Z4) Z13)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z13)),
  forall (HW_3: ps0 = s),
  forall (HW_4: (valid alloc s)),
  forall (result: ((pointer) Z4)),
  forall (HW_5: result = (acc t_Z13 s)),
  forall (p: ((pointer) Z4)),
  forall (HW_6: p = result),
  forall (HW_7: (valid alloc ps0)),
  forall (result0: ((pointer) Z4)),
  forall (HW_8: result0 = (acc t_Z13 ps0)),
  (valid alloc result0).
Proof.
intuition.
subst;
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z13)),
  forall (s: ((pointer) Z13)),
  forall (t_Z13: ((memory) ((pointer) Z4) Z13)),
  forall (x_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z13)),
  forall (HW_3: ps0 = s),
  forall (HW_4: (valid alloc s)),
  forall (result: ((pointer) Z4)),
  forall (HW_5: result = (acc t_Z13 s)),
  forall (p: ((pointer) Z4)),
  forall (HW_6: p = result),
  forall (HW_7: (valid alloc ps0)),
  forall (result0: ((pointer) Z4)),
  forall (HW_8: result0 = (acc t_Z13 ps0)),
  forall (HW_9: (valid alloc result0)),
  forall (x_Z4_0: ((memory) Z Z4)),
  forall (HW_10: x_Z4_0 = (upd x_Z4 result0 1)),
  (valid alloc s).
Proof.
intuition; subst; auto.
caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z13)),
  forall (s: ((pointer) Z13)),
  forall (t_Z13: ((memory) ((pointer) Z4) Z13)),
  forall (x_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z13)),
  forall (HW_3: ps0 = s),
  forall (HW_4: (valid alloc s)),
  forall (result: ((pointer) Z4)),
  forall (HW_5: result = (acc t_Z13 s)),
  forall (p: ((pointer) Z4)),
  forall (HW_6: p = result),
  forall (HW_7: (valid alloc ps0)),
  forall (result0: ((pointer) Z4)),
  forall (HW_8: result0 = (acc t_Z13 ps0)),
  forall (HW_9: (valid alloc result0)),
  forall (x_Z4_0: ((memory) Z Z4)),
  forall (HW_10: x_Z4_0 = (upd x_Z4 result0 1)),
  forall (HW_11: (valid alloc s)),
  forall (result1: ((pointer) Z4)),
  forall (HW_12: result1 = (acc t_Z13 s)),
  (valid alloc result1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z13)),
  forall (s: ((pointer) Z13)),
  forall (t_Z13: ((memory) ((pointer) Z4) Z13)),
  forall (x_Z4: ((memory) Z Z4)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z13)),
  forall (HW_3: ps0 = s),
  forall (HW_4: (valid alloc s)),
  forall (result: ((pointer) Z4)),
  forall (HW_5: result = (acc t_Z13 s)),
  forall (p: ((pointer) Z4)),
  forall (HW_6: p = result),
  forall (HW_7: (valid alloc ps0)),
  forall (result0: ((pointer) Z4)),
  forall (HW_8: result0 = (acc t_Z13 ps0)),
  forall (HW_9: (valid alloc result0)),
  forall (x_Z4_0: ((memory) Z Z4)),
  forall (HW_10: x_Z4_0 = (upd x_Z4 result0 1)),
  forall (HW_11: (valid alloc s)),
  forall (result1: ((pointer) Z4)),
  forall (HW_12: result1 = (acc t_Z13 s)),
  forall (HW_13: (valid alloc result1)),
  forall (result2: Z),
  forall (HW_14: result2 = (acc x_Z4_0 result1)),
  (* File "struct.c", line 20, characters 13-25 *) result2 = 1.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

