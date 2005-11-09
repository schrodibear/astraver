(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export struct_spec_why.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_1 : 
  forall (t2: ((pointer) Z8)),
  forall (alloc: alloc_table),
  forall (x_Z8: ((memory) Z Z8)),
  forall (y_Z8: ((memory) Z Z8)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z8 t2) = 0)),
  forall (result: Z),
  forall (HW_2: result = (acc x_Z8 t2)),
  forall (x_Z8_0: ((memory) Z Z8)),
  forall (HW_3: x_Z8_0 = (upd x_Z8 t2 (result + 1))),
  forall (result0: Z),
  forall (HW_4: result0 = (acc x_Z8_0 t2)),
  forall (x_Z8_1: ((memory) Z Z8)),
  forall (HW_5: x_Z8_1 = (upd x_Z8_0 t2 (1 + result0))),
  (* File "struct.c", line 9, characters 13-63 *) ((result0 = 1 /\
  (acc x_Z8_1 t2) = 2) /\ (acc y_Z8 t2) = (acc y_Z8 t2)) /\
  (not_assigns alloc x_Z8 x_Z8_1 (pset_singleton t2)).
Proof.
intuition; subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_2 : 
  forall (t2: ((pointer) Z8)),
  forall (alloc: alloc_table),
  forall (x_Z8: ((memory) Z Z8)),
  forall (y_Z8: ((memory) Z Z8)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z8 t2) = 0)),
  forall (result: Z),
  forall (HW_2: result = (acc x_Z8 t2)),
  forall (x_Z8_0: ((memory) Z Z8)),
  forall (HW_3: x_Z8_0 = (upd x_Z8 t2 (result + 1))),
  forall (result0: Z),
  forall (HW_4: result0 = (acc x_Z8_0 t2)),
  forall (HW_6: (forall (x_Z8_1:((memory) Z Z8)),
                 (x_Z8_1 = (upd x_Z8_0 t2 (1 + result0)) ->
                  (* File "struct.c", line 9, characters 13-63 *) ((result0 =
                  1 /\ (acc x_Z8_1 t2) = 2) /\ (acc y_Z8 t2) = (acc y_Z8 t2)) /\
                  (not_assigns alloc x_Z8 x_Z8_1 (pset_singleton t2))))),
  (valid alloc t2).
Proof.
intuition; subst; caduceus; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_3 : 
  forall (t2: ((pointer) Z8)),
  forall (alloc: alloc_table),
  forall (x_Z8: ((memory) Z Z8)),
  forall (y_Z8: ((memory) Z Z8)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z8 t2) = 0)),
  forall (result: Z),
  forall (HW_2: result = (acc x_Z8 t2)),
  forall (x_Z8_0: ((memory) Z Z8)),
  forall (HW_3: x_Z8_0 = (upd x_Z8 t2 (result + 1))),
  forall (HW_7: (forall (result:Z),
                 (result = (acc x_Z8_0 t2) ->
                  (forall (x_Z8_1:((memory) Z Z8)),
                   (x_Z8_1 = (upd x_Z8_0 t2 (1 + result)) ->
                    (* File "struct.c", line 9, characters 13-63 *)
                    ((result = 1 /\ (acc x_Z8_1 t2) = 2) /\ (acc y_Z8 t2) =
                    (acc y_Z8 t2)) /\
                    (not_assigns alloc x_Z8 x_Z8_1 (pset_singleton t2)))) /\
                  (valid alloc t2)))),
  (valid alloc t2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_4 : 
  forall (t2: ((pointer) Z8)),
  forall (alloc: alloc_table),
  forall (x_Z8: ((memory) Z Z8)),
  forall (y_Z8: ((memory) Z Z8)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z8 t2) = 0)),
  forall (result: Z),
  forall (HW_2: result = (acc x_Z8 t2)),
  forall (HW_8: (forall (x_Z8_0:((memory) Z Z8)),
                 (x_Z8_0 = (upd x_Z8 t2 (result + 1)) ->
                  (forall (result:Z),
                   (result = (acc x_Z8_0 t2) ->
                    (forall (x_Z8_1:((memory) Z Z8)),
                     (x_Z8_1 = (upd x_Z8_0 t2 (1 + result)) ->
                      (* File "struct.c", line 9, characters 13-63 *)
                      ((result = 1 /\ (acc x_Z8_1 t2) = 2) /\ (acc y_Z8 t2) =
                      (acc y_Z8 t2)) /\
                      (not_assigns alloc x_Z8 x_Z8_1 (pset_singleton t2)))) /\
                    (valid alloc t2))) /\
                  (valid alloc t2)))),
  (valid alloc t2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma f_impl_po_5 : 
  forall (t2: ((pointer) Z8)),
  forall (alloc: alloc_table),
  forall (x_Z8: ((memory) Z Z8)),
  forall (y_Z8: ((memory) Z Z8)),
  forall (HW_1: (* File "struct.c", line 7, characters 14-38 *)
                ((valid alloc t2) /\ (acc x_Z8 t2) = 0)),
  forall (HW_9: (forall (result:Z),
                 (result = (acc x_Z8 t2) ->
                  (forall (x_Z8_0:((memory) Z Z8)),
                   (x_Z8_0 = (upd x_Z8 t2 (result + 1)) ->
                    (forall (result:Z),
                     (result = (acc x_Z8_0 t2) ->
                      (forall (x_Z8_1:((memory) Z Z8)),
                       (x_Z8_1 = (upd x_Z8_0 t2 (1 + result)) ->
                        (* File "struct.c", line 9, characters 13-63 *)
                        ((result = 1 /\ (acc x_Z8_1 t2) = 2) /\
                        (acc y_Z8 t2) = (acc y_Z8 t2)) /\
                        (not_assigns alloc x_Z8 x_Z8_1 (pset_singleton t2)))) /\
                      (valid alloc t2))) /\
                    (valid alloc t2))) /\
                  (valid alloc t2)))),
  (valid alloc t2).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z11)),
  forall (s: ((pointer) Z11)),
  forall (t_Z11: ((memory) ((pointer) Z2) Z11)),
  forall (x_Z2: ((memory) Z Z2)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z11)),
  forall (HW_3: ps0 = s),
  forall (result: ((pointer) Z2)),
  forall (HW_4: result = (acc t_Z11 s)),
  forall (p: ((pointer) Z2)),
  forall (HW_5: p = result),
  forall (result0: ((pointer) Z2)),
  forall (HW_6: result0 = (acc t_Z11 ps0)),
  forall (x_Z2_0: ((memory) Z Z2)),
  forall (HW_7: x_Z2_0 = (upd x_Z2 result0 1)),
  forall (result1: ((pointer) Z2)),
  forall (HW_8: result1 = (acc t_Z11 s)),
  forall (result2: Z),
  forall (HW_9: result2 = (acc x_Z2_0 result1)),
  (* File "struct.c", line 20, characters 13-25 *) result2 = 1.
Proof.
 intuition.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z11)),
  forall (s: ((pointer) Z11)),
  forall (t_Z11: ((memory) ((pointer) Z2) Z11)),
  forall (x_Z2: ((memory) Z Z2)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z11)),
  forall (HW_3: ps0 = s),
  forall (result: ((pointer) Z2)),
  forall (HW_4: result = (acc t_Z11 s)),
  forall (p: ((pointer) Z2)),
  forall (HW_5: p = result),
  forall (result0: ((pointer) Z2)),
  forall (HW_6: result0 = (acc t_Z11 ps0)),
  forall (x_Z2_0: ((memory) Z Z2)),
  forall (HW_7: x_Z2_0 = (upd x_Z2 result0 1)),
  forall (result1: ((pointer) Z2)),
  forall (HW_8: result1 = (acc t_Z11 s)),
  forall (HW_10: (forall (result:Z),
                  (result = (acc x_Z2_0 result1) ->
                   (* File "struct.c", line 20, characters 13-25 *) result =
                   1))),
  (valid alloc result1).
Proof.
 intuition.
subst; auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z11)),
  forall (s: ((pointer) Z11)),
  forall (t_Z11: ((memory) ((pointer) Z2) Z11)),
  forall (x_Z2: ((memory) Z Z2)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z11)),
  forall (HW_3: ps0 = s),
  forall (result: ((pointer) Z2)),
  forall (HW_4: result = (acc t_Z11 s)),
  forall (p: ((pointer) Z2)),
  forall (HW_5: p = result),
  forall (result0: ((pointer) Z2)),
  forall (HW_6: result0 = (acc t_Z11 ps0)),
  forall (x_Z2_0: ((memory) Z Z2)),
  forall (HW_7: x_Z2_0 = (upd x_Z2 result0 1)),
  forall (HW_11: (forall (result:((pointer) Z2)),
                  (result = (acc t_Z11 s) ->
                   (forall (result0:Z),
                    (result0 = (acc x_Z2_0 result) ->
                     (* File "struct.c", line 20, characters 13-25 *)
                     result0 = 1)) /\
                   (valid alloc result)))),
  (valid alloc s).
Proof.
intuition.
subst;
auto.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_4 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z11)),
  forall (s: ((pointer) Z11)),
  forall (t_Z11: ((memory) ((pointer) Z2) Z11)),
  forall (x_Z2: ((memory) Z Z2)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z11)),
  forall (HW_3: ps0 = s),
  forall (result: ((pointer) Z2)),
  forall (HW_4: result = (acc t_Z11 s)),
  forall (p: ((pointer) Z2)),
  forall (HW_5: p = result),
  forall (result0: ((pointer) Z2)),
  forall (HW_6: result0 = (acc t_Z11 ps0)),
  forall (HW_12: (forall (x_Z2_0:((memory) Z Z2)),
                  (x_Z2_0 = (upd x_Z2 result0 1) ->
                   (forall (result:((pointer) Z2)),
                    (result = (acc t_Z11 s) ->
                     (forall (result0:Z),
                      (result0 = (acc x_Z2_0 result) ->
                       (* File "struct.c", line 20, characters 13-25 *)
                       result0 = 1)) /\
                     (valid alloc result))) /\
                   (valid alloc s)))),
  (valid alloc result0).
Proof.
intuition; subst; auto.
caduceus.
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_5 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z11)),
  forall (s: ((pointer) Z11)),
  forall (t_Z11: ((memory) ((pointer) Z2) Z11)),
  forall (x_Z2: ((memory) Z Z2)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z11)),
  forall (HW_3: ps0 = s),
  forall (result: ((pointer) Z2)),
  forall (HW_4: result = (acc t_Z11 s)),
  forall (p: ((pointer) Z2)),
  forall (HW_5: p = result),
  forall (HW_13: (forall (result:((pointer) Z2)),
                  (result = (acc t_Z11 ps0) ->
                   (forall (x_Z2_0:((memory) Z Z2)),
                    (x_Z2_0 = (upd x_Z2 result 1) ->
                     (forall (result:((pointer) Z2)),
                      (result = (acc t_Z11 s) ->
                       (forall (result0:Z),
                        (result0 = (acc x_Z2_0 result) ->
                         (* File "struct.c", line 20, characters 13-25 *)
                         result0 = 1)) /\
                       (valid alloc result))) /\
                     (valid alloc s))) /\
                   (valid alloc result)))),
  (valid alloc ps0).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "", line 0, characters 0-0: *)
(*Why goal*) Lemma g_impl_po_6 : 
  forall (alloc: alloc_table),
  forall (ps: ((pointer) Z11)),
  forall (s: ((pointer) Z11)),
  forall (t_Z11: ((memory) ((pointer) Z2) Z11)),
  forall (x_Z2: ((memory) Z Z2)),
  forall (HW_1: (* File "struct.c", line 19, characters 14-24 *)
                (valid alloc ps) /\ (valid_range alloc s 0 0)),
  forall (ps0: ((pointer) Z11)),
  forall (HW_3: ps0 = s),
  forall (HW_14: (forall (result:((pointer) Z2)),
                  (result = (acc t_Z11 s) ->
                   (forall (p:((pointer) Z2)),
                    (p = result ->
                     (forall (result:((pointer) Z2)),
                      (result = (acc t_Z11 ps0) ->
                       (forall (x_Z2_0:((memory) Z Z2)),
                        (x_Z2_0 = (upd x_Z2 result 1) ->
                         (forall (result:((pointer) Z2)),
                          (result = (acc t_Z11 s) ->
                           (forall (result0:Z),
                            (result0 = (acc x_Z2_0 result) ->
                             (* File "struct.c", line 20, characters 13-25 *)
                             result0 = 1)) /\
                           (valid alloc result))) /\
                         (valid alloc s))) /\
                       (valid alloc result))) /\
                     (valid alloc ps0)))))),
  (valid alloc s).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

