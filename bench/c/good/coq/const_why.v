(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/const.why", characters 594-671 *)
Lemma f_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (c: Z),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre3: (separation_w_x alloc z x_0 t1 t2 w) /\
                (separation_w_t alloc t t1 t2 w) /\ (constant_c c) /\
                (separation_intern_w alloc t1 t2 w) /\
                (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                (constant_x alloc x y z x_0 intP) /\
                (constant_t alloc t intP)),
  (valid alloc (shift t 2)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 35-701 *)
Lemma f_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (c: Z),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre3: (separation_w_x alloc z x_0 t1 t2 w) /\
                (separation_w_t alloc t t1 t2 w) /\ (constant_c c) /\
                (separation_intern_w alloc t1 t2 w) /\
                (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                (constant_x alloc x y z x_0 intP) /\
                (constant_t alloc t intP)),
  forall (Pre2: (valid alloc (shift t 2))),
  forall (result: Z),
  forall (Post1: result = (c + (acc intP (shift t 2)))),
  result = 8.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 1242-1314 *)
Lemma g_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre4: (separation_w_x alloc z x_0 t1 t2 w) /\
                (separation_w_t alloc t t1 t2 w) /\
                (separation_intern_w alloc t1 t2 w) /\
                (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                (constant_x alloc x y z x_0 intP) /\
                (constant_t alloc t intP)),
  (valid alloc x_0).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 1242-1314 *)
Lemma g_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre4: (separation_w_x alloc z x_0 t1 t2 w) /\
                (separation_w_t alloc t t1 t2 w) /\
                (separation_intern_w alloc t1 t2 w) /\
                (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                (constant_x alloc x y z x_0 intP) /\
                (constant_t alloc t intP)),
  forall (Pre1: (valid alloc x_0)),
  (valid alloc (shift (acc z x_0) 2)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 739-1344 *)
Lemma g_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre4: (separation_w_x alloc z x_0 t1 t2 w) /\
                (separation_w_t alloc t t1 t2 w) /\
                (separation_intern_w alloc t1 t2 w) /\
                (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                (constant_x alloc x y z x_0 intP) /\
                (constant_t alloc t intP)),
  forall (Pre1: (valid alloc x_0)),
  forall (Pre3: (valid alloc (shift (acc z x_0) 2))),
  forall (result: Z),
  forall (Post1: result = (acc intP (shift (acc z x_0) 2))),
  result = 3.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 1462-1478 *)
Lemma h_impl_po_1 : 
  forall (U_y: ((memory) Z)),
  forall (alloc: alloc_table),
  forall (y_0: pointer),
  forall (Pre2: (valid_y alloc y_0) /\ (constant_y alloc U_y y_0)),
  (valid alloc y_0).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 1382-1506 *)
Lemma h_impl_po_2 : 
  forall (U_y: ((memory) Z)),
  forall (alloc: alloc_table),
  forall (y_0: pointer),
  forall (Pre2: (valid_y alloc y_0) /\ (constant_y alloc U_y y_0)),
  forall (Pre1: (valid alloc y_0)),
  forall (result: Z),
  forall (Post1: result = (acc U_y y_0)),
  result = 2.
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 2064-2141 *)
Lemma i_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre12: (separation_w_x alloc z x_0 t1 t2 w) /\
                 (separation_w_t alloc t t1 t2 w) /\
                 (separation_intern_w alloc t1 t2 w) /\
                 (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                 (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                 (constant_x alloc x y z x_0 intP) /\
                 (constant_t alloc t intP)),
  (valid alloc w).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 2149-2176 *)
Lemma i_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre12: (separation_w_x alloc z x_0 t1 t2 w) /\
                 (separation_w_t alloc t t1 t2 w) /\
                 (separation_intern_w alloc t1 t2 w) /\
                 (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                 (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                 (constant_x alloc x y z x_0 intP) /\
                 (constant_t alloc t intP)),
  forall (Pre4: (valid alloc w)),
  forall (caduceus_5: pointer),
  forall (Post3: caduceus_5 = (shift (acc t1 w) 0)),
  (valid alloc caduceus_5).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 2047-2176 *)
Lemma i_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (z: ((memory) pointer)),
  forall (Pre12: (separation_w_x alloc z x_0 t1 t2 w) /\
                 (separation_w_t alloc t t1 t2 w) /\
                 (separation_intern_w alloc t1 t2 w) /\
                 (separation_x_t alloc t z x_0) /\ (valid_x alloc z x_0) /\
                 (valid_w alloc t1 t2 w) /\ (valid_t alloc t) /\
                 (constant_x alloc x y z x_0 intP) /\
                 (constant_t alloc t intP)),
  forall (Pre4: (valid alloc w)),
  forall (caduceus_5: pointer),
  forall (Post3: caduceus_5 = (shift (acc t1 w) 0)),
  forall (Pre3: (valid alloc caduceus_5)),
  forall (intP0: ((memory) Z)),
  forall (Post8: intP0 = (upd intP caduceus_5 1)),
  (forall (result:pointer),
   (result = (shift (acc t2 w) 0) ->
    (forall (intP:((memory) Z)),
     (intP = (upd intP0 result 2) ->
      (((forall (result:Z),
         (result = (acc intP (shift (acc t1 w) 0)) -> result = 1 /\
          (constant_x alloc x y z x_0 intP) /\ (constant_t alloc t intP))) /\
      (valid alloc w)) /\ (valid alloc (shift (acc t1 w) 0))) /\
      (valid alloc (shift (acc t1 w) 0)))) /\
    (valid alloc result))) /\
  (valid alloc w).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 3372-3400 *)
Lemma invariants_initially_established_impl_po_1 : 
  forall (U_y: ((memory) Z)),
  forall (alloc: alloc_table),
  forall (c: Z),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (y_0: pointer),
  forall (z: ((memory) pointer)),
  forall (Pre49: (separation_w_x alloc z x_0 t1 t2 w) /\
                 (separation_w_t alloc t t1 t2 w) /\ (constant_c c) /\
                 (separation_intern_w alloc t1 t2 w) /\
                 (separation_x_t alloc t z x_0) /\ (valid_y alloc y_0) /\
                 (valid_x alloc z x_0) /\ (valid_w alloc t1 t2 w) /\
                 (valid_t alloc t) /\ (constant_y alloc U_y y_0) /\
                 (constant_x alloc x y z x_0 intP) /\
                 (constant_t alloc t intP)),
  forall (c0: Z),
  forall (Post1: c0 = 5),
  forall (caduceus_20: pointer),
  forall (Post4: caduceus_20 = (shift t 0)),
  (valid alloc caduceus_20).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/const.why", characters 3335-3400 *)
Lemma invariants_initially_established_impl_po_2 : 
  forall (U_x: ((memory) Z)),
  forall (U_y: ((memory) Z)),
  forall (alloc: alloc_table),
  forall (c: Z),
  forall (intP: ((memory) Z)),
  forall (t: pointer),
  forall (t1: ((memory) pointer)),
  forall (t2: ((memory) pointer)),
  forall (w: pointer),
  forall (x: ((memory) Z)),
  forall (x_0: pointer),
  forall (y: ((memory) Z)),
  forall (y_0: pointer),
  forall (z: ((memory) pointer)),
  forall (Pre49: (separation_w_x alloc z x_0 t1 t2 w) /\
                 (separation_w_t alloc t t1 t2 w) /\ (constant_c c) /\
                 (separation_intern_w alloc t1 t2 w) /\
                 (separation_x_t alloc t z x_0) /\ (valid_y alloc y_0) /\
                 (valid_x alloc z x_0) /\ (valid_w alloc t1 t2 w) /\
                 (valid_t alloc t) /\ (constant_y alloc U_y y_0) /\
                 (constant_x alloc x y z x_0 intP) /\
                 (constant_t alloc t intP)),
  forall (c0: Z),
  forall (Post1: c0 = 5),
  forall (caduceus_20: pointer),
  forall (Post4: caduceus_20 = (shift t 0)),
  forall (Pre3: (valid alloc caduceus_20)),
  forall (intP0: ((memory) Z)),
  forall (Post44: intP0 = (upd intP caduceus_20 1)),
  (forall (result:pointer),
   (result = (shift t 1) ->
    (forall (intP:((memory) Z)),
     (intP = (upd intP0 result 2) ->
      (forall (result:pointer),
       (result = (shift t 2) ->
        (forall (intP0:((memory) Z)),
         (intP0 = (upd intP result 3) ->
          (forall (result:pointer),
           (result = (shift t 3) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP0 result 4) ->
              (forall (result:pointer),
               (result = x_0 ->
                (forall (x0:((memory) Z)),
                 (x0 = (upd x result 5) ->
                  (forall (result:pointer),
                   (result = x_0 ->
                    (forall (y0:((memory) Z)),
                     (y0 = (upd y result 6) ->
                      (forall (result:pointer),
                       (result = (shift (acc z x_0) 0) ->
                        (forall (intP0:((memory) Z)),
                         (intP0 = (upd intP result 1) ->
                          (forall (result:pointer),
                           (result = (shift (acc z x_0) 1) ->
                            (forall (intP:((memory) Z)),
                             (intP = (upd intP0 result 2) ->
                              (forall (result:pointer),
                               (result = (shift (acc z x_0) 2) ->
                                (forall (intP0:((memory) Z)),
                                 (intP0 = (upd intP result 3) ->
                                  (forall (result:pointer),
                                   (result = y_0 ->
                                    (forall (U_x0:((memory) Z)),
                                     (U_x0 = (upd U_x result 1) ->
                                      (forall (result:pointer),
                                       (result = y_0 ->
                                        (forall (U_y0:((memory) Z)),
                                         (U_y0 = (upd U_y result 2) ->
                                          (forall (result:pointer),
                                           (result = (shift (acc t1 w) 0) ->
                                            (forall (intP:((memory) Z)),
                                             (intP = (upd intP0 result 1) ->
                                              (forall (result:pointer),
                                               (result = (shift (acc t1 w) 1) ->
                                                (forall (intP0:((memory) Z)),
                                                 (intP0 = (upd intP result 2) ->
                                                  (forall (result:pointer),
                                                   (result = (shift (
                                                              acc t2 w) 0) ->
                                                    (forall (intP:((memory) Z)),
                                                     (intP = (upd intP0
                                                              result 3) ->
                                                      True)) /\
                                                    (valid alloc result))) /\
                                                  (valid alloc w))) /\
                                                (valid alloc result))) /\
                                              (valid alloc w))) /\
                                            (valid alloc result))) /\
                                          (valid alloc w))) /\
                                        (valid alloc result))))) /\
                                    (valid alloc result))))) /\
                                (valid alloc result))) /\
                              (valid alloc x_0))) /\
                            (valid alloc result))) /\
                          (valid alloc x_0))) /\
                        (valid alloc result))) /\
                      (valid alloc x_0))) /\
                    (valid alloc result))))) /\
                (valid alloc result))))) /\
            (valid alloc result))))) /\
        (valid alloc result))))) /\
    (valid alloc result))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

