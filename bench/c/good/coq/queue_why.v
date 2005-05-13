(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export queue_spec_why.

(* Why obligation from file "why/queue.why", characters 224-252 *)
Lemma invariants_initially_established_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre34: (valid_range alloc t 0 5) /\ (valid_range alloc q 0 1) /\
                 ~((base_addr q) = (base_addr t))),
  forall (caduceus_11: pointer),
  forall (Post3: caduceus_11 = t),
  (valid alloc caduceus_11).
Proof.
intuition.
subst.
auto.
Save.

(* Why obligation from file "why/queue.why", characters 200-252 *)
Lemma invariants_initially_established_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (intP: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre34: (valid_range alloc t 0 5) /\ (valid_range alloc q 0 1) /\
                 ~((base_addr q) = (base_addr t))),
  forall (caduceus_11: pointer),
  forall (Post3: caduceus_11 = t),
  forall (Pre3: (valid alloc caduceus_11)),
  forall (intP0: ((memory) Z)),
  forall (Post34: intP0 = (upd intP caduceus_11 0)),
  (forall (result:pointer),
   (result = (shift t 1) ->
    (forall (intP:((memory) Z)),
     (intP = (upd intP0 result 0) ->
      (forall (result:pointer),
       (result = (shift t 2) ->
        (forall (intP0:((memory) Z)),
         (intP0 = (upd intP result 0) ->
          (forall (result:pointer),
           (result = (shift t 3) ->
            (forall (intP:((memory) Z)),
             (intP = (upd intP0 result 0) ->
              (forall (result:pointer),
               (result = (shift t 4) ->
                (forall (intP0:((memory) Z)),
                 (intP0 = (upd intP result 0) ->
                  (forall (result:pointer),
                   (result = q ->
                    (forall (contents0:((memory) pointer)),
                     (contents0 = (upd contents result t) ->
                      (forall (result:pointer),
                       (result = q ->
                        (forall (length0:((memory) Z)),
                         (length0 = (upd length result 5) ->
                          (forall (result:pointer),
                           (result = q ->
                            (forall (first0:((memory) Z)),
                             (first0 = (upd first result 0) ->
                              (forall (result:pointer),
                               (result = q ->
                                (forall (last0:((memory) Z)),
                                 (last0 = (upd last result 0) ->
                                  (forall (result:pointer),
                                   (result = q ->
                                    (forall (empty0:((memory) Z)),
                                     (empty0 = (upd empty result 0) ->
                                      (forall (result:pointer),
                                       (result = q ->
                                        (forall (full0:((memory) Z)),
                                         (full0 = (upd full result 1) ->
                                          ((valid_range alloc
                                            (acc contents0 q) 0
                                            ((acc length0 q) - 1)) /\
                                          0 <= (acc first0 q) /\
                                          (acc first0 q) <
                                          (acc length0 q)) /\ 0 <=
                                          (acc last0 q) /\ (acc last0 q) <
                                          (acc length0 q))) /\
                                        (valid alloc result))))) /\
                                    (valid alloc result))))) /\
                                (valid alloc result))))) /\
                            (valid alloc result))))) /\
                        (valid alloc result))))) /\
                    (valid alloc result))))) /\
                (valid alloc result))))) /\
            (valid alloc result))))) /\
        (valid alloc result))))) /\
    (valid alloc result))).
Proof.
intuition;subst;auto;
caduceus;unfold valid_range in *|- *;intuition.
Save.


(* Why obligation from file "why/queue.why", characters 1568-1587 *)
Lemma pop_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre23: ((acc empty q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (valid_range alloc q 0 1)),
  (valid alloc q).
Proof.
intuition.
Save.

(* Why obligation from file "why/queue.why", characters 1720-1743 *)
Lemma pop_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre23: ((acc empty q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (valid_range alloc q 0 1)),
  forall (Pre5: (valid alloc q)),
  forall (caduceus_1: pointer),
  forall (Post21: caduceus_1 = (acc contents q)),
  forall (caduceus1: pointer),
  forall (Post20: caduceus1 = q),
  (valid alloc caduceus1).
Proof.
intuition.
subst;auto.
Save.


(* Why obligation from file "why/queue.why", characters 1793-2048 *)
Lemma pop_impl_po_3 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (intP: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre23: ((acc empty q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (valid_range alloc q 0 1)),
  forall (Pre5: (valid alloc q)),
  forall (caduceus_1: pointer),
  forall (Post21: caduceus_1 = (acc contents q)),
  forall (caduceus1: pointer),
  forall (Post20: caduceus1 = q),
  forall (Pre4: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post19: caduceus2 = (acc first caduceus1)),
  forall (Pre3: (valid alloc caduceus1)),
  forall (first0: ((memory) Z)),
  forall (Post24: first0 = (upd first caduceus1 (1 + caduceus2))),
  forall (result0: Z),
  forall (Post18: result0 = caduceus2),
  (forall (result:pointer),
   (result = (shift caduceus_1 result0) ->
    ((forall (result0:Z),
      (result0 = (acc intP result) ->
       (((((acc first0 q) = (acc length q) ->
           (forall (result:pointer),
            (result = q ->
             (forall (first1:((memory) Z)),
              (first1 = (upd first0 result 0) ->
               (forall (result:pointer),
                (result = q ->
                 (forall (full0:((memory) Z)),
                  (full0 = (upd full result 0) ->
                   (forall (result:pointer),
                    (result = q ->
                     ((forall (result1:Z),
                       ((acc first1 q) = (acc last q) /\ result1 = 1 \/
                        (acc first1 q) <> (acc last q) /\ result1 = 0 ->
                        (forall (empty0:((memory) Z)),
                         (empty0 = (upd empty result result1) ->
                          (forall (result:Z),
                           (result = result0 -> ((acc full0 q) = 0 /\
                            result =
                            (acc intP (shift (acc contents q) (acc first q)))) /\
                            (((not_assigns alloc full full0
                               (pset_singleton q)) /\
                            (not_assigns alloc first first1
                             (pset_singleton q))) /\
                            (not_assigns alloc empty empty0
                             (pset_singleton q))) /\
                            ((valid_range alloc (acc contents q) 0
                              ((acc length q) - 1)) /\
                            0 <= (acc first1 q) /\ (acc first1 q) <
                            (acc length q)) /\ 0 <= (acc last q) /\
                            (acc last q) < (acc length q))))) /\
                        (valid alloc result))) /\
                     (valid alloc q)) /\ (valid alloc q))))) /\
                 (valid alloc result))))) /\
             (valid alloc result))))) /\
       (((acc first0 q) <> (acc length q) ->
         (forall (result:unit),
          (result = tt ->
           (forall (result:pointer),
            (result = q ->
             (forall (full0:((memory) Z)),
              (full0 = (upd full result 0) ->
               (forall (result:pointer),
                (result = q ->
                 ((forall (result1:Z),
                   ((acc first0 q) = (acc last q) /\ result1 = 1 \/
                    (acc first0 q) <> (acc last q) /\ result1 = 0 ->
                    (forall (empty0:((memory) Z)),
                     (empty0 = (upd empty result result1) ->
                      (forall (result:Z),
                       (result = result0 -> ((acc full0 q) = 0 /\ result =
                        (acc intP (shift (acc contents q) (acc first q)))) /\
                        (((not_assigns alloc full full0 (pset_singleton q)) /\
                        (not_assigns alloc first first0 (pset_singleton q))) /\
                        (not_assigns alloc empty empty0 (pset_singleton q))) /\
                        ((valid_range alloc (acc contents q) 0
                          ((acc length q) - 1)) /\
                        0 <= (acc first0 q) /\ (acc first0 q) <
                        (acc length q)) /\ 0 <= (acc last q) /\
                        (acc last q) < (acc length q))))) /\
                    (valid alloc result))) /\
                 (valid alloc q)) /\ (valid alloc q))))) /\
             (valid alloc result)))))))) /\
       (valid alloc q)) /\ (valid alloc q))) /\
    (valid alloc result)) /\ (valid alloc result))).
Proof.
intuition;subst;auto;caduceus.
rewrite acc_upd_eq in H8;auto.
omega.
Save.

(* Why obligation from file "why/queue.why", characters 3671-3690 *)
Lemma push_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre23: ((acc full q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (valid_range alloc q 0 1)),
  (valid alloc q).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/queue.why", characters 3815-3837 *)
Lemma push_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre23: ((acc full q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (valid_range alloc q 0 1)),
  forall (Pre5: (valid alloc q)),
  forall (caduceus_6: pointer),
  forall (Post9: caduceus_6 = (acc contents q)),
  forall (caduceus1: pointer),
  forall (Post8: caduceus1 = q),
  (valid alloc caduceus1).
Proof.
intuition.
subst;auto.
Save.

(* Why obligation from file "why/queue.why", characters 3883-4076 *)
Lemma push_impl_po_3 : 
  forall (c: Z),
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (intP: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre23: ((acc full q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (valid_range alloc q 0 1)),
  forall (Pre5: (valid alloc q)),
  forall (caduceus_6: pointer),
  forall (Post9: caduceus_6 = (acc contents q)),
  forall (caduceus1: pointer),
  forall (Post8: caduceus1 = q),
  forall (Pre4: (valid alloc caduceus1)),
  forall (caduceus2: Z),
  forall (Post7: caduceus2 = (acc last caduceus1)),
  forall (Pre3: (valid alloc caduceus1)),
  forall (last0: ((memory) Z)),
  forall (Post23: last0 = (upd last caduceus1 (1 + caduceus2))),
  forall (result0: Z),
  forall (Post6: result0 = caduceus2),
  (forall (result:pointer),
   (result = (shift caduceus_6 result0) ->
    (forall (intP0:((memory) Z)),
     (intP0 = (upd intP result c) ->
      (((((acc last0 q) = (acc length q) ->
          (forall (result:pointer),
           (result = q ->
            (forall (last1:((memory) Z)),
             (last1 = (upd last0 result 0) ->
              (forall (result:pointer),
               (result = q ->
                (forall (empty0:((memory) Z)),
                 (empty0 = (upd empty result 0) ->
                  (forall (result:pointer),
                   (result = q ->
                    ((forall (result0:Z),
                      ((acc first q) = (acc last1 q) /\ result0 = 1 \/
                       (acc first q) <> (acc last1 q) /\ result0 = 0 ->
                       (forall (full0:((memory) Z)),
                        (full0 = (upd full result result0) ->
                         ((acc empty0 q) = 0 /\
                         (acc intP0 (shift (acc contents q) (acc last q))) =
                         c) /\
                         ((((not_assigns alloc last last1 (pset_singleton q)) /\
                         (not_assigns alloc intP intP0
                          (pset_singleton (shift (acc contents q)
                                           (acc last q))))) /\
                         (not_assigns alloc full full0 (pset_singleton q))) /\
                         (not_assigns alloc empty empty0 (pset_singleton q))) /\
                         ((valid_range alloc (acc contents q) 0
                           ((acc length q) - 1)) /\
                         0 <= (acc first q) /\ (acc first q) <
                         (acc length q)) /\ 0 <= (acc last1 q) /\
                         (acc last1 q) < (acc length q))) /\
                       (valid alloc result))) /\
                    (valid alloc q)) /\ (valid alloc q))))) /\
                (valid alloc result))))) /\
            (valid alloc result))))) /\
      (((acc last0 q) <> (acc length q) ->
        (forall (result:unit),
         (result = tt ->
          (forall (result:pointer),
           (result = q ->
            (forall (empty0:((memory) Z)),
             (empty0 = (upd empty result 0) ->
              (forall (result:pointer),
               (result = q ->
                ((forall (result0:Z),
                  ((acc first q) = (acc last0 q) /\ result0 = 1 \/
                   (acc first q) <> (acc last0 q) /\ result0 = 0 ->
                   (forall (full0:((memory) Z)),
                    (full0 = (upd full result result0) -> ((acc empty0 q) =
                     0 /\ (acc intP0 (shift (acc contents q) (acc last q))) =
                     c) /\
                     ((((not_assigns alloc last last0 (pset_singleton q)) /\
                     (not_assigns alloc intP intP0
                      (pset_singleton (shift (acc contents q) (acc last q))))) /\
                     (not_assigns alloc full full0 (pset_singleton q))) /\
                     (not_assigns alloc empty empty0 (pset_singleton q))) /\
                     ((valid_range alloc (acc contents q) 0
                       ((acc length q) - 1)) /\
                     0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                     0 <= (acc last0 q) /\ (acc last0 q) < (acc length q))) /\
                   (valid alloc result))) /\
                (valid alloc q)) /\ (valid alloc q))))) /\
            (valid alloc result)))))))) /\
      (valid alloc q)) /\ (valid alloc q))) /\
    (valid alloc result))).
Proof.
intuition;subst;auto;caduceus.
rewrite acc_upd_eq in H8;auto.
omega.
Save.

(* Why obligation from file "why/queue.why", characters 5792-5811 *)
Lemma test_impl_po_1 : 
  forall (q1: pointer),
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre5: ((((valid alloc q1) /\ ~(q1 = q)) /\ (acc empty q) = 0) /\
                ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                0 <= (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <=
                (acc last q) /\ (acc last q) < (acc length q)) /\
                (valid_range alloc q 0 1)),
  ((acc empty q) = 0 /\
  ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\ 0 <=
  (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <= (acc last q) /\
  (acc last q) < (acc length q)) /\ (valid_range alloc q 0 1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/queue.why", characters 5775-5816 *)
Lemma test_impl_po_2 : 
  forall (q1: pointer),
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (intP: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (Pre5: ((((valid alloc q1) /\ ~(q1 = q)) /\ (acc empty q) = 0) /\
                ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                0 <= (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <=
                (acc last q) /\ (acc last q) < (acc length q)) /\
                (valid_range alloc q 0 1)),
  forall (Pre3: ((acc empty q) = 0 /\
                ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                0 <= (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <=
                (acc last q) /\ (acc last q) < (acc length q)) /\
                (valid_range alloc q 0 1)),
  forall (empty0: ((memory) Z)),
  forall (first0: ((memory) Z)),
  forall (full0: ((memory) Z)),
  forall (caduceus_1: Z),
  forall (Post4: ((acc full0 q) = 0 /\ caduceus_1 =
                 (acc intP (shift (acc contents q) (acc first q)))) /\
                 (((not_assigns alloc full full0 (pset_singleton q)) /\
                 (not_assigns alloc first first0 (pset_singleton q))) /\
                 (not_assigns alloc empty empty0 (pset_singleton q))) /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first0 q) /\ (acc first0 q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)),
  forall (result: unit),
  forall (Post1: result = tt),
  (forall (result:Z),
   (result = (acc empty0 q1) -> result = (acc empty q1) /\
    ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\ 0 <=
    (acc first0 q) /\ (acc first0 q) < (acc length q)) /\ 0 <=
    (acc last q) /\ (acc last q) < (acc length q))) /\
  (valid alloc q1).
Proof.
intuition.
subst;auto.
Save.

