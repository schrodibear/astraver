(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/queue.why", characters 224-252 *)
Lemma invariants_initially_established_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre34: (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
  forall (caduceus_11: pointer),
  forall (Post3: caduceus_11 = (shift t 0)),
  (valid alloc caduceus_11).
Proof.
unfold valid_t.
intuition.
subst.
auto.
Save.

(* Why obligation from file "why/queue.why", characters 187-252 *)
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
  forall (Pre34: (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
  forall (caduceus_11: pointer),
  forall (Post3: caduceus_11 = (shift t 0)),
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
unfold valid_t;intuition;subst;auto;
caduceus.
Save.


(* Why obligation from file "why/queue.why", characters 1634-1653 *)
Lemma pop_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre23: ((acc empty q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
  (valid alloc q).
Proof.
intuition.
Save.

(* Why obligation from file "why/queue.why", characters 1786-1809 *)
Lemma pop_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre23: ((acc empty q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
  forall (Pre5: (valid alloc q)),
  forall (caduceus_6: pointer),
  forall (Post21: caduceus_6 = (acc contents q)),
  forall (caduceus1: pointer),
  forall (Post20: caduceus1 = q),
  (valid alloc caduceus1).
Proof.
intuition.
subst;auto.
Save.


(* Why obligation from file "why/queue.why", characters 1859-2114 *)
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
  forall (t: pointer),
  forall (Pre23: ((acc empty q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
  forall (Pre5: (valid alloc q)),
  forall (caduceus_6: pointer),
  forall (Post21: caduceus_6 = (acc contents q)),
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
   (result = (shift caduceus_6 result0) ->
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
                            (((assigns alloc full full0 (pointer_loc q)) /\
                            (assigns alloc first first1 (pointer_loc q))) /\
                            (assigns alloc empty empty0 (pointer_loc q))) /\
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
                        (((assigns alloc full full0 (pointer_loc q)) /\
                        (assigns alloc first first0 (pointer_loc q))) /\
                        (assigns alloc empty empty0 (pointer_loc q))) /\
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
rewrite acc_upd_eq in H10;auto.
assert (1+q# first <= q # length).
omega.
generalize (Zle_lt_or_eq (1 + q # first) (q # length) H6).
intros [h|h];auto.
elim H10;auto.
Save.

(* Why obligation from file "why/queue.why", characters 3740-3759 *)
Lemma push_impl_po_1 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre23: ((acc full q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
  (valid alloc q).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/queue.why", characters 3884-3906 *)
Lemma push_impl_po_2 : 
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (first: ((memory) Z)),
  forall (full: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre23: ((acc full q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
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

(* Why obligation from file "why/queue.why", characters 3952-4145 *)
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
  forall (t: pointer),
  forall (Pre23: ((acc full q) = 0 /\
                 ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                 0 <= (acc first q) /\ (acc first q) < (acc length q)) /\
                 0 <= (acc last q) /\ (acc last q) < (acc length q)) /\
                 (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                 (valid_q alloc q)),
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
                         ((((assigns alloc last last1 (pointer_loc q)) /\
                         (assigns alloc intP intP0
                          (pointer_loc (shift (acc contents q) (acc last q))))) /\
                         (assigns alloc full full0 (pointer_loc q))) /\
                         (assigns alloc empty empty0 (pointer_loc q))) /\
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
                     c) /\ ((((assigns alloc last last0 (pointer_loc q)) /\
                     (assigns alloc intP intP0
                      (pointer_loc (shift (acc contents q) (acc last q))))) /\
                     (assigns alloc full full0 (pointer_loc q))) /\
                     (assigns alloc empty empty0 (pointer_loc q))) /\
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
rewrite acc_upd_eq in H10;auto.
assert (1+q# last <= q # length).
omega.
generalize (Zle_lt_or_eq (1 + q # last) (q # length) H6).
intros [h|h];auto.
elim H10;auto.
Save.

(* Why obligation from file "why/queue.why", characters 5899-5918 *)
Lemma test_impl_po_1 : 
  forall (q1: pointer),
  forall (alloc: alloc_table),
  forall (contents: ((memory) pointer)),
  forall (empty: ((memory) Z)),
  forall (first: ((memory) Z)),
  forall (last: ((memory) Z)),
  forall (length: ((memory) Z)),
  forall (q: pointer),
  forall (t: pointer),
  forall (Pre5: ((((valid alloc q1) /\ ~(q1 = q)) /\ (acc empty q) = 0) /\
                ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                0 <= (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <=
                (acc last q) /\ (acc last q) < (acc length q)) /\
                (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                (valid_q alloc q)),
  ((acc empty q) = 0 /\
  ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\ 0 <=
  (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <= (acc last q) /\
  (acc last q) < (acc length q)) /\ (separation_q_t alloc contents t q) /\
  (valid_t alloc t) /\ (valid_q alloc q).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/queue.why", characters 5882-5923 *)
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
  forall (t: pointer),
  forall (Pre5: ((((valid alloc q1) /\ ~(q1 = q)) /\ (acc empty q) = 0) /\
                ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                0 <= (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <=
                (acc last q) /\ (acc last q) < (acc length q)) /\
                (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                (valid_q alloc q)),
  forall (Pre3: ((acc empty q) = 0 /\
                ((valid_range alloc (acc contents q) 0 ((acc length q) - 1)) /\
                0 <= (acc first q) /\ (acc first q) < (acc length q)) /\ 0 <=
                (acc last q) /\ (acc last q) < (acc length q)) /\
                (separation_q_t alloc contents t q) /\ (valid_t alloc t) /\
                (valid_q alloc q)),
  forall (empty0: ((memory) Z)),
  forall (first0: ((memory) Z)),
  forall (full0: ((memory) Z)),
  forall (caduceus_1: Z),
  forall (Post4: ((acc full0 q) = 0 /\ caduceus_1 =
                 (acc intP (shift (acc contents q) (acc first q)))) /\
                 (((assigns alloc full full0 (pointer_loc q)) /\
                 (assigns alloc first first0 (pointer_loc q))) /\
                 (assigns alloc empty empty0 (pointer_loc q))) /\
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

