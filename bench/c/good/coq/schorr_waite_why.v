(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/schorr_waite.why", characters 447-447 *)
Lemma schorr_waite_impl_po_1 : 
  forall (root: pointer),
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Post18: t = root),
  forall (p: pointer),
  forall (Post17: p = null),
  forall (Variant1: Z),
  forall (c0: ((memory) Z)),
  forall (l0: ((memory) pointer)),
  forall (m0: ((memory) Z)),
  forall (p1: pointer),
  forall (r0: ((memory) pointer)),
  forall (t1: pointer),
  forall (Pre41: Variant1 = 0),
  forall (Test8: true = true),
  forall (Test5: ~(p1 = null)),
  ((t1 = null ->
    (forall (result:Z),
     (result = (acc c0 p1) ->
      ((result <> 0 ->
        (forall (result:pointer),
         (result = t1 ->
          (forall (t:pointer),
           (t = p1 ->
            (forall (p:pointer),
             (p = (acc r0 p1) ->
              (forall (result0:pointer),
               (result0 = t ->
                (forall (r:((memory) pointer)),
                 (r = (upd r0 result0 result) -> (Zwf 0 0 0))) /\
                (valid alloc result0))))) /\
            (valid alloc p1))))))) /\
      ((result = 0 ->
        (forall (result:pointer),
         (result = t1 ->
          (forall (t:pointer),
           (t = (acc r0 p1) ->
            (forall (result0:pointer),
             (result0 = p1 ->
              (forall (result1:pointer),
               (result1 = (acc l0 p1) ->
                (forall (r:((memory) pointer)),
                 (r = (upd r0 result0 result1) ->
                  (forall (result0:pointer),
                   (result0 = p1 ->
                    (forall (l:((memory) pointer)),
                     (l = (upd l0 result0 result) ->
                      (forall (result:pointer),
                       (result = p1 ->
                        (forall (c:((memory) Z)),
                         (c = (upd c0 result 1) -> (Zwf 0 0 0))) /\
                        (valid alloc result))))) /\
                    (valid alloc result0))))) /\
                (valid alloc result0))) /\
              (valid alloc p1))))) /\
          (valid alloc p1))))))) /\
    (valid alloc p1))) /\
  ((~(t1 = null) ->
    (forall (result:Z),
     (result = (acc m0 t1) ->
      ((result <> 0 ->
        (forall (result:Z),
         (result = (acc c0 p1) ->
          ((result <> 0 ->
            (forall (result:pointer),
             (result = t1 ->
              (forall (t:pointer),
               (t = p1 ->
                (forall (p:pointer),
                 (p = (acc r0 p1) ->
                  (forall (result0:pointer),
                   (result0 = t ->
                    (forall (r:((memory) pointer)),
                     (r = (upd r0 result0 result) -> (Zwf 0 0 0))) /\
                    (valid alloc result0))))) /\
                (valid alloc p1))))))) /\
          ((result = 0 ->
            (forall (result:pointer),
             (result = t1 ->
              (forall (t:pointer),
               (t = (acc r0 p1) ->
                (forall (result0:pointer),
                 (result0 = p1 ->
                  (forall (result1:pointer),
                   (result1 = (acc l0 p1) ->
                    (forall (r:((memory) pointer)),
                     (r = (upd r0 result0 result1) ->
                      (forall (result0:pointer),
                       (result0 = p1 ->
                        (forall (l:((memory) pointer)),
                         (l = (upd l0 result0 result) ->
                          (forall (result:pointer),
                           (result = p1 ->
                            (forall (c:((memory) Z)),
                             (c = (upd c0 result 1) -> (Zwf 0 0 0))) /\
                            (valid alloc result))))) /\
                        (valid alloc result0))))) /\
                    (valid alloc result0))) /\
                  (valid alloc p1))))) /\
              (valid alloc p1))))))) /\
        (valid alloc p1))) /\
      ((result = 0 ->
        (forall (result:pointer),
         (result = p1 ->
          (forall (p:pointer),
           (p = t1 ->
            (forall (t:pointer),
             (t = (acc l0 t1) ->
              (forall (result0:pointer),
               (result0 = p ->
                (forall (l:((memory) pointer)),
                 (l = (upd l0 result0 result) ->
                  (forall (result:pointer),
                   (result = p ->
                    (forall (m:((memory) Z)),
                     (m = (upd m0 result 1) ->
                      (forall (result:pointer),
                       (result = p ->
                        (forall (c:((memory) Z)),
                         (c = (upd c0 result 0) -> (Zwf 0 0 0))) /\
                        (valid alloc result))))) /\
                    (valid alloc result))))) /\
                (valid alloc result0))))) /\
            (valid alloc t1))))))))) /\
    (valid alloc t1))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/schorr_waite.why", characters 339-352 *)
Lemma schorr_waite_impl_po_2 : 
  forall (root: pointer),
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Post18: t = root),
  forall (p: pointer),
  forall (Post17: p = null),
  forall (Variant1: Z),
  forall (p1: pointer),
  forall (t1: pointer),
  forall (Pre41: Variant1 = 0),
  forall (Test8: true = true),
  forall (Test4: p1 = null),
  forall (Test3: ~(t1 = null)),
  (valid alloc t1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/schorr_waite.why", characters 256-445 *)
Lemma schorr_waite_impl_po_3 : 
  forall (root: pointer),
  forall (alloc: alloc_table),
  forall (t: pointer),
  forall (Post18: t = root),
  forall (p: pointer),
  forall (Post17: p = null),
  forall (Variant1: Z),
  forall (c0: ((memory) Z)),
  forall (l0: ((memory) pointer)),
  forall (m0: ((memory) Z)),
  forall (p1: pointer),
  forall (r0: ((memory) pointer)),
  forall (t1: pointer),
  forall (Pre41: Variant1 = 0),
  forall (Test8: true = true),
  forall (Test4: p1 = null),
  forall (Test3: ~(t1 = null)),
  forall (Pre4: (valid alloc t1)),
  forall (caduceus_10: Z),
  forall (Post38: caduceus_10 = (acc m0 t1)),
  forall (result2: bool),
  forall (Post40: (if result2 then caduceus_10 <> 0 else caduceus_10 = 0)),
  (if result2 then True
   else ((t1 = null ->
          (forall (result:Z),
           (result = (acc c0 p1) ->
            ((result <> 0 ->
              (forall (result:pointer),
               (result = t1 ->
                (forall (t:pointer),
                 (t = p1 ->
                  (forall (p:pointer),
                   (p = (acc r0 p1) ->
                    (forall (result0:pointer),
                     (result0 = t ->
                      (forall (r:((memory) pointer)),
                       (r = (upd r0 result0 result) -> (Zwf 0 0 0))) /\
                      (valid alloc result0))))) /\
                  (valid alloc p1))))))) /\
            ((result = 0 ->
              (forall (result:pointer),
               (result = t1 ->
                (forall (t:pointer),
                 (t = (acc r0 p1) ->
                  (forall (result0:pointer),
                   (result0 = p1 ->
                    (forall (result1:pointer),
                     (result1 = (acc l0 p1) ->
                      (forall (r:((memory) pointer)),
                       (r = (upd r0 result0 result1) ->
                        (forall (result0:pointer),
                         (result0 = p1 ->
                          (forall (l:((memory) pointer)),
                           (l = (upd l0 result0 result) ->
                            (forall (result:pointer),
                             (result = p1 ->
                              (forall (c:((memory) Z)),
                               (c = (upd c0 result 1) -> (Zwf 0 0 0))) /\
                              (valid alloc result))))) /\
                          (valid alloc result0))))) /\
                      (valid alloc result0))) /\
                    (valid alloc p1))))) /\
                (valid alloc p1))))))) /\
          (valid alloc p1))) /\
   ((~(t1 = null) ->
     (forall (result:Z),
      (result = (acc m0 t1) ->
       ((result <> 0 ->
         (forall (result:Z),
          (result = (acc c0 p1) ->
           ((result <> 0 ->
             (forall (result:pointer),
              (result = t1 ->
               (forall (t:pointer),
                (t = p1 ->
                 (forall (p:pointer),
                  (p = (acc r0 p1) ->
                   (forall (result0:pointer),
                    (result0 = t ->
                     (forall (r:((memory) pointer)),
                      (r = (upd r0 result0 result) -> (Zwf 0 0 0))) /\
                     (valid alloc result0))))) /\
                 (valid alloc p1))))))) /\
           ((result = 0 ->
             (forall (result:pointer),
              (result = t1 ->
               (forall (t:pointer),
                (t = (acc r0 p1) ->
                 (forall (result0:pointer),
                  (result0 = p1 ->
                   (forall (result1:pointer),
                    (result1 = (acc l0 p1) ->
                     (forall (r:((memory) pointer)),
                      (r = (upd r0 result0 result1) ->
                       (forall (result0:pointer),
                        (result0 = p1 ->
                         (forall (l:((memory) pointer)),
                          (l = (upd l0 result0 result) ->
                           (forall (result:pointer),
                            (result = p1 ->
                             (forall (c:((memory) Z)),
                              (c = (upd c0 result 1) -> (Zwf 0 0 0))) /\
                             (valid alloc result))))) /\
                         (valid alloc result0))))) /\
                     (valid alloc result0))) /\
                   (valid alloc p1))))) /\
               (valid alloc p1))))))) /\
         (valid alloc p1))) /\
       ((result = 0 ->
         (forall (result:pointer),
          (result = p1 ->
           (forall (p:pointer),
            (p = t1 ->
             (forall (t:pointer),
              (t = (acc l0 t1) ->
               (forall (result0:pointer),
                (result0 = p ->
                 (forall (l:((memory) pointer)),
                  (l = (upd l0 result0 result) ->
                   (forall (result:pointer),
                    (result = p ->
                     (forall (m:((memory) Z)),
                      (m = (upd m0 result 1) ->
                       (forall (result:pointer),
                        (result = p ->
                         (forall (c:((memory) Z)),
                          (c = (upd c0 result 0) -> (Zwf 0 0 0))) /\
                         (valid alloc result))))) /\
                     (valid alloc result))))) /\
                 (valid alloc result0))))) /\
             (valid alloc t1))))))))) /\
     (valid alloc t1)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/schorr_waite.why", characters 124-1485 *)
Lemma schorr_waite_impl_po_4 : 
  forall (root: pointer),
  forall (t: pointer),
  forall (Post18: t = root),
  forall (p: pointer),
  forall (Post17: p = null),
  forall (Variant1: Z),
  forall (Pre41: Variant1 = 0),
  forall (Test8: true = true),
  forall (Post19: (Zwf 0 0 0)),
  (Zwf 0 0 Variant1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

