(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

Proof.
intuition.
destruct result0; intuition.
Save.

Proof.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 799-828 *)
Lemma flag_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre15: (valid_range alloc t 0 n) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post9: b = 0),
  forall (i: Z),
  forall (Post8: i = 0),
  forall (r: Z),
  forall (Post7: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre14: Variant1 = (r1 - i1)),
  forall (Pre13: (((((((forall (k:Z),
                        (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                 0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                 (isMonochrome alloc intP0 t 0 b1 BLUE)) /\
                 (isMonochrome alloc intP0 t b1 i1 WHITE)) /\
                 (isMonochrome alloc intP0 t r1 n RED)),
  forall (Test2: i1 < r1),
  forall (aux_1: pointer),
  forall (Post24: aux_1 = (shift t i1)),
  (valid alloc aux_1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 799-828 *)
Lemma flag_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre15: (valid_range alloc t 0 n) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post9: b = 0),
  forall (i: Z),
  forall (Post8: i = 0),
  forall (r: Z),
  forall (Post7: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre14: Variant1 = (r1 - i1)),
  forall (Pre13: (((((((forall (k:Z),
                        (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                 0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                 (isMonochrome alloc intP0 t 0 b1 BLUE)) /\
                 (isMonochrome alloc intP0 t b1 i1 WHITE)) /\
                 (isMonochrome alloc intP0 t r1 n RED)),
  forall (Test2: i1 < r1),
  forall (aux_1: pointer),
  forall (Post24: aux_1 = (shift t i1)),
  forall (Pre2: (valid alloc aux_1)),
  forall (result0: Z),
  forall (Post26: result0 = (acc intP0 aux_1)),
  ((result0 = BLUE ->
    (forall (result:Z),
     (result = b1 ->
      (forall (b:Z),
       (b = (result + 1) ->
        (forall (result0:Z),
         (result0 = i1 ->
          (forall (i:Z),
           (i = (result0 + 1) ->
            (forall (intP:((memory) Z)),
             (((acc intP (shift t result)) = (acc intP0 (shift t result0)) /\
              (acc intP (shift t result0)) = (acc intP0 (shift t result))) /\
              (assigns alloc intP0 intP
               (union_loc (pointer_loc (shift t result0))
                (pointer_loc (shift t result)))) ->
              ((((((((forall (k:Z),
                      (0 <= k /\ k < n -> (isColor (acc intP (shift t k))))) /\
              0 <= b) /\ b <= i) /\ i <= r1) /\ r1 <= n) /\
              (isMonochrome alloc intP t 0 b BLUE)) /\
              (isMonochrome alloc intP t b i WHITE)) /\
              (isMonochrome alloc intP t r1 n RED)) /\
              (Zwf 0 (r1 - i) (r1 - i1)))) /\
            (valid_index alloc t result) /\ (valid_index alloc t result0))))))))))) /\
  ((result0 <> BLUE ->
    (forall (result:pointer),
     (result = (shift t i1) ->
      (forall (result0:Z),
       (result0 = (acc intP0 result) ->
        ((result0 = WHITE ->
          (forall (i:Z),
           (i = (i1 + 1) ->
            ((((((((forall (k:Z),
                    (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
            0 <= b1) /\ b1 <= i) /\ i <= r1) /\ r1 <= n) /\
            (isMonochrome alloc intP0 t 0 b1 BLUE)) /\
            (isMonochrome alloc intP0 t b1 i WHITE)) /\
            (isMonochrome alloc intP0 t r1 n RED)) /\
            (Zwf 0 (r1 - i) (r1 - i1)))))) /\
        ((result0 <> WHITE ->
          (forall (result:pointer),
           (result = (shift t i1) ->
            (forall (result0:Z),
             (result0 = (acc intP0 result) ->
              ((result0 = RED ->
                (forall (r:Z),
                 (r = (r1 - 1) ->
                  (forall (intP:((memory) Z)),
                   (((acc intP (shift t r)) = (acc intP0 (shift t i1)) /\
                    (acc intP (shift t i1)) = (acc intP0 (shift t r))) /\
                    (assigns alloc intP0 intP
                     (union_loc (pointer_loc (shift t i1))
                      (pointer_loc (shift t r)))) ->
                    ((((((((forall (k:Z),
                            (0 <= k /\ k < n ->
                             (isColor (acc intP (shift t k))))) /\
                    0 <= b1) /\ b1 <= i1) /\ i1 <= r) /\ r <= n) /\
                    (isMonochrome alloc intP t 0 b1 BLUE)) /\
                    (isMonochrome alloc intP t b1 i1 WHITE)) /\
                    (isMonochrome alloc intP t r n RED)) /\
                    (Zwf 0 (r - i1) (r1 - i1)))) /\
                  (valid_index alloc t r) /\ (valid_index alloc t i1))))) /\
              ((result0 <> RED ->
                ((((((((forall (k:Z),
                        (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                (isMonochrome alloc intP0 t 0 b1 BLUE)) /\
                (isMonochrome alloc intP0 t b1 i1 WHITE)) /\
                (isMonochrome alloc intP0 t r1 n RED)) /\
                (Zwf 0 (r1 - i1) (r1 - i1)))))) /\
            (valid alloc result))))))) /\
      (valid alloc result))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 295-1599 *)
Lemma flag_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre15: (valid_range alloc t 0 n) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post9: b = 0),
  forall (i: Z),
  forall (Post8: i = 0),
  forall (r: Z),
  forall (Post7: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre14: Variant1 = (r1 - i1)),
  forall (Pre13: (((((((forall (k:Z),
                        (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                 0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                 (isMonochrome alloc intP0 t 0 b1 BLUE)) /\
                 (isMonochrome alloc intP0 t b1 i1 WHITE)) /\
                 (isMonochrome alloc intP0 t r1 n RED)),
  forall (Test1: i1 >= r1),
  (exists b:Z,
   (exists r:Z, ((isMonochrome alloc intP0 t 0 b BLUE) /\
    (isMonochrome alloc intP0 t b r WHITE)) /\
    (isMonochrome alloc intP0 t r n RED))) /\
  (assigns alloc intP intP0 (range_loc t 0 n)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 343-745 *)
Lemma flag_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre15: (valid_range alloc t 0 n) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post9: b = 0),
  forall (i: Z),
  forall (Post8: i = 0),
  forall (r: Z),
  forall (Post7: r = n),
  (((((((forall (k:Z), (0 <= k /\ k < n -> (isColor (acc intP (shift t k))))) /\
  0 <= b) /\ b <= i) /\ i <= r) /\ r <= n) /\
  (isMonochrome alloc intP t 0 b BLUE)) /\
  (isMonochrome alloc intP t b i WHITE)) /\
  (isMonochrome alloc intP t r n RED).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

