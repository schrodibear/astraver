(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/flag.why", characters 1000-1028 *)
Lemma flag_impl_po_1 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre11: (valid_range alloc t 0 (n - 1)) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post24: b = 0),
  forall (i: Z),
  forall (Post23: i = 0),
  forall (r: Z),
  forall (Post22: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre10: Variant1 = (r1 - i1)),
  forall (Pre9: (((((((forall (k:Z),
                       (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
                (isMonochrome alloc intP0 t b1 (i1 - 1) WHITE)) /\
                (isMonochrome alloc intP0 t r1 (n - 1) RED)),
  forall (Test8: i1 < r1),
  (valid alloc (shift t i1)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 1191-1299 *)
Lemma flag_impl_po_2 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre11: (valid_range alloc t 0 (n - 1)) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post24: b = 0),
  forall (i: Z),
  forall (Post23: i = 0),
  forall (r: Z),
  forall (Post22: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre10: Variant1 = (r1 - i1)),
  forall (Pre9: (((((((forall (k:Z),
                       (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
                (isMonochrome alloc intP0 t b1 (i1 - 1) WHITE)) /\
                (isMonochrome alloc intP0 t r1 (n - 1) RED)),
  forall (Test8: i1 < r1),
  forall (Pre8: (valid alloc (shift t i1))),
  forall (caduceus_1: Z),
  forall (Post21: caduceus_1 = (acc intP0 (shift t i1))),
  forall (Test7: caduceus_1 = BLUE),
  forall (caduceus: Z),
  forall (Post19: caduceus = b1),
  forall (b2: Z),
  forall (Post17: b2 = (caduceus + 1)),
  forall (result2: Z),
  forall (Post18: result2 = caduceus),
  (forall (result:Z),
   (result = i1 ->
    (forall (i:Z),
     (i = (result + 1) ->
      (forall (result0:Z),
       (result0 = result ->
        (forall (intP:((memory) Z)),
         (((acc intP (shift t result2)) = (acc intP0 (shift t result0)) /\
          (acc intP (shift t result0)) = (acc intP0 (shift t result2))) /\
          (assigns alloc intP0 intP
           (union_loc (pointer_loc (shift t result0))
            (pointer_loc (shift t result2)))) ->
          ((((((((forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k))))) /\
          0 <= b2) /\ b2 <= i) /\ i <= r1) /\ r1 <= n) /\
          (isMonochrome alloc intP t 0 (b2 - 1) BLUE)) /\
          (isMonochrome alloc intP t b2 (i - 1) WHITE)) /\
          (isMonochrome alloc intP t r1 (n - 1) RED)) /\
          (Zwf 0 (r1 - i) (r1 - i1)))) /\
        (valid_index alloc t result2) /\ (valid_index alloc t result0))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 1706-1736 *)
Lemma flag_impl_po_3 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre11: (valid_range alloc t 0 (n - 1)) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post24: b = 0),
  forall (i: Z),
  forall (Post23: i = 0),
  forall (r: Z),
  forall (Post22: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre10: Variant1 = (r1 - i1)),
  forall (Pre9: (((((((forall (k:Z),
                       (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
                (isMonochrome alloc intP0 t b1 (i1 - 1) WHITE)) /\
                (isMonochrome alloc intP0 t r1 (n - 1) RED)),
  forall (Test8: i1 < r1),
  forall (Pre8: (valid alloc (shift t i1))),
  forall (caduceus_1: Z),
  forall (Post21: caduceus_1 = (acc intP0 (shift t i1))),
  forall (Test6: caduceus_1 <> BLUE),
  forall (Test5: caduceus_1 = WHITE),
  forall (i2: Z),
  forall (Post9: i2 = (i1 + 1)),
  ((((((((forall (k:Z),
          (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
  0 <= b1) /\ b1 <= i2) /\ i2 <= r1) /\ r1 <= n) /\
  (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
  (isMonochrome alloc intP0 t b1 (i2 - 1) WHITE)) /\
  (isMonochrome alloc intP0 t r1 (n - 1) RED)) /\ (Zwf 0 (r1 - i2) (r1 - i1)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 1870-1904 *)
Lemma flag_impl_po_4 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre11: (valid_range alloc t 0 (n - 1)) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post24: b = 0),
  forall (i: Z),
  forall (Post23: i = 0),
  forall (r: Z),
  forall (Post22: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre10: Variant1 = (r1 - i1)),
  forall (Pre9: (((((((forall (k:Z),
                       (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
                (isMonochrome alloc intP0 t b1 (i1 - 1) WHITE)) /\
                (isMonochrome alloc intP0 t r1 (n - 1) RED)),
  forall (Test8: i1 < r1),
  forall (Pre8: (valid alloc (shift t i1))),
  forall (caduceus_1: Z),
  forall (Post21: caduceus_1 = (acc intP0 (shift t i1))),
  forall (Test6: caduceus_1 <> BLUE),
  forall (Test4: caduceus_1 <> WHITE),
  forall (Test3: caduceus_1 = RED),
  forall (r2: Z),
  forall (Post6: r2 = (r1 - 1)),
  forall (result4: Z),
  forall (Post7: result4 = r2),
  (forall (intP:((memory) Z)),
   (((acc intP (shift t result4)) = (acc intP0 (shift t i1)) /\
    (acc intP (shift t i1)) = (acc intP0 (shift t result4))) /\
    (assigns alloc intP0 intP
     (union_loc (pointer_loc (shift t i1)) (pointer_loc (shift t result4)))) ->
    ((((((((forall (k:Z),
            (0 <= k /\ k < n -> (isColor (acc intP (shift t k))))) /\
    0 <= b1) /\ b1 <= i1) /\ i1 <= r2) /\ r2 <= n) /\
    (isMonochrome alloc intP t 0 (b1 - 1) BLUE)) /\
    (isMonochrome alloc intP t b1 (i1 - 1) WHITE)) /\
    (isMonochrome alloc intP t r2 (n - 1) RED)) /\
    (Zwf 0 (r2 - i1) (r1 - i1)))) /\
  (valid_index alloc t result4) /\ (valid_index alloc t i1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 2000-2000 *)
Lemma flag_impl_po_5 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre11: (valid_range alloc t 0 (n - 1)) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post24: b = 0),
  forall (i: Z),
  forall (Post23: i = 0),
  forall (r: Z),
  forall (Post22: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre10: Variant1 = (r1 - i1)),
  forall (Pre9: (((((((forall (k:Z),
                       (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
                (isMonochrome alloc intP0 t b1 (i1 - 1) WHITE)) /\
                (isMonochrome alloc intP0 t r1 (n - 1) RED)),
  forall (Test8: i1 < r1),
  forall (Pre8: (valid alloc (shift t i1))),
  forall (caduceus_1: Z),
  forall (Post21: caduceus_1 = (acc intP0 (shift t i1))),
  forall (Test6: caduceus_1 <> BLUE),
  forall (Test4: caduceus_1 <> WHITE),
  forall (Test2: caduceus_1 <> RED),
  forall (result3: unit),
  forall (Post2: result3 = tt),
  ((((((((forall (k:Z),
          (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
  0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
  (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
  (isMonochrome alloc intP0 t b1 (i1 - 1) WHITE)) /\
  (isMonochrome alloc intP0 t r1 (n - 1) RED)) /\ (Zwf 0 (r1 - i1) (r1 - i1)).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 372-2015 *)
Lemma flag_impl_po_6 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre11: (valid_range alloc t 0 (n - 1)) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post24: b = 0),
  forall (i: Z),
  forall (Post23: i = 0),
  forall (r: Z),
  forall (Post22: r = n),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (intP0: ((memory) Z)),
  forall (r1: Z),
  forall (Pre10: Variant1 = (r1 - i1)),
  forall (Pre9: (((((((forall (k:Z),
                       (0 <= k /\ k < n -> (isColor (acc intP0 (shift t k))))) /\
                0 <= b1) /\ b1 <= i1) /\ i1 <= r1) /\ r1 <= n) /\
                (isMonochrome alloc intP0 t 0 (b1 - 1) BLUE)) /\
                (isMonochrome alloc intP0 t b1 (i1 - 1) WHITE)) /\
                (isMonochrome alloc intP0 t r1 (n - 1) RED)),
  forall (Test1: i1 >= r1),
  (exists b:Z,
   (exists r:Z, ((isMonochrome alloc intP0 t 0 (b - 1) BLUE) /\
    (isMonochrome alloc intP0 t b (r - 1) WHITE)) /\
    (isMonochrome alloc intP0 t r (n - 1) RED))) /\
  (assigns alloc intP intP0 (range_loc t 0 (n - 1))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/flag.why", characters 434-934 *)
Lemma flag_impl_po_7 : 
  forall (t: pointer),
  forall (n: Z),
  forall (alloc: alloc_table),
  forall (intP: ((memory) Z)),
  forall (Pre11: (valid_range alloc t 0 (n - 1)) /\
                 (forall (k:Z),
                  (0 <= k /\ k < n -> (isColor (acc intP (shift t k)))))),
  forall (b: Z),
  forall (Post24: b = 0),
  forall (i: Z),
  forall (Post23: i = 0),
  forall (r: Z),
  forall (Post22: r = n),
  (((((((forall (k:Z), (0 <= k /\ k < n -> (isColor (acc intP (shift t k))))) /\
  0 <= b) /\ b <= i) /\ i <= r) /\ r <= n) /\
  (isMonochrome alloc intP t 0 (b - 1) BLUE)) /\
  (isMonochrome alloc intP t b (i - 1) WHITE)) /\
  (isMonochrome alloc intP t r (n - 1) RED).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

