(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Export caduceus_spec_why.

(* Why obligation from file "why/switch.why", characters 196-219 *)
Lemma f1_impl_po_1 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post13: caduceus_1 = x),
  forall (Test8: caduceus_1 = 0 \/ caduceus_1 <> 0 /\ caduceus_1 = 1),
  forall (y1: Z),
  forall (Post10: y1 = 1),
  forall (y2: Z),
  forall (Post11: y2 = 4),
  (forall (result:Z), (result = y2 -> (x = 4 -> result = 2))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 303-318 *)
Lemma f1_impl_po_2 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post13: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test6: caduceus_1 = 2 \/ caduceus_1 <> 2 /\ caduceus_1 = 4),
  forall (y1: Z),
  forall (Post8: y1 = 2),
  (forall (result:Z), (result = y1 -> (x = 4 -> result = 2))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 376-391 *)
Lemma f1_impl_po_3 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post13: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test5: caduceus_1 <> 2 /\ caduceus_1 <> 4),
  forall (Test4: caduceus_1 = 3),
  forall (y1: Z),
  forall (Post6: y1 = 3),
  (forall (result:Z), (result = y1 -> (x = 4 -> result = 2))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 716-739 *)
Lemma f1_impl_po_4 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post13: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test5: caduceus_1 <> 2 /\ caduceus_1 <> 4),
  forall (Test3: caduceus_1 <> 3),
  forall (Test2: caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\
                 caduceus_1 <> 3 /\ caduceus_1 <> 4),
  forall (y1: Z),
  forall (Post2: y1 = 4),
  forall (y2: Z),
  forall (Post3: y2 = 5),
  (forall (result:unit),
   (result = tt ->
    (forall (result:Z), (result = y2 -> (x = 4 -> result = 2))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 757-757 *)
Lemma f1_impl_po_5 : 
  forall (x: Z),
  forall (y: Z),
  forall (caduceus_1: Z),
  forall (Post13: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test5: caduceus_1 <> 2 /\ caduceus_1 <> 4),
  forall (Test3: caduceus_1 <> 3),
  forall (Test1: caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/
                 caduceus_1 <> 1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\
                 (caduceus_1 = 3 \/ caduceus_1 <> 3 /\ caduceus_1 = 4)))),
  forall (result3: unit),
  forall (Post1: result3 = tt),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = y -> (x = 4 -> result = 2))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 1054-1077 *)
Lemma f1a_impl_po_1 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post15: caduceus_1 = x),
  forall (Test8: caduceus_1 = 0 \/ caduceus_1 <> 0 /\ caduceus_1 = 1),
  forall (y1: Z),
  forall (Post12: y1 = 1),
  forall (y2: Z),
  forall (Post13: y2 = 4),
  (forall (y:Z),
   (y = 5 -> (forall (result:Z), (result = y -> (x = 4 -> result = 2))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 1180-1200 *)
Lemma f1a_impl_po_2 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post15: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test6: caduceus_1 = 2 \/ caduceus_1 <> 2 /\ caduceus_1 = 4),
  forall (y1: Z),
  forall (Post9: y1 = 2),
  forall (result2: Z),
  forall (Post10: result2 = y1),
  (forall (result:Z), (result = result2 -> (x = 4 -> result = 2))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 1279-1299 *)
Lemma f1a_impl_po_3 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post15: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test5: caduceus_1 <> 2 /\ caduceus_1 <> 4),
  forall (Test4: caduceus_1 = 3),
  forall (y1: Z),
  forall (Post6: y1 = 3),
  forall (result3: Z),
  forall (Post7: result3 = y1),
  (forall (result:Z), (result = result3 -> (x = 4 -> result = 2))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 1633-1648 *)
Lemma f1a_impl_po_4 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post15: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test5: caduceus_1 <> 2 /\ caduceus_1 <> 4),
  forall (Test3: caduceus_1 <> 3),
  forall (Test2: caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\
                 caduceus_1 <> 3 /\ caduceus_1 <> 4),
  forall (y1: Z),
  forall (Post3: y1 = 4),
  (forall (result:unit),
   (result = tt ->
    (forall (y:Z),
     (y = 5 -> (forall (result:Z), (result = y -> (x = 4 -> result = 2))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 1667-1667 *)
Lemma f1a_impl_po_5 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post15: caduceus_1 = x),
  forall (Test7: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (Test5: caduceus_1 <> 2 /\ caduceus_1 <> 4),
  forall (Test3: caduceus_1 <> 3),
  forall (Test1: caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/
                 caduceus_1 <> 1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\
                 (caduceus_1 = 3 \/ caduceus_1 <> 3 /\ caduceus_1 = 4)))),
  forall (result3: unit),
  forall (Post2: result3 = tt),
  (forall (result:unit),
   (result = tt ->
    (forall (y:Z),
     (y = 5 -> (forall (result:Z), (result = y -> (x = 4 -> result = 2))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 2044-2059 *)
Lemma f2_impl_po_1 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post14: caduceus_1 = x),
  forall (Test2: caduceus_1 = 0 \/ caduceus_1 <> 0 /\ caduceus_1 = 1),
  forall (y1: Z),
  forall (Post2: y1 = 1),
  ((caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/ caduceus_1 <>
    1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\ caduceus_1 = 4)) ->
    (forall (y:Z),
     (y = 2 ->
      ((caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/ caduceus_1 <>
        1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\ (caduceus_1 = 3 \/
        caduceus_1 <> 3 /\ caduceus_1 = 4))) ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\
        caduceus_1 <> 3 /\ caduceus_1 <> 4 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))))))) /\
  ((caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\ caduceus_1 <>
    4 ->
    (forall (result:unit),
     (result = tt ->
      ((caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/ caduceus_1 <>
        1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\ (caduceus_1 = 3 \/
        caduceus_1 <> 3 /\ caduceus_1 = 4))) ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\
        caduceus_1 <> 3 /\ caduceus_1 <> 4 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y1 -> result = 4)))))))))))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 2074-2074 *)
Lemma f2_impl_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (caduceus_1: Z),
  forall (Post14: caduceus_1 = x),
  forall (Test1: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  ((caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/ caduceus_1 <>
    1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\ caduceus_1 = 4)) ->
    (forall (y:Z),
     (y = 2 ->
      ((caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/ caduceus_1 <>
        1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\ (caduceus_1 = 3 \/
        caduceus_1 <> 3 /\ caduceus_1 = 4))) ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\
        caduceus_1 <> 3 /\ caduceus_1 <> 4 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))))))) /\
  ((caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\ caduceus_1 <>
    4 ->
    (forall (result:unit),
     (result = tt ->
      ((caduceus_1 = 0 \/ caduceus_1 <> 0 /\ (caduceus_1 = 1 \/ caduceus_1 <>
        1 /\ (caduceus_1 = 2 \/ caduceus_1 <> 2 /\ (caduceus_1 = 3 \/
        caduceus_1 <> 3 /\ caduceus_1 = 4))) ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 <> 0 /\ caduceus_1 <> 1 /\ caduceus_1 <> 2 /\
        caduceus_1 <> 3 /\ caduceus_1 <> 4 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))))))).
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

Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 3023-3038 *)
Lemma f3_impl_po_1 : 
  forall (x: Z),
  forall (caduceus_1: Z),
  forall (Post14: caduceus_1 = x),
  forall (Test2: caduceus_1 = 0 \/ caduceus_1 <> 0 /\ caduceus_1 = 1),
  forall (y1: Z),
  forall (Post2: y1 = 1),
  ((caduceus_1 <> 2 /\ caduceus_1 <> 3 ->
    (forall (y:Z),
     (y = 2 ->
      ((caduceus_1 <> 2 ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 = 2 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))))))) /\
  ((caduceus_1 = 2 \/ caduceus_1 <> 2 /\ caduceus_1 = 3 ->
    (forall (result:unit),
     (result = tt ->
      ((caduceus_1 <> 2 ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 = 2 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y1 -> result = 4)))))))))))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 3053-3053 *)
Lemma f3_impl_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (caduceus_1: Z),
  forall (Post14: caduceus_1 = x),
  forall (Test1: caduceus_1 <> 0 /\ caduceus_1 <> 1),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  ((caduceus_1 <> 2 /\ caduceus_1 <> 3 ->
    (forall (y:Z),
     (y = 2 ->
      ((caduceus_1 <> 2 ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 = 2 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))))))) /\
  ((caduceus_1 = 2 \/ caduceus_1 <> 2 /\ caduceus_1 = 3 ->
    (forall (result:unit),
     (result = tt ->
      ((caduceus_1 <> 2 ->
        (forall (y:Z),
         (y = 3 ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))) /\
      ((caduceus_1 = 2 ->
        (forall (result:unit),
         (result = tt ->
          ((true = true ->
            (forall (y:Z),
             (y = 4 ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))) /\
          ((false = true ->
            (forall (result:unit),
             (result = tt ->
              (forall (result:unit),
               (result = tt ->
                (forall (result:Z), (result = y -> result = 4)))))))))))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 3613-3619 *)
Lemma f4_impl_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post10: y = 0),
  forall (caduceus_1: Z),
  forall (Post8: caduceus_1 = x),
  forall (Test4: caduceus_1 = 0),
  forall (Test3: x = 0),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = y -> result = 0)))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 3630-3630 *)
Lemma f4_impl_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post10: y = 0),
  forall (caduceus_1: Z),
  forall (Post8: caduceus_1 = x),
  forall (Test4: caduceus_1 = 0),
  forall (Test2: x <> 0),
  forall (result1: unit),
  forall (Post3: result1 = tt),
  (forall (y:Z),
   (y = 1 ->
    (forall (result:unit),
     (result = tt -> (forall (result:Z), (result = y -> result = 0)))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 3659-3659 *)
Lemma f4_impl_po_3 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post10: y = 0),
  forall (caduceus_1: Z),
  forall (Post8: caduceus_1 = x),
  forall (Test1: caduceus_1 <> 0),
  forall (result0: unit),
  forall (Post2: result0 = tt),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = y -> result = 0)))).
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

(* Why obligation from file "why/switch.why", characters 4075-4081 *)
Lemma f5_impl_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post9: y = 0),
  forall (caduceus_1: Z),
  forall (Post7: caduceus_1 = x),
  forall (Test4: caduceus_1 = 1),
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 0),
  forall (Test3: x > 0),
  (forall (result:unit),
   (result = tt ->
    (forall (y:Z),
     (y = 1 ->
      (forall (result:unit),
       (result = tt ->
        (forall (result:Z), (result = y -> (x = 1 -> result = 1))))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 4011-4098 *)
Lemma f5_impl_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post9: y = 0),
  forall (caduceus_1: Z),
  forall (Post7: caduceus_1 = x),
  forall (Test4: caduceus_1 = 1),
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 0),
  forall (Test3: x > 0),
  forall (Post10: (Zwf 0 0 0)),
  (Zwf 0 0 Variant1).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 4011-4098 *)
Lemma f5_impl_po_3 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post9: y = 0),
  forall (caduceus_1: Z),
  forall (Post7: caduceus_1 = x),
  forall (Test4: caduceus_1 = 1),
  forall (Variant1: Z),
  forall (Pre3: Variant1 = 0),
  forall (Test2: x <= 0),
  (forall (y:Z),
   (y = 1 ->
    (forall (result:unit),
     (result = tt ->
      (forall (result:Z), (result = y -> (x = 1 -> result = 1))))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 4210-4210 *)
Lemma f5_impl_po_4 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post9: y = 0),
  forall (caduceus_1: Z),
  forall (Post7: caduceus_1 = x),
  forall (Test1: caduceus_1 <> 1),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = y -> (x = 1 -> result = 1))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 4475-4490 *)
Lemma f6_impl_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post7: y = 0),
  forall (caduceus_1: Z),
  forall (Post5: caduceus_1 = x),
  forall (Test2: caduceus_1 = (1 + 1)),
  forall (y1: Z),
  forall (Post2: y1 = 1),
  (forall (result:unit),
   (result = tt ->
    (forall (result:Z), (result = y1 -> (x = 2 -> result = 1))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 4505-4505 *)
Lemma f6_impl_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post7: y = 0),
  forall (caduceus_1: Z),
  forall (Post5: caduceus_1 = x),
  forall (Test1: caduceus_1 <> (1 + 1)),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = y -> (x = 2 -> result = 1))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 4750-4765 *)
Lemma f7_impl_po_1 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post7: y = 0),
  forall (caduceus_1: Z),
  forall (Post5: caduceus_1 = x),
  forall (Test2: caduceus_1 = A),
  forall (y1: Z),
  forall (Post2: y1 = 1),
  (forall (result:unit),
   (result = tt ->
    (forall (result:Z), (result = y1 -> (x = A -> result = 1))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

(* Why obligation from file "why/switch.why", characters 4774-4774 *)
Lemma f7_impl_po_2 : 
  forall (x: Z),
  forall (y: Z),
  forall (Post7: y = 0),
  forall (caduceus_1: Z),
  forall (Post5: caduceus_1 = x),
  forall (Test1: caduceus_1 <> A),
  forall (result0: unit),
  forall (Post1: result0 = tt),
  (forall (result:unit),
   (result = tt -> (forall (result:Z), (result = y -> (x = A -> result = 1))))).
Proof.
intuition.
(* FILL PROOF HERE *)
Save.

