
Require Import Why.

Parameter l : Z.
Axiom l_pos : (0 < l)%Z.

(*Why*) Parameter swap :
  forall (i: Z), forall (j: Z), forall (a: (array Z)),
  forall (H: (array_length a) = l),
  (sig_2 (array Z) unit
   (fun (a0: (array Z)) (result: unit)  => ((array_length a0) = l /\
    (access a0 i) = (access a j) /\ (access a0 j) = (access a i) /\
    (forall (k:Z),
     (0 <= k /\ k < l -> (k <> i -> (k <> j -> (access a0 k) = (access a k)))))))).

(* Why obligation from file "max.mlw", characters 565-570 *)
Lemma pgm_max_end_po_1 : 
  forall (a: (array Z)),
  forall (Pre15: (array_length a) = l),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre11: Variant1 = (l - y1)),
  forall (Pre10: (0 <= y1 /\ y1 <= l) /\ (0 <= x1 /\ x1 < l) /\
                 (forall (k:Z),
                  (0 <= k /\ k < y1 -> (access a k) <= (access a x1)))),
  forall (Test4: y1 < l),
  0 <= y1 /\ y1 < (array_length a).
Proof.
auto with *.
Qed.

(* Why obligation from file "max.mlw", characters 573-578 *)
Lemma pgm_max_end_po_2 : 
  forall (a: (array Z)),
  forall (Pre15: (array_length a) = l),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre11: Variant1 = (l - y1)),
  forall (Pre10: (0 <= y1 /\ y1 <= l) /\ (0 <= x1 /\ x1 < l) /\
                 (forall (k:Z),
                  (0 <= k /\ k < y1 -> (access a k) <= (access a x1)))),
  forall (Test4: y1 < l),
  forall (Pre8: 0 <= y1 /\ y1 < (array_length a)),
  0 <= x1 /\ x1 < (array_length a).
Proof.
auto with *.
Qed.

(* Why obligation from file "max.mlw", characters 584-591 *)
Lemma pgm_max_end_po_3 : 
  forall (a: (array Z)),
  forall (Pre15: (array_length a) = l),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre11: Variant1 = (l - y1)),
  forall (Pre10: (0 <= y1 /\ y1 <= l) /\ (0 <= x1 /\ x1 < l) /\
                 (forall (k:Z),
                  (0 <= k /\ k < y1 -> (access a k) <= (access a x1)))),
  forall (Test4: y1 < l),
  forall (Pre8: 0 <= y1 /\ y1 < (array_length a)),
  forall (Pre9: 0 <= x1 /\ x1 < (array_length a)),
  forall (Test3: (access a y1) > (access a x1)),
  forall (x2: Z),
  forall (Post3: x2 = y1),
  forall (y: Z),
  forall (HW_2: y = (y1 + 1)),
  ((0 <= y /\ y <= l) /\ (0 <= x2 /\ x2 < l) /\
  (forall (k:Z), (0 <= k /\ k < y -> (access a k) <= (access a x2)))) /\
  (Zwf 0 (l - y) (l - y1)).
Proof.
intuition.
assert ((k < y1)%Z \/ k = y1).
 omega.
 intuition.
subst; generalize (H7 k); intuition.
subst; intuition.
Qed.

(* Why obligation from file "max.mlw", characters 591-591 *)
Lemma pgm_max_end_po_4 : 
  forall (a: (array Z)),
  forall (Pre15: (array_length a) = l),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre11: Variant1 = (l - y1)),
  forall (Pre10: (0 <= y1 /\ y1 <= l) /\ (0 <= x1 /\ x1 < l) /\
                 (forall (k:Z),
                  (0 <= k /\ k < y1 -> (access a k) <= (access a x1)))),
  forall (Test4: y1 < l),
  forall (Pre8: 0 <= y1 /\ y1 < (array_length a)),
  forall (Pre9: 0 <= x1 /\ x1 < (array_length a)),
  forall (Test2: (access a y1) <= (access a x1)),
  forall (y: Z),
  forall (HW_4: y = (y1 + 1)),
  ((0 <= y /\ y <= l) /\ (0 <= x1 /\ x1 < l) /\
  (forall (k:Z), (0 <= k /\ k < y -> (access a k) <= (access a x1)))) /\
  (Zwf 0 (l - y) (l - y1)).
Proof.
intuition.
assert ((k < y1)%Z \/ k = y1).
 omega.
 intuition.
subst; intuition.
Qed.

(* Why obligation from file "max.mlw", characters 415-620 *)
Lemma pgm_max_end_po_5 : 
  forall (a: (array Z)),
  forall (Pre15: (array_length a) = l),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre11: Variant1 = (l - y1)),
  forall (Pre10: (0 <= y1 /\ y1 <= l) /\ (0 <= x1 /\ x1 < l) /\
                 (forall (k:Z),
                  (0 <= k /\ k < y1 -> (access a k) <= (access a x1)))),
  forall (Test1: y1 >= l),
  forall (a0: (array Z)),
  forall (HW_6: (array_length a0) = l /\ (access a0 x1) =
                (access a (l - 1)) /\ (access a0 (l - 1)) = (access a x1) /\
                (forall (k:Z),
                 (0 <= k /\ k < l ->
                  (k <> x1 -> (k <> (l - 1) -> (access a0 k) = (access a k)))))),
  (forall (k:Z),
   (0 <= k /\ k < (l - 1) -> (k <> x1 -> (access a0 k) = (access a k)))) /\
  (access a0 x1) = (access a (l - 1)) /\ (access a0 (l - 1)) =
  (access a x1) /\
  (forall (k:Z),
   (0 <= k /\ k < (l - 1) -> (access a0 k) <= (access a0 (l - 1)))).
Proof.
intuition.
assert (k = x1 \/ k <> x1).
 omega.
 intuition.
subst; intuition.
rewrite H6; rewrite H5; apply H3; omega.
rewrite H5.
 rewrite H8; try omega.
apply H3; omega.
Qed.

(* Why obligation from file "max.mlw", characters 415-620 *)
Lemma pgm_max_end_po_6 : 
  forall (a: (array Z)),
  forall (Pre15: (array_length a) = l),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  forall (Variant1: Z),
  forall (x1: Z),
  forall (y1: Z),
  forall (Pre11: Variant1 = (l - y1)),
  forall (Pre10: (0 <= y1 /\ y1 <= l) /\ (0 <= x1 /\ x1 < l) /\
                 (forall (k:Z),
                  (0 <= k /\ k < y1 -> (access a k) <= (access a x1)))),
  forall (Test1: y1 >= l),
  (array_length a) = l.
Proof.
intuition.
Qed.

(* Why obligation from file "max.mlw", characters 449-533 *)
Lemma pgm_max_end_po_7 : 
  forall (a: (array Z)),
  forall (Pre15: (array_length a) = l),
  forall (x0: Z),
  forall (Post1: x0 = 0),
  forall (y0: Z),
  forall (Post2: y0 = 1),
  (0 <= y0 /\ y0 <= l) /\ (0 <= x0 /\ x0 < l) /\
  (forall (k:Z), (0 <= k /\ k < y0 -> (access a k) <= (access a x0))).
Proof.
generalize l_pos; intuition.
assert (k = 0%Z \/ (0 < k)%Z).
 omega.
 intuition.
subst; intuition.
Save.

