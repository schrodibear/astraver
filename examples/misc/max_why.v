
Require Why.

Parameter l : Z.
Axiom l_pos : `0 < l`.

(*Why*) Parameter swap :
  (i: Z)(j: Z)(a: (array Z))(_: `(array_length a) = l`)
  (sig_2 (array Z) unit [a0: (array Z)][result: unit]
   (`(array_length a0) = l` /\ `(access a0 i) = (access a j)` /\
   `(access a0 j) = (access a i)` /\
   ((k:Z)
    (`0 <= k` /\ `k < l` ->
     (`k <> i` -> (`k <> j` -> `(access a0 k) = (access a k)`)))))).

(* Why obligation from file "max.mlw", characters 555-560 *)
Lemma pgm_max_end_po_1 : 
  (a: (array Z))
  (Pre15: `(array_length a) = l`)
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (x1: Z)
  (y1: Z)
  (Pre11: Variant1 = `l - y1`)
  (Pre10: (`0 <= y1` /\ `y1 <= l`) /\ (`0 <= x1` /\ `x1 < l`) /\
          ((k:Z) (`0 <= k` /\ `k < y1` -> `(access a k) <= (access a x1)`)))
  (Test4: `y1 < l`)
  `0 <= y1` /\ `y1 < (array_length a)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "max.mlw", characters 563-568 *)
Lemma pgm_max_end_po_2 : 
  (a: (array Z))
  (Pre15: `(array_length a) = l`)
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (x1: Z)
  (y1: Z)
  (Pre11: Variant1 = `l - y1`)
  (Pre10: (`0 <= y1` /\ `y1 <= l`) /\ (`0 <= x1` /\ `x1 < l`) /\
          ((k:Z) (`0 <= k` /\ `k < y1` -> `(access a k) <= (access a x1)`)))
  (Test4: `y1 < l`)
  (Pre8: `0 <= y1` /\ `y1 < (array_length a)`)
  `0 <= x1` /\ `x1 < (array_length a)`.
Proof.
Auto with *.
Save.

(* Why obligation from file "max.mlw", characters 574-581 *)
Lemma pgm_max_end_po_3 : 
  (a: (array Z))
  (Pre15: `(array_length a) = l`)
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (x1: Z)
  (y1: Z)
  (Pre11: Variant1 = `l - y1`)
  (Pre10: (`0 <= y1` /\ `y1 <= l`) /\ (`0 <= x1` /\ `x1 < l`) /\
          ((k:Z) (`0 <= k` /\ `k < y1` -> `(access a k) <= (access a x1)`)))
  (Test4: `y1 < l`)
  (Pre8: `0 <= y1` /\ `y1 < (array_length a)`)
  (Pre9: `0 <= x1` /\ `x1 < (array_length a)`)
  (Test3: `(access a y1) > (access a x1)`)
  (x2: Z)
  (Post3: x2 = y1)
  ((y:Z)
   (y = `y1 + 1` -> ((`0 <= y` /\ `y <= l`) /\ (`0 <= x2` /\ `x2 < l`) /\
    ((k:Z) (`0 <= k` /\ `k < y` -> `(access a k) <= (access a x2)`))) /\
    (Zwf `0` `l - y` `l - y1`))).
Proof.
Intuition.
Assert `k<y1` \/ k=y1. Omega. Intuition.
Subst; Generalize (H7 k); Intuition.
Subst; Intuition.
Unfold Zwf; Intuition.
Save.

(* Why obligation from file "max.mlw", characters 552-581 *)
Lemma pgm_max_end_po_4 : 
  (a: (array Z))
  (Pre15: `(array_length a) = l`)
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `1`)
  (Variant1: Z)
  (x1: Z)
  (y1: Z)
  (Pre11: Variant1 = `l - y1`)
  (Pre10: (`0 <= y1` /\ `y1 <= l`) /\ (`0 <= x1` /\ `x1 < l`) /\
          ((k:Z) (`0 <= k` /\ `k < y1` -> `(access a k) <= (access a x1)`)))
  (Test4: `y1 < l`)
  (Pre8: `0 <= y1` /\ `y1 < (array_length a)`)
  (Pre9: `0 <= x1` /\ `x1 < (array_length a)`)
  (Test2: `(access a y1) <= (access a x1)`)
  ((y:Z)
   (y = `y1 + 1` -> ((`0 <= y` /\ `y <= l`) /\ (`0 <= x1` /\ `x1 < l`) /\
    ((k:Z) (`0 <= k` /\ `k < y` -> `(access a k) <= (access a x1)`))) /\
    (Zwf `0` `l - y` `l - y1`))).
Proof.
Intuition.
Assert `k<y1` \/ k=y1. Omega. Intuition.
Subst; Intuition.
Unfold Zwf; Intuition.
Save.

(* Why obligation from file "max.mlw", characters 439-523 *)
Lemma pgm_max_end_po_5 : 
  (a: (array Z))
  (Pre15: `(array_length a) = l`)
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `1`)
  (`0 <= y0` /\ `y0 <= l`) /\ (`0 <= x0` /\ `x0 < l`) /\
  ((k:Z) (`0 <= k` /\ `k < y0` -> `(access a k) <= (access a x0)`)).
Proof.
Generalize l_pos; Intuition.
Assert `k=0` \/ `0<k`. Omega. Intuition.
Subst; Intuition.
Save.

(* Why obligation from file "max.mlw", characters 345-797 *)
Lemma pgm_max_end_po_6 : 
  (a: (array Z))
  (Pre15: `(array_length a) = l`)
  (x0: Z)
  (Post1: x0 = `0`)
  (y0: Z)
  (Post2: y0 = `1`)
  (x1: Z)
  (y1: Z)
  (Post5: ((`0 <= y1` /\ `y1 <= l`) /\ (`0 <= x1` /\ `x1 < l`) /\
          ((k:Z) (`0 <= k` /\ `k < y1` -> `(access a k) <= (access a x1)`))) /\
          `y1 >= l`)
  (Pre14: `(array_length a) = l`)
  (a0: (array Z))
  (Post10: `(array_length a0) = l` /\ `(access a0 x1) = (access a l - 1)` /\
           `(access a0 l - 1) = (access a x1)` /\
           ((k:Z)
            (`0 <= k` /\ `k < l` ->
             (`k <> x1` -> (`k <> l - 1` -> `(access a0 k) = (access a k)`)))))
  ((k:Z)
   (`0 <= k` /\ `k < l - 1` -> (`k <> x1` -> `(access a0 k) = (access a k)`))) /\
  `(access a0 x1) = (access a l - 1)` /\
  `(access a0 l - 1) = (access a x1)` /\
  ((k:Z) (`0 <= k` /\ `k < l - 1` -> `(access a0 k) <= (access a0 l - 1)`)).
Proof.
Intuition.
Assert k=x1 \/ ~k=x1. Omega. Intuition.
Subst; Intuition.
Rewrite H7; Rewrite H6; Apply H4; Omega.
Rewrite H6. Rewrite H9; Try Omega.
Apply H4; Omega.
Save.

