(* Load Programs. *)
Require Import Why.

Parameter l : Z.
Axiom l_pos : (0 < l)%Z.

(*Why*) Parameter
          swap :
            forall (i j:Z) (a:array Z) (x_:array_length a = l),
              sig_2 (array Z) unit
                (fun (a0:array Z) (result:unit) =>
                   array_length a0 = l /\
                   access a0 i = access a j /\
                   access a0 j = access a i /\
                   (forall k:Z,
                      (0 <= k)%Z /\ (k < l)%Z ->
                      k <> i -> k <> j -> access a0 k = access a k)).

(* Why obligation from file , characters 555-560 *)
Lemma pgm_max_end_po_1 :
 forall (a:array Z) (Pre15:array_length a = l) (x0:Z) (Post1:x0 = 0%Z)
   (y0:Z) (Post2:y0 = 1%Z) (Variant1 x1 y1:Z)
   (Pre11:Variant1 = (l - y1)%Z)
   (Pre10:((0 <= y1)%Z /\ (y1 <= l)%Z) /\
          ((0 <= x1)%Z /\ (x1 < l)%Z) /\
          (forall k:Z,
             (0 <= k)%Z /\ (k < y1)%Z -> (access a k <= access a x1)%Z))
   (Test4:(y1 < l)%Z), (0 <= y1)%Z /\ (y1 < array_length a)%Z.
Proof.
auto with *.
Qed.

(* Why obligation from file , characters 563-568 *)
Lemma pgm_max_end_po_2 :
 forall (a:array Z) (Pre15:array_length a = l) (x0:Z) (Post1:x0 = 0%Z)
   (y0:Z) (Post2:y0 = 1%Z) (Variant1 x1 y1:Z)
   (Pre11:Variant1 = (l - y1)%Z)
   (Pre10:((0 <= y1)%Z /\ (y1 <= l)%Z) /\
          ((0 <= x1)%Z /\ (x1 < l)%Z) /\
          (forall k:Z,
             (0 <= k)%Z /\ (k < y1)%Z -> (access a k <= access a x1)%Z))
   (Test4:(y1 < l)%Z) (Pre8:(0 <= y1)%Z /\ (y1 < array_length a)%Z),
   (0 <= x1)%Z /\ (x1 < array_length a)%Z.
Proof.
auto with *.
Qed.

(* Why obligation from file , characters 574-581 *)
Lemma pgm_max_end_po_3 :
 forall (a:array Z) (Pre15:array_length a = l) (x0:Z) (Post1:x0 = 0%Z)
   (y0:Z) (Post2:y0 = 1%Z) (Variant1 x1 y1:Z)
   (Pre11:Variant1 = (l - y1)%Z)
   (Pre10:((0 <= y1)%Z /\ (y1 <= l)%Z) /\
          ((0 <= x1)%Z /\ (x1 < l)%Z) /\
          (forall k:Z,
             (0 <= k)%Z /\ (k < y1)%Z -> (access a k <= access a x1)%Z))
   (Test4:(y1 < l)%Z) (Pre8:(0 <= y1)%Z /\ (y1 < array_length a)%Z)
   (Pre9:(0 <= x1)%Z /\ (x1 < array_length a)%Z)
   (Test3:(access a y1 > access a x1)%Z) (x2:Z) (Post3:x2 = y1) 
   (y:Z),
   y = (y1 + 1)%Z ->
   (((0 <= y)%Z /\ (y <= l)%Z) /\
    ((0 <= x2)%Z /\ (x2 < l)%Z) /\
    (forall k:Z,
       (0 <= k)%Z /\ (k < y)%Z -> (access a k <= access a x2)%Z)) /\
   Zwf 0 (l - y) (l - y1).
Proof.
intuition.
assert ((k < y1)%Z \/ k = y1).
 omega.
 intuition.
subst; generalize (H7 k); intuition.
subst; intuition.
Qed.

(* Why obligation from file , characters 581-581 *)
Lemma pgm_max_end_po_4 :
 forall (a:array Z) (Pre15:array_length a = l) (x0:Z) (Post1:x0 = 0%Z)
   (y0:Z) (Post2:y0 = 1%Z) (Variant1 x1 y1:Z)
   (Pre11:Variant1 = (l - y1)%Z)
   (Pre10:((0 <= y1)%Z /\ (y1 <= l)%Z) /\
          ((0 <= x1)%Z /\ (x1 < l)%Z) /\
          (forall k:Z,
             (0 <= k)%Z /\ (k < y1)%Z -> (access a k <= access a x1)%Z))
   (Test4:(y1 < l)%Z) (Pre8:(0 <= y1)%Z /\ (y1 < array_length a)%Z)
   (Pre9:(0 <= x1)%Z /\ (x1 < array_length a)%Z)
   (Test2:(access a y1 <= access a x1)%Z) (y:Z),
   y = (y1 + 1)%Z ->
   (((0 <= y)%Z /\ (y <= l)%Z) /\
    ((0 <= x1)%Z /\ (x1 < l)%Z) /\
    (forall k:Z,
       (0 <= k)%Z /\ (k < y)%Z -> (access a k <= access a x1)%Z)) /\
   Zwf 0 (l - y) (l - y1).
Proof.
intuition.
assert ((k < y1)%Z \/ k = y1).
 omega.
 intuition.
subst; intuition.
Qed.

(* Why obligation from file , characters 439-523 *)
Lemma pgm_max_end_po_5 :
 forall (a:array Z) (Pre15:array_length a = l) (x0:Z) (Post1:x0 = 0%Z)
   (y0:Z) (Post2:y0 = 1%Z),
   ((0 <= y0)%Z /\ (y0 <= l)%Z) /\
   ((0 <= x0)%Z /\ (x0 < l)%Z) /\
   (forall k:Z,
      (0 <= k)%Z /\ (k < y0)%Z -> (access a k <= access a x0)%Z).
Proof.
generalize l_pos; intuition.
assert (k = 0%Z \/ (0 < k)%Z).
 omega.
 intuition.
subst; intuition.
Qed.

(* Why obligation from file , characters 345-797 *)
Lemma pgm_max_end_po_6 :
 forall (a:array Z) (Pre15:array_length a = l) (x0:Z) (Post1:x0 = 0%Z)
   (y0:Z) (Post2:y0 = 1%Z) (x1 y1:Z)
   (Post5:(((0 <= y1)%Z /\ (y1 <= l)%Z) /\
           ((0 <= x1)%Z /\ (x1 < l)%Z) /\
           (forall k:Z,
              (0 <= k)%Z /\ (k < y1)%Z -> (access a k <= access a x1)%Z)) /\
          (y1 >= l)%Z) (Pre14:array_length a = l) (a0:array Z)
   (Post10:array_length a0 = l /\
           access a0 x1 = access a (l - 1) /\
           access a0 (l - 1) = access a x1 /\
           (forall k:Z,
              (0 <= k)%Z /\ (k < l)%Z ->
              k <> x1 -> k <> (l - 1)%Z -> access a0 k = access a k)),
   (forall k:Z,
      (0 <= k)%Z /\ (k < l - 1)%Z ->
      k <> x1 -> access a0 k = access a k) /\
   access a0 x1 = access a (l - 1) /\
   access a0 (l - 1) = access a x1 /\
   (forall k:Z,
      (0 <= k)%Z /\ (k < l - 1)%Z ->
      (access a0 k <= access a0 (l - 1))%Z).
Proof.
intuition.
assert (k = x1 \/ k <> x1).
 omega.
 intuition.
subst; intuition.
rewrite H7; rewrite H6; apply H4; omega.
rewrite H6.
 rewrite H9; try omega.
apply H4; omega.
Qed.

