(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Import Why.
Require Import Sumbool.

(*Why*) Parameter N : Z.

Axiom N_non_negative : (0 <= N)%Z.

Inductive color : Set :=
  | blue : color
  | white : color
  | red : color.

Lemma eq_color_dec : forall c1 c2:color, {c1 = c2} + {c1 <> c2}.
 Proof.
 intros; decide equality c1 c2.
Qed.

Definition eq_blue c := bool_of_sumbool (eq_color_dec c blue).
Definition eq_white c := bool_of_sumbool (eq_color_dec c white).

Definition monochrome (t:array color) (i j:Z) (c:color) : Prop :=
  forall k:Z, (i <= k < j)%Z -> access t k = c.

(* Why obligation from file "flag.mlw", characters 771-786 *)
Lemma dutch_flag_po_1 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  0 <= i1 /\ i1 < (array_length t0).
Proof.
intuition.
Qed.

(* Why obligation from file "flag.mlw", characters 813-818 *)
Lemma dutch_flag_po_2 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test5: (access t0 i1) = blue),
  0 <= b1 /\ b1 < (array_length t0).
Proof.
intuition.
Qed.

(* Why obligation from file "flag.mlw", characters 828-842 *)
Lemma dutch_flag_po_3 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test5: (access t0 i1) = blue),
  forall (Pre10: 0 <= b1 /\ b1 < (array_length t0)),
  forall (u: color),
  forall (Post26: u = (access t0 b1)),
  forall (Pre8: 0 <= i1 /\ i1 < (array_length t0)),
  forall (aux_2: color),
  forall (Post20: aux_2 = (access t0 i1)),
  forall (aux_1: Z),
  forall (Post19: aux_1 = b1),
  0 <= aux_1 /\ aux_1 < (array_length t0).
Proof.
intuition.
Qed.

(* Why obligation from file "flag.mlw", characters 828-842 *)
Lemma dutch_flag_po_4 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test5: (access t0 i1) = blue),
  forall (Pre10: 0 <= b1 /\ b1 < (array_length t0)),
  forall (u: color),
  forall (Post26: u = (access t0 b1)),
  forall (Pre8: 0 <= i1 /\ i1 < (array_length t0)),
  forall (aux_2: color),
  forall (Post20: aux_2 = (access t0 i1)),
  forall (aux_1: Z),
  forall (Post19: aux_1 = b1),
  forall (Pre7: 0 <= aux_1 /\ aux_1 < (array_length t0)),
  forall (t1: (array color)),
  forall (Post18: t1 = (store t0 aux_1 aux_2)),
  forall (result: color),
  forall (HW_3: result = u),
  forall (result0: Z),
  forall (HW_4: result0 = i1),
  forall (t: (array color)),
  forall (HW_5: t = (store t1 result0 result)),
  forall (b: Z),
  forall (HW_6: b = (b1 + 1)),
  forall (i: Z),
  forall (HW_7: i = (i1 + 1)),
  ((0 <= b /\ b <= i) /\ (i <= r1 /\ r1 <= N) /\ (monochrome t 0 b blue) /\
  (monochrome t b i white) /\ (monochrome t r1 N red) /\ (array_length t) =
  N) /\ (Zwf 0 (r1 - i) (r1 - i1)).
Proof.
unfold monochrome, Zwf; intuition try omega.
assert (h: (k < b1)%Z \/ k = b1).
 omega.
 intuition.
subst t2; AccessOther.
subst t1; AccessOther.
auto.
subst; simpl; auto.
subst; simpl; omega.
assert (h: b1 = i1 \/ (b1 < i1)).
 omega.
 intuition.
subst.
AccessSame.
assumption.
subst t2; AccessOther.
subst; AccessSame.
assumption.
subst t1; simpl; omega.
subst t1; simpl; omega.
assert (h: k = i1 \/ (k < i1)).
 omega.
 intuition.
subst; AccessSame.
apply H7; omega.
subst t2; AccessOther.
subst; AccessOther.
apply H7; omega.
subst t1; simpl; omega.
subst t1; simpl; omega.
subst t2; AccessOther.
subst; AccessOther.
apply H9; omega.
subst t1; simpl; omega.
subst t1; simpl; omega.
subst t2 t1; simpl; auto.
Qed.

(* Why obligation from file "flag.mlw", characters 828-842 *)
Lemma dutch_flag_po_5 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test5: (access t0 i1) = blue),
  forall (Pre10: 0 <= b1 /\ b1 < (array_length t0)),
  forall (u: color),
  forall (Post26: u = (access t0 b1)),
  forall (Pre8: 0 <= i1 /\ i1 < (array_length t0)),
  forall (aux_2: color),
  forall (Post20: aux_2 = (access t0 i1)),
  forall (aux_1: Z),
  forall (Post19: aux_1 = b1),
  forall (Pre7: 0 <= aux_1 /\ aux_1 < (array_length t0)),
  forall (t1: (array color)),
  forall (Post18: t1 = (store t0 aux_1 aux_2)),
  forall (result: color),
  forall (HW_3: result = u),
  forall (result0: Z),
  forall (HW_4: result0 = i1),
  0 <= result0 /\ result0 < (array_length t1).
Proof.
intuition; subst; auto.
Qed.

(* Why obligation from file "flag.mlw", characters 945-956 *)
Lemma dutch_flag_po_6 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test4: ~((access t0 i1) = blue)),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test3: (access t0 i1) = white),
  forall (i2: Z),
  forall (Post14: i2 = (i1 + 1)),
  ((0 <= b1 /\ b1 <= i2) /\ (i2 <= r1 /\ r1 <= N) /\
  (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i2 white) /\
  (monochrome t0 r1 N red) /\ (array_length t0) = N) /\
  (Zwf 0 (r1 - i2) (r1 - i1)).
Proof.
unfold monochrome, Zwf; intuition try omega.
assert (h: (k < i1)%Z \/ k = i1).
 omega.
 intuition.
subst k; assumption.
Qed.

(* Why obligation from file "flag.mlw", characters 1008-1013 *)
Lemma dutch_flag_po_7 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test4: ~((access t0 i1) = blue)),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test2: ~((access t0 i1) = white)),
  forall (r2: Z),
  forall (Post2: r2 = (r1 - 1)),
  0 <= r2 /\ r2 < (array_length t0).
Proof.
intuition; subst; omega.
Qed.

(* Why obligation from file "flag.mlw", characters 1023-1037 *)
Lemma dutch_flag_po_8 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test4: ~((access t0 i1) = blue)),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test2: ~((access t0 i1) = white)),
  forall (r2: Z),
  forall (Post2: r2 = (r1 - 1)),
  forall (Pre5: 0 <= r2 /\ r2 < (array_length t0)),
  forall (u: color),
  forall (Post13: u = (access t0 r2)),
  forall (Pre3: 0 <= i1 /\ i1 < (array_length t0)),
  forall (aux_6: color),
  forall (Post7: aux_6 = (access t0 i1)),
  forall (aux_5: Z),
  forall (Post6: aux_5 = r2),
  0 <= aux_5 /\ aux_5 < (array_length t0).
Proof.
intuition; subst; omega.
Qed.

(* Why obligation from file "flag.mlw", characters 1023-1037 *)
Lemma dutch_flag_po_9 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test4: ~((access t0 i1) = blue)),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test2: ~((access t0 i1) = white)),
  forall (r2: Z),
  forall (Post2: r2 = (r1 - 1)),
  forall (Pre5: 0 <= r2 /\ r2 < (array_length t0)),
  forall (u: color),
  forall (Post13: u = (access t0 r2)),
  forall (Pre3: 0 <= i1 /\ i1 < (array_length t0)),
  forall (aux_6: color),
  forall (Post7: aux_6 = (access t0 i1)),
  forall (aux_5: Z),
  forall (Post6: aux_5 = r2),
  forall (Pre2: 0 <= aux_5 /\ aux_5 < (array_length t0)),
  forall (t1: (array color)),
  forall (Post5: t1 = (store t0 aux_5 aux_6)),
  forall (result: color),
  forall (HW_41: result = u),
  forall (result0: Z),
  forall (HW_42: result0 = i1),
  forall (t: (array color)),
  forall (HW_43: t = (store t1 result0 result)),
  ((0 <= b1 /\ b1 <= i1) /\ (i1 <= r2 /\ r2 <= N) /\
  (monochrome t 0 b1 blue) /\ (monochrome t b1 i1 white) /\
  (monochrome t r2 N red) /\ (array_length t) = N) /\
  (Zwf 0 (r2 - i1) (r1 - i1)).
Proof.
unfold monochrome, Zwf; intuition try omega.
subst t2 t1; do 2 AccessOther.
apply H; omega.
subst t2 t1; do 2 AccessOther.
 apply H7; omega.
assert (h: k = r2 \/ (r2 < k)).
 omega.
 intuition.
assert (h': k = i1 \/ (i1 < k)).
 omega.
 intuition.
generalize H19; clear H19; subst t2 k result0 i1; AccessSame. intro H19.
subst.
generalize Test4; generalize Test2; case (access t0 (r1-1)); tauto.
subst; simpl; auto.
subst; AccessOther.
generalize Test4; generalize Test2; case (access t0 i1); tauto.
subst; do 2 AccessOther.
apply H9; omega.
subst t2 t1; simpl; trivial.
 Qed.

(* Why obligation from file "flag.mlw", characters 1023-1037 *)
Lemma dutch_flag_po_10 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test6: i1 < r1),
  forall (Pre11: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test4: ~((access t0 i1) = blue)),
  forall (Pre6: 0 <= i1 /\ i1 < (array_length t0)),
  forall (Test2: ~((access t0 i1) = white)),
  forall (r2: Z),
  forall (Post2: r2 = (r1 - 1)),
  forall (Pre5: 0 <= r2 /\ r2 < (array_length t0)),
  forall (u: color),
  forall (Post13: u = (access t0 r2)),
  forall (Pre3: 0 <= i1 /\ i1 < (array_length t0)),
  forall (aux_6: color),
  forall (Post7: aux_6 = (access t0 i1)),
  forall (aux_5: Z),
  forall (Post6: aux_5 = r2),
  forall (Pre2: 0 <= aux_5 /\ aux_5 < (array_length t0)),
  forall (t1: (array color)),
  forall (Post5: t1 = (store t0 aux_5 aux_6)),
  forall (result: color),
  forall (HW_41: result = u),
  forall (result0: Z),
  forall (HW_42: result0 = i1),
  0 <= result0 /\ result0 < (array_length t1).
Proof.
intuition.
subst; simpl; auto.
Qed.


(* Why obligation from file "flag.mlw", characters 532-1162 *)
Lemma dutch_flag_po_11 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  forall (Variant1: Z),
  forall (b1: Z),
  forall (i1: Z),
  forall (r1: Z),
  forall (t0: (array color)),
  forall (Pre13: Variant1 = (r1 - i1)),
  forall (Pre12: (0 <= b1 /\ b1 <= i1) /\ (i1 <= r1 /\ r1 <= N) /\
                 (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 i1 white) /\
                 (monochrome t0 r1 N red) /\ (array_length t0) = N),
  forall (Test1: i1 >= r1),
  (monochrome t0 0 b1 blue) /\ (monochrome t0 b1 r1 white) /\
  (monochrome t0 r1 N red).
Proof.
intuition.
replace r1 with i1.
 trivial.
 omega.
Save.

(* Why obligation from file "flag.mlw", characters 572-739 *)
Lemma dutch_flag_po_12 : 
  forall (t: (array color)),
  forall (Pre14: (array_length t) = N),
  forall (b: Z),
  forall (Post32: b = 0),
  forall (i: Z),
  forall (Post31: i = 0),
  forall (r: Z),
  forall (Post30: r = N),
  (0 <= b /\ b <= i) /\ (i <= r /\ r <= N) /\ (monochrome t 0 b blue) /\
  (monochrome t b i white) /\ (monochrome t r N red) /\ (array_length t) = N.
Proof.
intuition.
subst; exact N_non_negative.
unfold monochrome; intros; absurd (0 < 0)%Z; omega.
unfold monochrome; intros; absurd (0 < 0)%Z; omega.
unfold monochrome; intros; absurd (N < N)%Z; omega.
Save.

