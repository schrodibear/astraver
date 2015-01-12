(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)

Require Why.
Require Sumbool.

(*Why*) Parameter N : Z.

Axiom N_non_negative : `0 <= N`.

Inductive color : Set := blue : color | white : color | red : color.

Lemma eq_color_dec : (c1,c2:color) { c1=c2 } + { ~c1=c2 }.
Proof. 
Intros; Decide Equality c1 c2.
Save.

Definition eq_blue :=  [c](bool_of_sumbool (eq_color_dec c blue)).
Definition eq_white := [c](bool_of_sumbool (eq_color_dec c white)).

Definition monochrome [t:(array color); i,j:Z; c:color] : Prop :=
  (k:Z)`i <= k < j` -> #t[k]=c.

(* Why obligation from file "flag.mlw", characters 721-726 *)
Lemma dutch_flag_po_1 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  `0 <= i1` /\ `i1 < (array_length t0)`.
Proof.
Intuition.
Save.

(* Why obligation from file "flag.mlw", characters 754-759 *)
Lemma dutch_flag_po_2 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test5: (access t0 i1) = blue)
  `0 <= b1` /\ `b1 < (array_length t0)`.
Proof.
Intuition.
Save.

(* Why obligation from file "flag.mlw", characters 785-795 *)
Lemma dutch_flag_po_3 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test5: (access t0 i1) = blue)
  (Pre14: `0 <= b1` /\ `b1 < (array_length t0)`)
  (u: color)
  (Post3: u = (access t0 b1))
  (Pre12: `0 <= b1` /\ `b1 < (array_length t0)`)
  (Pre13: `0 <= i1` /\ `i1 < (array_length t0)`)
  (t1: (array color))
  (Post1: t1 = (store t0 b1 (access t0 i1)))
  `0 <= i1` /\ `i1 < (array_length t1)`.
Proof.
Intuition.
ArraySubst t1.
Save.

(* Why obligation from file "flag.mlw", characters 763-799 *)
Lemma dutch_flag_po_4 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test5: (access t0 i1) = blue)
  (Pre14: `0 <= b1` /\ `b1 < (array_length t0)`)
  (u: color)
  (Post3: u = (access t0 b1))
  (Pre12: `0 <= b1` /\ `b1 < (array_length t0)`)
  (Pre13: `0 <= i1` /\ `i1 < (array_length t0)`)
  (t1: (array color))
  (Post1: t1 = (store t0 b1 (access t0 i1)))
  (Pre11: `0 <= i1` /\ `i1 < (array_length t1)`)
  (t2: (array color))
  (Post2: t2 = (store t1 i1 u))
  ((b:Z)
   (b = `b1 + 1` ->
    ((i:Z)
     (i = `i1 + 1` -> ((`0 <= b` /\ `b <= i`) /\ (`i <= r1` /\ `r1 <= N`) /\
      (monochrome t2 `0` b blue) /\ (monochrome t2 b i white) /\
      (monochrome t2 r1 N red) /\ `(array_length t2) = N`) /\
      (Zwf `0` `r1 - i` `r1 - i1`))))).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Assert h:`k < b1` \/ k=b1. Omega. Intuition.
Subst t2; AccessOther.
Subst t1; AccessOther.
Auto.
Subst t1; Simpl; Auto.
Assert h:`b1 = i1` \/ `b1 < i1`. Omega. Intuition.
Subst k t2 b1.
AccessSame.
Subst u; Assumption.
Subst t2; AccessOther.
Subst k; AccessSame.
Assumption.
Subst t1; Simpl; Auto.
Assert h:`k = i1` \/ `k < i1`. Omega. Intuition.
Subst t2 k; AccessSame.
Subst u; Apply H7; Omega.
Subst t2; AccessOther.
AccessOther.
Apply H7; Omega.
Subst t1; Simpl; Auto.
Subst t2; AccessOther.
AccessOther.
Apply H9; Omega.
Subst t1; Simpl; Auto.
Subst t2; Simpl; Auto.
Save.

(* Why obligation from file "flag.mlw", characters 886-897 *)
Lemma dutch_flag_po_5 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test4: ~((access t0 i1) = blue))
  (Pre10: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test3: (access t0 i1) = white)
  (i2: Z)
  (Post6: i2 = `i1 + 1`)
  ((`0 <= b1` /\ `b1 <= i2`) /\ (`i2 <= r1` /\ `r1 <= N`) /\
  (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i2 white) /\
  (monochrome t0 r1 N red) /\ `(array_length t0) = N`) /\
  (Zwf `0` `r1 - i2` `r1 - i1`).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Assert h:`k<i1` \/ k=i1. Omega. Intuition.
Subst k; Assumption.
Save.

(* Why obligation from file "flag.mlw", characters 949-954 *)
Lemma dutch_flag_po_6 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test4: ~((access t0 i1) = blue))
  (Pre10: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test2: ~((access t0 i1) = white))
  (r2: Z)
  (Post7: r2 = `r1 - 1`)
  `0 <= r2` /\ `r2 < (array_length t0)`.
Proof.
Intuition.
Save.

(* Why obligation from file "flag.mlw", characters 980-990 *)
Lemma dutch_flag_po_7 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test4: ~((access t0 i1) = blue))
  (Pre10: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test2: ~((access t0 i1) = white))
  (r2: Z)
  (Post7: r2 = `r1 - 1`)
  (Pre9: `0 <= r2` /\ `r2 < (array_length t0)`)
  (u: color)
  (Post10: u = (access t0 r2))
  (Pre7: `0 <= r2` /\ `r2 < (array_length t0)`)
  (Pre8: `0 <= i1` /\ `i1 < (array_length t0)`)
  (t1: (array color))
  (Post8: t1 = (store t0 r2 (access t0 i1)))
  `0 <= i1` /\ `i1 < (array_length t1)`.
Proof.
Unfold monochrome; Intuition
  (Try Subst result; Try Subst result0; Try Subst result1;
  Try Omega).
ArraySubst t1.
Save.

(* Why obligation from file "flag.mlw", characters 958-994 *)
Lemma dutch_flag_po_8 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test6: `i1 < r1`)
  (Pre15: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test4: ~((access t0 i1) = blue))
  (Pre10: `0 <= i1` /\ `i1 < (array_length t0)`)
  (Test2: ~((access t0 i1) = white))
  (r2: Z)
  (Post7: r2 = `r1 - 1`)
  (Pre9: `0 <= r2` /\ `r2 < (array_length t0)`)
  (u: color)
  (Post10: u = (access t0 r2))
  (Pre7: `0 <= r2` /\ `r2 < (array_length t0)`)
  (Pre8: `0 <= i1` /\ `i1 < (array_length t0)`)
  (t1: (array color))
  (Post8: t1 = (store t0 r2 (access t0 i1)))
  (Pre6: `0 <= i1` /\ `i1 < (array_length t1)`)
  (t2: (array color))
  (Post9: t2 = (store t1 i1 u))
  ((`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r2` /\ `r2 <= N`) /\
  (monochrome t2 `0` b1 blue) /\ (monochrome t2 b1 i1 white) /\
  (monochrome t2 r2 N red) /\ `(array_length t2) = N`) /\
  (Zwf `0` `r2 - i1` `r1 - i1`).
Proof.
Unfold monochrome Zwf; Intuition Try Omega.
Subst t2 t1; Do 2 AccessOther.
Apply H; Omega.
Subst t2 t1; Do 2 AccessOther. 
Apply H7; Omega.
Assert h:`k = r2` \/ `r2 < k`. Omega. Intuition.
Assert h':`k = i1` \/ `i1 < k`. Omega. Intuition.
Generalize H19; Clear H19; 
  Subst t2 t1 k; AccessSame; Intro H19.
Subst u; Rewrite <- H19; Subst r2.
Generalize Test4; Generalize Test2 ; Case (access t0 i1); Tauto.
Subst t2 t1 k; AccessOther.
Generalize Test4; Generalize Test2 ; Case (access t0 i1); Tauto.
Subst t2 t1; Do 2 AccessOther.
Apply H9; Omega.
Subst t2 t1; Simpl; Trivial.
Save.

(* Why obligation from file "flag.mlw", characters 473-1103 *)
Lemma dutch_flag_po_9 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (Variant1: Z)
  (b1: Z)
  (i1: Z)
  (r1: Z)
  (t0: (array color))
  (Pre17: Variant1 = `r1 - i1`)
  (Pre16: (`0 <= b1` /\ `b1 <= i1`) /\ (`i1 <= r1` /\ `r1 <= N`) /\
          (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 i1 white) /\
          (monochrome t0 r1 N red) /\ `(array_length t0) = N`)
  (Test1: `i1 >= r1`)
  (monochrome t0 `0` b1 blue) /\ (monochrome t0 b1 r1 white) /\
  (monochrome t0 r1 N red).
Proof.
Intuition.
Replace r1 with i1. Trivial. Omega. 
Save.

(* Why obligation from file "flag.mlw", characters 513-680 *)
Lemma dutch_flag_po_10 : 
  (t: (array color))
  (Pre18: `(array_length t) = N`)
  (b: Z)
  (Post13: b = `0`)
  (i: Z)
  (Post12: i = `0`)
  (r: Z)
  (Post11: r = N)
  (`0 <= b` /\ `b <= i`) /\ (`i <= r` /\ `r <= N`) /\
  (monochrome t `0` b blue) /\ (monochrome t b i white) /\
  (monochrome t r N red) /\ `(array_length t) = N`.
Proof.
Intuition.
Subst; Exact N_non_negative.
Unfold monochrome; Intros; Absurd `0<0`; Omega.
Unfold monochrome; Intros; Absurd `0<0`; Omega.
Unfold monochrome; Intros; Absurd `N<N`; Omega.
Save.

