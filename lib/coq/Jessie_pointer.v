(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require int.Int.

Axiom pointer : forall (t:Type), Type.
Parameter pointer_WhyType : forall (t:Type) {t_WT:WhyType t},
  WhyType (pointer t).
Existing Instance pointer_WhyType.

Parameter null: forall {t:Type} {t_WT:WhyType t}, (pointer t).

Parameter sub_pointer: forall {t:Type} {t_WT:WhyType t}, (pointer t) ->
  (pointer t) -> Z.

Parameter shift: forall {t:Type} {t_WT:WhyType t}, (pointer t) -> Z ->
  (pointer t).

Parameter same_block: forall {t:Type} {t_WT:WhyType t}, (pointer t) ->
  (pointer t) -> Prop.

Axiom Sub_pointer_def : forall {t:Type} {t_WT:WhyType t}, forall (a:(pointer
  t)), forall (i:Z) (j:Z), ((sub_pointer (shift a i) (shift a
  j)) = (i - j)%Z).

Axiom Shift_def1 : forall {t:Type} {t_WT:WhyType t}, forall (a:(pointer t)),
  forall (i:Z), forall (j:Z), ((shift (shift a i) j) = (shift a (i + j)%Z)).

Axiom Shift_def2 : forall {t:Type} {t_WT:WhyType t}, forall (a:(pointer t)),
  ((shift a 0%Z) = a).

Axiom Same_block_def : forall {t:Type} {t_WT:WhyType t}, forall (a:(pointer
  t)) (b:(pointer t)), (same_block a b) <-> exists i:Z, (a = (shift b i)).

Axiom Sub_pointer_shift : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)) (q:(pointer t)), (same_block p q) -> (p = (shift q
  (sub_pointer p q))).

Axiom Sub_pointer_self : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), ((sub_pointer p p) = 0%Z).

Axiom Sub_pointer_zero : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)) (q:(pointer t)), (same_block p q) -> (((sub_pointer p q) = 0%Z) ->
  (p = q)).

Axiom Sub_pointer_shift_left : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)) (q:(pointer t)) (i:Z), (same_block p q) ->
  ((sub_pointer (shift p i) q) = ((sub_pointer p q) + i)%Z).

Axiom Sub_pointer_shift_right : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)) (q:(pointer t)) (i:Z), (same_block p q) ->
  ((sub_pointer p (shift q i)) = ((sub_pointer p q) - i)%Z).

Axiom Sub_pointer_neg : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)) (q:(pointer t)), (same_block p q) -> ((sub_pointer p
  q) = (-(sub_pointer q p))%Z).

Axiom Shift_shift : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer t)),
  forall (i:Z) (j:Z), ((shift (shift p i) j) = (shift p (i + j)%Z)).

Axiom Neq_shift : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer t)),
  forall (i:Z), forall (j:Z), (~ (i = j)) -> ~ ((shift p i) = (shift p j)).

Axiom Same_block_refl : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), (same_block p p).

Axiom Same_block_shift : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (i:Z), (same_block p (shift p i)).

Axiom Same_block_symm : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (q:(pointer t)), (same_block p q) <-> (same_block q p).

Axiom Same_block_trans : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (q:(pointer t)), forall (r:(pointer t)), ((same_block p q) /\
  (same_block q r)) -> (same_block p r).

Axiom Same_block_shift_right : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pointer t)), forall (i:Z), (same_block p
  q) -> (same_block p (shift q i)).

Axiom Same_block_shift_left : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pointer t)), forall (i:Z), (same_block q
  p) -> (same_block (shift q i) p).

