(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require Import ZOdiv.
Require Import Rbasic_fun.
Require Import R_sqrt.
Require Import Rtrigo.
Require Import AltSeries. (* for def of pi *)
Definition unit  := unit.

Parameter mark : Type.

Parameter at1: forall (a:Type), a -> mark -> a.

Implicit Arguments at1.

Parameter old: forall (a:Type), a -> a.

Implicit Arguments old.

Axiom Inv_unit : forall (x:Z) (y:Z), ((x + (-y)%Z)%Z = 0%Z) -> (x = y).

Axiom Abs_le : forall (x:Z) (y:Z), ((Zabs x) <= y)%Z <-> (((-y)%Z <= x)%Z /\
  (x <= y)%Z).

Axiom Abs_zero : forall (x:Z), ((Zabs x) = 0%Z) -> (x = 0%Z).

Axiom Inv_unit1 : forall (x:R) (y:R), ((x + (-y)%R)%R = 0%R) -> (x = y).

Axiom sub_zero : forall (x:R) (y:R), ((x - y)%R = 0%R) -> (x = y).

Axiom Abs_zero1 : forall (x:R), ((Rabs x) = 0%R) -> (x = 0%R).

Axiom Pi_interval : ((314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038196 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)%R <  PI)%R /\
  (PI <  (314159265358979323846264338327950288419716939937510582097494459230781640628620899862803482534211706798214808651328230664709384460955058223172535940812848111745028410270193852110555964462294895493038197 / 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)%R)%R.

Axiom Cos_plus_pi : forall (x:R),
  ((Rtrigo_def.cos (x + PI)%R) = (-(Rtrigo_def.cos x))%R).

Axiom Sin_plus_pi : forall (x:R),
  ((Rtrigo_def.sin (x + PI)%R) = (-(Rtrigo_def.sin x))%R).

Axiom Cos_plus_pi2 : forall (x:R),
  ((Rtrigo_def.cos (x + ((05 / 10)%R * PI)%R)%R) = (-(Rtrigo_def.sin x))%R).

Axiom Sin_plus_pi2 : forall (x:R),
  ((Rtrigo_def.sin (x + ((05 / 10)%R * PI)%R)%R) = (Rtrigo_def.cos x)).

Axiom Cos_neg : forall (x:R), ((Rtrigo_def.cos (-x)%R) = (Rtrigo_def.cos x)).

Axiom Sin_neg : forall (x:R),
  ((Rtrigo_def.sin (-x)%R) = (-(Rtrigo_def.sin x))%R).

Axiom Cos_sum : forall (x:R) (y:R),
  ((Rtrigo_def.cos (x + y)%R) = (((Rtrigo_def.cos x) * (Rtrigo_def.cos y))%R - ((Rtrigo_def.sin x) * (Rtrigo_def.sin y))%R)%R).

Axiom Sin_sum : forall (x:R) (y:R),
  ((Rtrigo_def.sin (x + y)%R) = (((Rtrigo_def.sin x) * (Rtrigo_def.cos y))%R + ((Rtrigo_def.cos x) * (Rtrigo_def.sin y))%R)%R).

Parameter atan: R -> R.


Axiom Tan_atan : forall (x:R), ((Rtrigo.tan (atan x)) = x).

Parameter single : Type.

Inductive mode  :=
  | NearestTiesToEven : mode 
  | ToZero : mode 
  | Up : mode 
  | Down : mode 
  | NearTiesToAway : mode .

Parameter round: mode -> R -> R.


Parameter round_logic: mode -> R -> single.


Parameter value: single -> R.


Parameter exact: single -> R.


Parameter model: single -> R.


Definition round_error(x:single): R := (Rabs ((value x) - (exact x))%R).

Definition total_error(x:single): R := (Rabs ((value x) - (model x))%R).

Definition no_overflow(m:mode) (x:R): Prop := ((Rabs (round m
  x)) <= (33554430 * 10141204801825835211973625643008)%R)%R.

Axiom Bounded_real_no_overflow : forall (m:mode) (x:R),
  ((Rabs x) <= (33554430 * 10141204801825835211973625643008)%R)%R ->
  (no_overflow m x).

Axiom Round_monotonic : forall (m:mode) (x:R) (y:R), (x <= y)%R -> ((round m
  x) <= (round m y))%R.

Axiom Round_idempotent : forall (m1:mode) (m2:mode) (x:R), ((round m1
  (round m2 x)) = (round m2 x)).

Axiom Round_value : forall (m:mode) (x:single), ((round m
  (value x)) = (value x)).

Axiom Bounded_value : forall (x:single),
  ((Rabs (value x)) <= (33554430 * 10141204801825835211973625643008)%R)%R.

Axiom Exact_rounding_for_integers : forall (m:mode) (i:Z),
  (((-16777216%Z)%Z <= i)%Z /\ (i <= 16777216%Z)%Z) -> ((round m
  (IZR i)) = (IZR i)).

Axiom Round_down_le : forall (x:R), ((round Down x) <= x)%R.

Axiom Round_up_ge : forall (x:R), (x <= (round Up x))%R.

Axiom Round_down_neg : forall (x:R), ((round Down (-x)%R) = (-(round Up
  x))%R).

Axiom Round_up_neg : forall (x:R), ((round Up (-x)%R) = (-(round Down x))%R).

Parameter double : Type.

Parameter round1: mode -> R -> R.


Parameter round_logic1: mode -> R -> double.


Parameter value1: double -> R.


Parameter exact1: double -> R.


Parameter model1: double -> R.


Definition round_error1(x:double): R := (Rabs ((value1 x) - (exact1 x))%R).

Definition total_error1(x:double): R := (Rabs ((value1 x) - (model1 x))%R).

Definition no_overflow1(m:mode) (x:R): Prop := ((Rabs (round1 m
  x)) <= (9007199254740991 * 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848)%R)%R.

Axiom Bounded_real_no_overflow1 : forall (m:mode) (x:R),
  ((Rabs x) <= (9007199254740991 * 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848)%R)%R ->
  (no_overflow1 m x).

Axiom Round_monotonic1 : forall (m:mode) (x:R) (y:R), (x <= y)%R ->
  ((round1 m x) <= (round1 m y))%R.

Axiom Round_idempotent1 : forall (m1:mode) (m2:mode) (x:R), ((round1 m1
  (round1 m2 x)) = (round1 m2 x)).

Axiom Round_value1 : forall (m:mode) (x:double), ((round1 m
  (value1 x)) = (value1 x)).

Axiom Bounded_value1 : forall (x:double),
  ((Rabs (value1 x)) <= (9007199254740991 * 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848)%R)%R.

Axiom Exact_rounding_for_integers1 : forall (m:mode) (i:Z),
  (((-9007199254740992%Z)%Z <= i)%Z /\ (i <= 9007199254740992%Z)%Z) ->
  ((round1 m (IZR i)) = (IZR i)).

Axiom Round_down_le1 : forall (x:R), ((round1 Down x) <= x)%R.

Axiom Round_up_ge1 : forall (x:R), (x <= (round1 Up x))%R.

Axiom Round_down_neg1 : forall (x:R), ((round1 Down (-x)%R) = (-(round1 Up
  x))%R).

Axiom Round_up_neg1 : forall (x:R), ((round1 Up (-x)%R) = (-(round1 Down
  x))%R).

Parameter alloc_table : forall (t:Type), Type.

Parameter pointer : forall (t:Type), Type.

Parameter block : forall (t:Type), Type.

Parameter base_block: forall (t:Type), (pointer t) -> (block t).

Implicit Arguments base_block.

Parameter offset_max: forall (t:Type), (alloc_table t) -> (pointer t) -> Z.

Implicit Arguments offset_max.

Parameter offset_min: forall (t:Type), (alloc_table t) -> (pointer t) -> Z.

Implicit Arguments offset_min.

Definition valid (t:Type)(a:(alloc_table t)) (p:(pointer t)): Prop :=
  ((offset_min a p) <= 0%Z)%Z /\ (0%Z <= (offset_max a p))%Z.
Implicit Arguments valid.

Definition same_block (t:Type)(p:(pointer t)) (q:(pointer t)): Prop :=
  ((base_block p) = (base_block q)).
Implicit Arguments same_block.

Parameter sub_pointer: forall (t:Type), (pointer t) -> (pointer t) -> Z.

Implicit Arguments sub_pointer.

Parameter shift: forall (t:Type), (pointer t) -> Z -> (pointer t).

Implicit Arguments shift.

Parameter null: forall (t:Type), (pointer t).

Set Contextual Implicit.
Implicit Arguments null.
Unset Contextual Implicit.

Parameter pointer_address: forall (t:Type), (pointer t) -> (pointer unit).

Implicit Arguments pointer_address.

Parameter absolute_address: Z -> (pointer unit).


Parameter address: forall (t:Type), (pointer t) -> Z.

Implicit Arguments address.

Axiom address_injective : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), (p = q) <-> ((address p) = (address q)).

Axiom address_shift_lt : forall (t:Type), forall (p:(pointer t)),
  forall (i:Z), forall (j:Z), ((address (shift p i)) <  (address (shift p
  j)))%Z <-> (i <  j)%Z.

Axiom address_shift_le : forall (t:Type), forall (p:(pointer t)),
  forall (i:Z), forall (j:Z), ((address (shift p i)) <= (address (shift p
  j)))%Z <-> (i <= j)%Z.

Axiom shift_zero : forall (t:Type), forall (p:(pointer t)), ((shift p
  0%Z) = p).

Axiom shift_shift : forall (t:Type), forall (p:(pointer t)), forall (i:Z),
  forall (j:Z), ((shift (shift p i) j) = (shift p (i + j)%Z)).

Axiom offset_max_shift : forall (t:Type), forall (a:(alloc_table t)),
  forall (p:(pointer t)), forall (i:Z), ((offset_max a (shift p
  i)) = ((offset_max a p) - i)%Z).

Axiom offset_min_shift : forall (t:Type), forall (a:(alloc_table t)),
  forall (p:(pointer t)), forall (i:Z), ((offset_min a (shift p
  i)) = ((offset_min a p) - i)%Z).

Axiom neq_shift : forall (t:Type), forall (p:(pointer t)), forall (i:Z),
  forall (j:Z), (~ (i = j)) -> ~ ((shift p i) = (shift p j)).

Axiom null_not_valid : forall (t:Type), forall (a:(alloc_table t)),
  ~ (valid a (null:(pointer t))).

Axiom null_pointer : forall (t:Type), forall (a:(alloc_table t)),
  (0%Z <= (offset_min a (null:(pointer t))))%Z /\ ((offset_max a
  (null:(pointer t))) <= (-2%Z)%Z)%Z.

Parameter eq_pointer_bool: forall (t:Type), (pointer t) -> (pointer t) ->
  bool.

Implicit Arguments eq_pointer_bool.

Parameter neq_pointer_bool: forall (t:Type), (pointer t) -> (pointer t) ->
  bool.

Implicit Arguments neq_pointer_bool.

Axiom eq_pointer_bool_def : forall (t:Type), forall (p1:(pointer t)),
  forall (p2:(pointer t)), ((eq_pointer_bool p1 p2) = true) <-> (p1 = p2).

Axiom neq_pointer_bool_def : forall (t:Type), forall (p1:(pointer t)),
  forall (p2:(pointer t)), ((neq_pointer_bool p1 p2) = true) <-> ~ (p1 = p2).

Axiom same_block_shift_right : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), forall (i:Z), (same_block p q) -> (same_block p
  (shift q i)).

Axiom same_block_shift_left : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), forall (i:Z), (same_block q p) ->
  (same_block (shift q i) p).

Axiom sub_pointer_shift : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), (same_block p q) -> (p = (shift q (sub_pointer p
  q))).

Axiom sub_pointer_self : forall (t:Type), forall (p:(pointer t)),
  ((sub_pointer p p) = 0%Z).

Axiom sub_pointer_zero : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), (same_block p q) -> (((sub_pointer p q) = 0%Z) ->
  (p = q)).

Axiom sub_pointer_shift_left : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), forall (i:Z), ((sub_pointer (shift p i)
  q) = ((sub_pointer p q) + i)%Z).

Axiom sub_pointer_shift_right : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), forall (i:Z), ((sub_pointer p (shift q
  i)) = ((sub_pointer p q) - i)%Z).

Parameter memory : forall (t:Type) (v:Type), Type.

Parameter select: forall (t:Type) (v:Type), (memory t v) -> (pointer t) -> v.

Implicit Arguments select.

Parameter store: forall (t:Type) (v:Type), (memory t v) -> (pointer t)
  -> v -> (memory t v).

Implicit Arguments store.

Axiom select_store_eq : forall (t:Type) (v:Type), forall (m:(memory t v)),
  forall (p1:(pointer t)), forall (p2:(pointer t)), forall (a:v),
  (p1 = p2) -> ((select (store m p1 a) p2) = a).

Axiom select_store_neq : forall (t:Type) (v:Type), forall (m:(memory t v)),
  forall (p1:(pointer t)), forall (p2:(pointer t)), forall (a:v),
  (~ (p1 = p2)) -> ((select (store m p1 a) p2) = (select m p2)).

Parameter pset : forall (t:Type), Type.

Parameter pset_empty: forall (t:Type), (pset t).

Set Contextual Implicit.
Implicit Arguments pset_empty.
Unset Contextual Implicit.

Parameter pset_singleton: forall (t:Type), (pointer t) -> (pset t).

Implicit Arguments pset_singleton.

Parameter pset_deref: forall (t:Type) (v:Type), (memory t (pointer v))
  -> (pset t) -> (pset v).

Implicit Arguments pset_deref.

Parameter pset_union: forall (t:Type), (pset t) -> (pset t) -> (pset t).

Implicit Arguments pset_union.

Parameter pset_all: forall (z:Type), (pset z) -> (pset z).

Implicit Arguments pset_all.

Parameter pset_range: forall (t:Type), (pset t) -> Z -> Z -> (pset t).

Implicit Arguments pset_range.

Parameter pset_range_left: forall (z:Type), (pset z) -> Z -> (pset z).

Implicit Arguments pset_range_left.

Parameter pset_range_right: forall (z:Type), (pset z) -> Z -> (pset z).

Implicit Arguments pset_range_right.

Parameter in_pset: forall (t:Type), (pointer t) -> (pset t) -> Prop.

Implicit Arguments in_pset.

Parameter valid_pset: forall (t:Type), (alloc_table t) -> (pset t) -> Prop.

Implicit Arguments valid_pset.

Definition pset_disjoint (t:Type)(ps1:(pset t)) (ps2:(pset t)): Prop :=
  forall (p:(pointer t)), ~ ((in_pset p ps1) /\ (in_pset p ps2)).
Implicit Arguments pset_disjoint.

Definition pset_included (t:Type)(ps1:(pset t)) (ps2:(pset t)): Prop :=
  forall (p:(pointer t)), (in_pset p ps1) -> (in_pset p ps2).
Implicit Arguments pset_included.

Axiom pset_included_self : forall (t:Type), forall (ps:(pset t)),
  (pset_included ps ps).

Axiom pset_included_range : forall (t:Type), forall (ps:(pset t)),
  forall (a:Z), forall (b:Z), forall (c:Z), forall (d:Z), ((c <= a)%Z /\
  (b <= d)%Z) -> (pset_included (pset_range ps a b) (pset_range ps c d)).

Axiom pset_included_range_all : forall (t:Type), forall (ps:(pset t)),
  forall (a:Z), forall (b:Z), (pset_included (pset_range ps a b)
  (pset_all ps)).

Axiom in_pset_empty : forall (t:Type), forall (p:(pointer t)), ~ (in_pset p
  (pset_empty:(pset t))).

Axiom in_pset_singleton : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pointer t)), (in_pset p (pset_singleton q)) <-> (p = q).

Axiom in_pset_deref : forall (v:Type) (t:Type), forall (p:(pointer v)),
  forall (m:(memory t (pointer v))), forall (q:(pset t)), (in_pset p
  (pset_deref m q)) <-> exists r:(pointer t), (in_pset r q) /\ (p = (select m
  r)).

Axiom in_pset_all : forall (t:Type), forall (p:(pointer t)), forall (q:(pset
  t)), (in_pset p (pset_all q)) <-> exists i:Z, exists r:(pointer t),
  (in_pset r q) /\ (p = (shift r i)).

Axiom in_pset_range : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pset t)), forall (a:Z), forall (b:Z), (in_pset p (pset_range q a
  b)) <-> exists i:Z, exists r:(pointer t), (a <= i)%Z /\ ((i <= b)%Z /\
  ((in_pset r q) /\ (p = (shift r i)))).

Axiom in_pset_range_left : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pset t)), forall (b:Z), (in_pset p (pset_range_left q b)) <->
  exists i:Z, exists r:(pointer t), (i <= b)%Z /\ ((in_pset r q) /\
  (p = (shift r i))).

Axiom in_pset_range_right : forall (t:Type), forall (p:(pointer t)),
  forall (q:(pset t)), forall (a:Z), (in_pset p (pset_range_right q a)) <->
  exists i:Z, exists r:(pointer t), (a <= i)%Z /\ ((in_pset r q) /\
  (p = (shift r i))).

Axiom in_pset_union : forall (t:Type), forall (p:(pointer t)),
  forall (s1:(pset t)), forall (s2:(pset t)), (in_pset p (pset_union s1
  s2)) <-> ((in_pset p s1) \/ (in_pset p s2)).

Axiom valid_pset_empty : forall (t:Type), forall (a:(alloc_table t)),
  (valid_pset a (pset_empty:(pset t))).

Axiom valid_pset_singleton : forall (t:Type), forall (a:(alloc_table t)),
  forall (p:(pointer t)), (valid_pset a (pset_singleton p)) <-> (valid a p).

Axiom valid_pset_deref : forall (v:Type) (t:Type), forall (a:(alloc_table
  v)), forall (m:(memory t (pointer v))), forall (q:(pset t)), (valid_pset a
  (pset_deref m q)) <-> forall (r:(pointer t)), forall (p:(pointer v)),
  ((in_pset r q) /\ (p = (select m r))) -> (valid a p).

Axiom valid_pset_range : forall (t:Type), forall (a:(alloc_table t)),
  forall (q:(pset t)), forall (c:Z), forall (d:Z), (valid_pset a
  (pset_range q c d)) <-> forall (i:Z), forall (r:(pointer t)), ((in_pset r
  q) /\ ((c <= i)%Z /\ (i <= d)%Z)) -> (valid a (shift r i)).

Axiom valid_pset_union : forall (t:Type), forall (a:(alloc_table t)),
  forall (s1:(pset t)), forall (s2:(pset t)), (valid_pset a (pset_union s1
  s2)) <-> ((valid_pset a s1) /\ (valid_pset a s2)).

Definition not_assigns (t:Type) (v:Type)(a:(alloc_table t)) (m1:(memory t v))
  (m2:(memory t v)) (l:(pset t)): Prop := forall (p:(pointer t)), ((valid a
  p) /\ ~ (in_pset p l)) -> ((select m2 p) = (select m1 p)).
Implicit Arguments not_assigns.

Axiom not_assigns_refl : forall (t:Type) (v:Type), forall (a:(alloc_table
  t)), forall (m:(memory t v)), forall (l:(pset t)), (not_assigns a m m l).

Axiom not_assigns_trans : forall (t:Type) (v:Type), forall (a:(alloc_table
  t)), forall (m1:(memory t v)), forall (m2:(memory t v)), forall (m3:(memory
  t v)), forall (l:(pset t)), (not_assigns a m1 m2 l) -> ((not_assigns a m2
  m3 l) -> (not_assigns a m1 m3 l)).

Parameter full_separated: forall (t1:Type) (t2:Type), (pointer t1)
  -> (pointer t2) -> Prop.

Implicit Arguments full_separated.

Axiom full_separated_shift1 : forall (z:Type), forall (p:(pointer z)),
  forall (q:(pointer z)), forall (i:Z), (full_separated p q) ->
  (full_separated p (shift q i)).

Axiom full_separated_shift2 : forall (z:Type), forall (p:(pointer z)),
  forall (q:(pointer z)), forall (i:Z), (full_separated p q) ->
  (full_separated (shift q i) p).

Axiom full_separated_shift3 : forall (z:Type), forall (p:(pointer z)),
  forall (q:(pointer z)), forall (i:Z), (full_separated q p) ->
  (full_separated (shift q i) p).

Axiom full_separated_shift4 : forall (z:Type), forall (p:(pointer z)),
  forall (q:(pointer z)), forall (i:Z), (full_separated q p) ->
  (full_separated p (shift q i)).

Parameter tag_table : forall (t:Type), Type.

Parameter tag_id : forall (t:Type), Type.

Parameter int_of_tag: forall (t:Type), (tag_id t) -> Z.

Implicit Arguments int_of_tag.

Parameter typeof: forall (t:Type), (tag_table t) -> (pointer t) -> (tag_id
  t).

Implicit Arguments typeof.

Parameter parenttag: forall (t:Type), (tag_id t) -> (tag_id t) -> Prop.

Implicit Arguments parenttag.

Parameter subtag: forall (t:Type), (tag_id t) -> (tag_id t) -> Prop.

Implicit Arguments subtag.

Parameter subtag_bool: forall (t:Type), (tag_id t) -> (tag_id t) -> bool.

Implicit Arguments subtag_bool.

Axiom subtag_bool_def : forall (t:Type), forall (t1:(tag_id t)),
  forall (t2:(tag_id t)), ((subtag_bool t1 t2) = true) <-> (subtag t1 t2).

Axiom subtag_refl : forall (t:Type), forall (t1:(tag_id t)), (subtag t1 t1).

Axiom subtag_parent : forall (t:Type), forall (t1:(tag_id t)),
  forall (t2:(tag_id t)), forall (t3:(tag_id t)), (subtag t1 t2) ->
  ((parenttag t2 t3) -> (subtag t1 t3)).

Definition instanceof (t:Type)(a:(tag_table t)) (p:(pointer t)) (t1:(tag_id
  t)): Prop := (subtag (typeof a p) t1).
Implicit Arguments instanceof.

Parameter downcast: forall (t:Type), (tag_table t) -> (pointer t) -> (tag_id
  t) -> (pointer t).

Implicit Arguments downcast.

Axiom downcast_instanceof : forall (t:Type), forall (a:(tag_table t)),
  forall (p:(pointer t)), forall (s:(tag_id t)), (instanceof a p s) ->
  ((downcast a p s) = p).

Parameter bottom_tag: forall (a:Type), (tag_id a).

Set Contextual Implicit.
Implicit Arguments bottom_tag.
Unset Contextual Implicit.

Axiom bottom_tag_axiom : forall (t:Type), forall (t1:(tag_id t)), (subtag t1
  (bottom_tag:(tag_id t))).

Axiom root_subtag : forall (t:Type), forall (a:(tag_id t)), forall (b:(tag_id
  t)), forall (c:(tag_id t)), (parenttag a (bottom_tag:(tag_id t))) ->
  ((parenttag b (bottom_tag:(tag_id t))) -> ((~ (a = b)) -> ((subtag c a) ->
  ~ (subtag c b)))).

Definition fully_packed (a:Type)(tag_table1:(tag_table a)) (usmutable:(memory
  a (tag_id a))) (this:(pointer a)): Prop := ((select usmutable
  this) = (typeof tag_table1 this)).
Implicit Arguments fully_packed.

Parameter bw_compl: Z -> Z.


Parameter bw_and: Z -> Z -> Z.


Axiom bw_and_not_null : forall (a:Z), forall (b:Z), (~ ((bw_and a
  b) = 0%Z)) -> ((~ (a = 0%Z)) /\ ~ (b = 0%Z)).

Parameter bw_xor: Z -> Z -> Z.


Parameter bw_or: Z -> Z -> Z.


Parameter lsl: Z -> Z -> Z.


Axiom lsl_left_positive_returns_positive : forall (a:Z), forall (b:Z),
  ((0%Z <= a)%Z /\ (0%Z <= b)%Z) -> (0%Z <= (lsl a b))%Z.

Axiom lsl_left_positive_monotone : forall (a1:Z), forall (a2:Z),
  forall (b:Z), ((0%Z <= a1)%Z /\ ((a1 <= a2)%Z /\ (0%Z <= b)%Z)) -> ((lsl a1
  b) <= (lsl a2 b))%Z.

Parameter lsr: Z -> Z -> Z.


Axiom lsr_left_positive_returns_positive : forall (a:Z), forall (b:Z),
  ((0%Z <= a)%Z /\ (0%Z <= b)%Z) -> (0%Z <= (lsr a b))%Z.

Axiom lsr_left_positive_decreases : forall (a:Z), forall (b:Z),
  ((0%Z <= a)%Z /\ (0%Z <= b)%Z) -> ((lsr a b) <= a)%Z.

Parameter asr: Z -> Z -> Z.


Axiom asr_positive_on_positive : forall (a:Z), forall (b:Z), ((0%Z <= a)%Z /\
  (0%Z <= b)%Z) -> (0%Z <= (asr a b))%Z.

Axiom asr_decreases_on_positive : forall (a:Z), forall (b:Z),
  ((0%Z <= a)%Z /\ (0%Z <= b)%Z) -> ((asr a b) <= a)%Z.

Axiom asr_lsr_same_on_positive : forall (a:Z), forall (b:Z), ((0%Z <= a)%Z /\
  (0%Z <= b)%Z) -> ((asr a b) = (lsr a b)).

Axiom lsl_of_lsr_decreases_on_positive : forall (a:Z), forall (b:Z),
  ((0%Z <= a)%Z /\ (0%Z <= b)%Z) -> ((lsl (lsr a b) b) <= a)%Z.

Axiom lsr_of_lsl_identity_on_positive : forall (a:Z), forall (b:Z),
  ((0%Z <= a)%Z /\ (0%Z <= b)%Z) -> ((lsr (lsl a b) b) = a).

Parameter alloc_extends: forall (t:Type), (alloc_table t) -> (alloc_table
  t) -> Prop.

Implicit Arguments alloc_extends.

Definition alloc_fresh (t:Type)(a:(alloc_table t)) (p:(pointer t))
  (n:Z): Prop := forall (i:Z), ((0%Z <= i)%Z /\ (i <  n)%Z) -> ~ (valid a
  (shift p i)).
Implicit Arguments alloc_fresh.

Axiom alloc_extends_offset_min : forall (t:Type), forall (a1:(alloc_table
  t)), forall (a2:(alloc_table t)), (alloc_extends a1 a2) ->
  forall (p:(pointer t)), (valid a1 p) -> ((offset_min a1 p) = (offset_min a2
  p)).

Axiom alloc_extends_offset_max : forall (t:Type), forall (a1:(alloc_table
  t)), forall (a2:(alloc_table t)), (alloc_extends a1 a2) ->
  forall (p:(pointer t)), (valid a1 p) -> ((offset_max a1 p) = (offset_max a2
  p)).

Axiom alloc_extends_not_assigns_empty : forall (t:Type) (v:Type),
  forall (a1:(alloc_table t)), forall (a2:(alloc_table t)),
  forall (m1:(memory t v)), forall (m2:(memory t v)), forall (l:(pset t)),
  forall (p:(pointer t)), forall (n:Z), ((alloc_extends a1 a2) /\
  ((alloc_fresh a1 p n) /\ ((not_assigns a2 m1 m2 l) /\ (pset_included l
  (pset_all (pset_singleton p)))))) -> (not_assigns a1 m1 m2
  (pset_empty:(pset t))).

Parameter alloc_extends_except: forall (t:Type), (alloc_table t)
  -> (alloc_table t) -> (pset t) -> Prop.

Implicit Arguments alloc_extends_except.

Axiom alloc_extends_except_offset_min : forall (t:Type),
  forall (a1:(alloc_table t)), forall (a2:(alloc_table t)), forall (l:(pset
  t)), (alloc_extends_except a1 a2 l) -> forall (p:(pointer t)), ((valid a1
  p) /\ ~ (in_pset p l)) -> ((offset_min a1 p) = (offset_min a2 p)).

Axiom alloc_extends_except_offset_max : forall (t:Type),
  forall (a1:(alloc_table t)), forall (a2:(alloc_table t)), forall (l:(pset
  t)), (alloc_extends_except a1 a2 l) -> forall (p:(pointer t)), ((valid a1
  p) /\ ~ (in_pset p l)) -> ((offset_max a1 p) = (offset_max a2 p)).

Parameter mybag : forall (a:Type), Type.

Parameter in_mybag: forall (a:Type), a -> (mybag a) -> Prop.

Implicit Arguments in_mybag.

Parameter disj_mybag: forall (a:Type), (mybag a) -> (mybag a) -> Prop.

Implicit Arguments disj_mybag.

Axiom disj_sym : forall (a:Type), forall (s1:(mybag a)) (s2:(mybag a)),
  (disj_mybag s1 s2) -> (disj_mybag s2 s1).

Parameter sub_mybag: forall (a:Type), (mybag a) -> (mybag a) -> Prop.

Implicit Arguments sub_mybag.

Axiom sub_refl : forall (a:Type), forall (sa:(mybag (pointer a))),
  (sub_mybag sa sa).

Axiom sub_disj : forall (a:Type), forall (s1:(mybag a)) (s2:(mybag a))
  (s3:(mybag a)), (disj_mybag s1 s2) -> ((sub_mybag s2 s3) -> (disj_mybag s1
  s3)).

Axiom sub_in : forall (a:Type), forall (s1:(mybag a)) (s2:(mybag a)),
  forall (p:a), (~ (in_mybag p s2)) -> ((sub_mybag s1 s2) -> ~ (in_mybag p
  s1)).

Parameter frame_between: forall (a:Type) (b:Type), (mybag (pointer a))
  -> (memory a b) -> (memory a b) -> Prop.

Implicit Arguments frame_between.

Axiom frame_between_refl : forall (a:Type) (b:Type), forall (sa:(mybag
  (pointer a))), forall (m:(memory a b)), (frame_between sa m m).

Axiom frame_between_gen : forall (a:Type) (b:Type), forall (sa:(mybag
  (pointer a))), forall (m1:(memory a b)) (m2:(memory a b)),
  forall (p:(pointer a)), forall (v:b), (frame_between sa m1 m2) ->
  ((in_mybag p sa) -> (frame_between sa (store m1 p v) m2)).

Axiom frame_between_gen2 : forall (a:Type) (b:Type), forall (sa:(mybag
  (pointer a))), forall (m1:(memory a b)) (m2:(memory a b)) (m3:(memory a
  b)), (frame_between sa m1 m2) -> ((frame_between sa m2 m3) ->
  (frame_between sa m1 m3)).

Axiom frame_between_gen_sub1 : forall (a:Type) (b:Type), forall (s12:(mybag
  (pointer a))) (s23:(mybag (pointer a))) (s13:(mybag (pointer a))),
  forall (m1:(memory a b)) (m2:(memory a b)) (m3:(memory a b)),
  (sub_mybag s12 s13) -> ((frame_between s12 m1 m2) -> ((frame_between s23 m2
  m3) -> (frame_between s13 m1 m3))).

Axiom frame_between_gen_sub2 : forall (a:Type) (b:Type), forall (s12:(mybag
  (pointer a))) (s23:(mybag (pointer a))) (s13:(mybag (pointer a))),
  forall (m1:(memory a b)) (m2:(memory a b)) (m3:(memory a b)),
  (frame_between s12 m1 m2) -> ((sub_mybag s23 s13) -> ((frame_between s23 m2
  m3) -> (frame_between s13 m1 m3))).

Axiom frame_between_pointer : forall (a:Type) (b:Type), forall (sa:(mybag
  (pointer a))), forall (m1:(memory a b)) (m2:(memory a b)),
  forall (p:(pointer a)), (frame_between sa m1 m2) -> ((~ (in_mybag p sa)) ->
  ((select m1 p) = (select m2 p))).

Axiom frame_between_sub : forall (a:Type) (b:Type), forall (sa:(mybag
  (pointer a))), forall (sb:(mybag (pointer a))), forall (m1:(memory a b))
  (m2:(memory a b)), (frame_between sa m1 m2) -> ((sub_mybag sa sb) ->
  (frame_between sb m1 m2)).

Parameter char_P : Type.

Parameter int8 : Type.

Parameter padding : Type.

Parameter void_P : Type.

Parameter char_P_tag: (tag_id char_P).


Axiom char_P_int : ((int_of_tag char_P_tag) = 1%Z).

Parameter char_P_of_pointer_address: (pointer unit) -> (pointer char_P).


Axiom char_P_of_pointer_address_of_pointer_addr : forall (p:(pointer
  char_P)), (p = (char_P_of_pointer_address (pointer_address p))).

Axiom char_P_parenttag_bottom : (parenttag char_P_tag (bottom_tag:(tag_id
  char_P))).

Axiom char_P_tags : forall (x:(pointer char_P)),
  forall (char_P_tag_table:(tag_table char_P)), (instanceof char_P_tag_table
  x char_P_tag).

Parameter integer_of_int8: int8 -> Z.


Definition eq_int8(x:int8) (y:int8): Prop :=
  ((integer_of_int8 x) = (integer_of_int8 y)).

Parameter int8_of_integer: Z -> int8.


Axiom int8_coerce : forall (x:Z), (((-128%Z)%Z <= x)%Z /\ (x <= 127%Z)%Z) ->
  ((integer_of_int8 (int8_of_integer x)) = x).

Axiom int8_extensionality : forall (x:int8), forall (y:int8),
  ((integer_of_int8 x) = (integer_of_int8 y)) -> (x = y).

Axiom int8_range : forall (x:int8), ((-128%Z)%Z <= (integer_of_int8 x))%Z /\
  ((integer_of_int8 x) <= 127%Z)%Z.

Definition left_valid_struct_char_P(p:(pointer char_P)) (a:Z)
  (char_P_alloc_table:(alloc_table char_P)): Prop :=
  ((offset_min char_P_alloc_table p) <= a)%Z.

Definition left_valid_struct_void_P(p:(pointer void_P)) (a:Z)
  (void_P_alloc_table:(alloc_table void_P)): Prop :=
  ((offset_min void_P_alloc_table p) <= a)%Z.

Axiom pointer_addr_of_char_P_of_pointer_address : forall (p:(pointer unit)),
  (p = (pointer_address (char_P_of_pointer_address p))).

Parameter void_P_of_pointer_address: (pointer unit) -> (pointer void_P).


Axiom pointer_addr_of_void_P_of_pointer_address : forall (p:(pointer unit)),
  (p = (pointer_address (void_P_of_pointer_address p))).

Definition right_valid_struct_char_P(p:(pointer char_P)) (b:Z)
  (char_P_alloc_table:(alloc_table char_P)): Prop :=
  (b <= (offset_max char_P_alloc_table p))%Z.

Definition right_valid_struct_void_P(p:(pointer void_P)) (b:Z)
  (void_P_alloc_table:(alloc_table void_P)): Prop :=
  (b <= (offset_max void_P_alloc_table p))%Z.

Definition strict_valid_root_char_P(p:(pointer char_P)) (a:Z) (b:Z)
  (char_P_alloc_table:(alloc_table char_P)): Prop :=
  ((offset_min char_P_alloc_table p) = a) /\ ((offset_max char_P_alloc_table
  p) = b).

Definition strict_valid_root_void_P(p:(pointer void_P)) (a:Z) (b:Z)
  (void_P_alloc_table:(alloc_table void_P)): Prop :=
  ((offset_min void_P_alloc_table p) = a) /\ ((offset_max void_P_alloc_table
  p) = b).

Definition strict_valid_struct_char_P(p:(pointer char_P)) (a:Z) (b:Z)
  (char_P_alloc_table:(alloc_table char_P)): Prop :=
  ((offset_min char_P_alloc_table p) = a) /\ ((offset_max char_P_alloc_table
  p) = b).

Definition strict_valid_struct_void_P(p:(pointer void_P)) (a:Z) (b:Z)
  (void_P_alloc_table:(alloc_table void_P)): Prop :=
  ((offset_min void_P_alloc_table p) = a) /\ ((offset_max void_P_alloc_table
  p) = b).

Definition valid_bitvector_struct_char_P(p:(pointer unit)) (a:Z) (b:Z)
  (bitvector_alloc_table:(alloc_table unit)): Prop :=
  ((offset_min bitvector_alloc_table p) = a) /\
  ((offset_max bitvector_alloc_table p) = b).

Definition valid_bitvector_struct_void_P(p:(pointer unit)) (a:Z) (b:Z)
  (bitvector_alloc_table:(alloc_table unit)): Prop :=
  ((offset_min bitvector_alloc_table p) = a) /\
  ((offset_max bitvector_alloc_table p) = b).

Definition valid_root_char_P(p:(pointer char_P)) (a:Z) (b:Z)
  (char_P_alloc_table:(alloc_table char_P)): Prop :=
  ((offset_min char_P_alloc_table p) <= a)%Z /\
  (b <= (offset_max char_P_alloc_table p))%Z.

Definition valid_root_void_P(p:(pointer void_P)) (a:Z) (b:Z)
  (void_P_alloc_table:(alloc_table void_P)): Prop :=
  ((offset_min void_P_alloc_table p) <= a)%Z /\
  (b <= (offset_max void_P_alloc_table p))%Z.

Definition valid_struct_char_P(p:(pointer char_P)) (a:Z) (b:Z)
  (char_P_alloc_table:(alloc_table char_P)): Prop :=
  ((offset_min char_P_alloc_table p) <= a)%Z /\
  (b <= (offset_max char_P_alloc_table p))%Z.

Definition valid_struct_void_P(p:(pointer void_P)) (a:Z) (b:Z)
  (void_P_alloc_table:(alloc_table void_P)): Prop :=
  ((offset_min void_P_alloc_table p) <= a)%Z /\
  (b <= (offset_max void_P_alloc_table p))%Z.

Parameter void_P_tag: (tag_id void_P).


Axiom void_P_int : ((int_of_tag void_P_tag) = 1%Z).

Axiom void_P_of_pointer_address_of_pointer_addr : forall (p:(pointer
  void_P)), (p = (void_P_of_pointer_address (pointer_address p))).

Axiom void_P_parenttag_bottom : (parenttag void_P_tag (bottom_tag:(tag_id
  void_P))).

Axiom void_P_tags : forall (x:(pointer void_P)),
  forall (void_P_tag_table:(tag_table void_P)), (instanceof void_P_tag_table
  x void_P_tag).

Axiom method_error : forall (x_3:R), ((Rabs x_3) <= (1 / 32)%R)%R ->
  ((Rabs ((1%R - ((x_3 * x_3)%R * (05 / 10)%R)%R)%R - (Rtrigo_def.cos x_3))%R) <= (1 / 16777216)%R)%R.

Inductive ref (a:Type) :=
  | mk_ref : a -> ref a.
Implicit Arguments mk_ref.

Definition contents (a:Type)(u:(ref a)): a :=
  match u with
  | mk_ref contents1 => contents1
  end.
Implicit Arguments contents.

Definition sub_single_post(m:mode) (x:single) (y:single)
  (res:single): Prop := ((value res) = (round m
  ((value x) - (value y))%R)) /\
  (((exact res) = ((exact x) - (exact y))%R) /\
  ((model res) = ((model x) - (model y))%R)).

Definition mul_single_post(m:mode) (x:single) (y:single)
  (res:single): Prop := ((value res) = (round m
  ((value x) * (value y))%R)) /\
  (((exact res) = ((exact x) * (exact y))%R) /\
  ((model res) = ((model x) * (model y))%R)).

Parameter char_P_alloc_table: (ref (alloc_table char_P)).


Parameter char_P_tag_table: (ref (tag_table char_P)).


Parameter void_P_alloc_table: (ref (alloc_table void_P)).


Parameter void_P_tag_table: (ref (tag_table void_P)).


(* YOU MAY EDIT THE CONTEXT BELOW *)
Require Import Interval_tactic.
(* DO NOT EDIT BELOW *)

Theorem WP_parameter_my_cos4_ensures_default : forall (x_2:single),
  ((Rabs (value x_2)) <= (007 / 100)%R)%R ->
  ((Rabs ((1%R - (((value x_2) * (value x_2))%R * (05 / 10)%R)%R)%R - (Rtrigo_def.cos (value x_2)))%R) <= (15 / 16777216)%R)%R.
(* YOU MAY EDIT THE PROOF BELOW *)
intros x H.
assert (Rabs (value x) <= 1 / 16)%R.
  apply Rle_trans with (1:=H).
  admit.
interval with (i_bisect_diff (value x)).
Qed.
(* DO NOT EDIT BELOW *)


