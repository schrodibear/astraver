(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import ZArith.
Require Import Rbase.
Require int.Int.
Definition implb(x:bool) (y:bool): bool := match (x,
  y) with
  | (true, false) => false
  | (_, _) => true
  end.

Definition zwf_zero(a:Z) (b:Z): Prop := (0%Z <= b)%Z /\ (a <  b)%Z.

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
  (s3:(mybag a)), (disj_mybag s1 s3) -> ((sub_mybag s2 s3) -> (disj_mybag s1
  s2)).

Axiom sub_in : forall (a:Type), forall (s1:(mybag a)) (s2:(mybag a)),
  forall (p:a), (~ (in_mybag p s2)) -> ((sub_mybag s1 s2) -> ~ (in_mybag p
  s1)).

Axiom sub_sub : forall (a:Type), forall (s1:(mybag a)) (s2:(mybag a))
  (s3:(mybag a)), (sub_mybag s1 s2) -> ((sub_mybag s2 s3) -> (sub_mybag s1
  s3)).

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

Parameter charP : Type.

Parameter int32 : Type.

Parameter int8 : Type.

Parameter intP : Type.

Parameter padding : Type.

Parameter voidP : Type.

Parameter charP_tag: (tag_id charP).


Axiom charP_int : ((int_of_tag charP_tag) = 1%Z).

Parameter charP_of_pointer_address: (pointer unit) -> (pointer charP).


Axiom charP_of_pointer_address_of_pointer_addr : forall (p:(pointer charP)),
  (p = (charP_of_pointer_address (pointer_address p))).

Axiom charP_parenttag_bottom : (parenttag charP_tag (bottom_tag:(tag_id
  charP))).

Axiom charP_tags : forall (x:(pointer charP)),
  forall (charP_tag_table:(tag_table charP)), (instanceof charP_tag_table x
  charP_tag).

Parameter integer_of_int32: int32 -> Z.


Definition eq_int32(x:int32) (y:int32): Prop :=
  ((integer_of_int32 x) = (integer_of_int32 y)).

Parameter integer_of_int8: int8 -> Z.


Definition eq_int8(x:int8) (y:int8): Prop :=
  ((integer_of_int8 x) = (integer_of_int8 y)).

Parameter int32_of_integer: Z -> int32.


Axiom int32_coerce : forall (x:Z), (((-2147483648%Z)%Z <= x)%Z /\
  (x <= 2147483647%Z)%Z) -> ((integer_of_int32 (int32_of_integer x)) = x).

Axiom int32_extensionality : forall (x:int32), forall (y:int32),
  ((integer_of_int32 x) = (integer_of_int32 y)) -> (x = y).

Axiom int32_range : forall (x:int32),
  ((-2147483648%Z)%Z <= (integer_of_int32 x))%Z /\
  ((integer_of_int32 x) <= 2147483647%Z)%Z.

Parameter int8_of_integer: Z -> int8.


Axiom int8_coerce : forall (x:Z), (((-128%Z)%Z <= x)%Z /\ (x <= 127%Z)%Z) ->
  ((integer_of_int8 (int8_of_integer x)) = x).

Axiom int8_extensionality : forall (x:int8), forall (y:int8),
  ((integer_of_int8 x) = (integer_of_int8 y)) -> (x = y).

Axiom int8_range : forall (x:int8), ((-128%Z)%Z <= (integer_of_int8 x))%Z /\
  ((integer_of_int8 x) <= 127%Z)%Z.

Parameter intP_tag: (tag_id intP).


Axiom intP_int : ((int_of_tag intP_tag) = 1%Z).

Parameter intP_of_pointer_address: (pointer unit) -> (pointer intP).


Axiom intP_of_pointer_address_of_pointer_addr : forall (p:(pointer intP)),
  (p = (intP_of_pointer_address (pointer_address p))).

Axiom intP_parenttag_bottom : (parenttag intP_tag (bottom_tag:(tag_id
  intP))).

Axiom intP_tags : forall (x:(pointer intP)),
  forall (intP_tag_table:(tag_table intP)), (instanceof intP_tag_table x
  intP_tag).

Definition left_valid_struct_charP(p:(pointer charP)) (a:Z)
  (charP_alloc_table:(alloc_table charP)): Prop :=
  ((offset_min charP_alloc_table p) <= a)%Z.

Definition left_valid_struct_intP(p:(pointer intP)) (a:Z)
  (intP_alloc_table:(alloc_table intP)): Prop :=
  ((offset_min intP_alloc_table p) <= a)%Z.

Definition left_valid_struct_voidP(p:(pointer voidP)) (a:Z)
  (voidP_alloc_table:(alloc_table voidP)): Prop :=
  ((offset_min voidP_alloc_table p) <= a)%Z.

Parameter num_of_pos: Z -> Z -> (pointer intP) -> (memory intP int32) -> Z.


Axiom pointer_addr_of_charP_of_pointer_address : forall (p:(pointer unit)),
  (p = (pointer_address (charP_of_pointer_address p))).

Axiom pointer_addr_of_intP_of_pointer_address : forall (p:(pointer unit)),
  (p = (pointer_address (intP_of_pointer_address p))).

Parameter voidP_of_pointer_address: (pointer unit) -> (pointer voidP).


Axiom pointer_addr_of_voidP_of_pointer_address : forall (p:(pointer unit)),
  (p = (pointer_address (voidP_of_pointer_address p))).

Definition right_valid_struct_charP(p:(pointer charP)) (b:Z)
  (charP_alloc_table:(alloc_table charP)): Prop :=
  (b <= (offset_max charP_alloc_table p))%Z.

Definition right_valid_struct_intP(p:(pointer intP)) (b:Z)
  (intP_alloc_table:(alloc_table intP)): Prop :=
  (b <= (offset_max intP_alloc_table p))%Z.

Definition right_valid_struct_voidP(p:(pointer voidP)) (b:Z)
  (voidP_alloc_table:(alloc_table voidP)): Prop :=
  (b <= (offset_max voidP_alloc_table p))%Z.

Definition strict_valid_root_charP(p:(pointer charP)) (a:Z) (b:Z)
  (charP_alloc_table:(alloc_table charP)): Prop :=
  ((offset_min charP_alloc_table p) = a) /\ ((offset_max charP_alloc_table
  p) = b).

Definition strict_valid_root_intP(p:(pointer intP)) (a:Z) (b:Z)
  (intP_alloc_table:(alloc_table intP)): Prop :=
  ((offset_min intP_alloc_table p) = a) /\ ((offset_max intP_alloc_table
  p) = b).

Definition strict_valid_root_voidP(p:(pointer voidP)) (a:Z) (b:Z)
  (voidP_alloc_table:(alloc_table voidP)): Prop :=
  ((offset_min voidP_alloc_table p) = a) /\ ((offset_max voidP_alloc_table
  p) = b).

Definition strict_valid_struct_charP(p:(pointer charP)) (a:Z) (b:Z)
  (charP_alloc_table:(alloc_table charP)): Prop :=
  ((offset_min charP_alloc_table p) = a) /\ ((offset_max charP_alloc_table
  p) = b).

Definition strict_valid_struct_intP(p:(pointer intP)) (a:Z) (b:Z)
  (intP_alloc_table:(alloc_table intP)): Prop :=
  ((offset_min intP_alloc_table p) = a) /\ ((offset_max intP_alloc_table
  p) = b).

Definition strict_valid_struct_voidP(p:(pointer voidP)) (a:Z) (b:Z)
  (voidP_alloc_table:(alloc_table voidP)): Prop :=
  ((offset_min voidP_alloc_table p) = a) /\ ((offset_max voidP_alloc_table
  p) = b).

Definition valid_root_charP(p:(pointer charP)) (a:Z) (b:Z)
  (charP_alloc_table:(alloc_table charP)): Prop :=
  ((offset_min charP_alloc_table p) <= a)%Z /\
  (b <= (offset_max charP_alloc_table p))%Z.

Definition valid_root_intP(p:(pointer intP)) (a:Z) (b:Z)
  (intP_alloc_table:(alloc_table intP)): Prop :=
  ((offset_min intP_alloc_table p) <= a)%Z /\
  (b <= (offset_max intP_alloc_table p))%Z.

Definition valid_root_voidP(p:(pointer voidP)) (a:Z) (b:Z)
  (voidP_alloc_table:(alloc_table voidP)): Prop :=
  ((offset_min voidP_alloc_table p) <= a)%Z /\
  (b <= (offset_max voidP_alloc_table p))%Z.

Definition valid_struct_charP(p:(pointer charP)) (a:Z) (b:Z)
  (charP_alloc_table:(alloc_table charP)): Prop :=
  ((offset_min charP_alloc_table p) <= a)%Z /\
  (b <= (offset_max charP_alloc_table p))%Z.

Definition valid_struct_intP(p:(pointer intP)) (a:Z) (b:Z)
  (intP_alloc_table:(alloc_table intP)): Prop :=
  ((offset_min intP_alloc_table p) <= a)%Z /\
  (b <= (offset_max intP_alloc_table p))%Z.

Definition valid_struct_voidP(p:(pointer voidP)) (a:Z) (b:Z)
  (voidP_alloc_table:(alloc_table voidP)): Prop :=
  ((offset_min voidP_alloc_table p) <= a)%Z /\
  (b <= (offset_max voidP_alloc_table p))%Z.

Parameter voidP_tag: (tag_id voidP).


Axiom voidP_int : ((int_of_tag voidP_tag) = 1%Z).

Axiom voidP_of_pointer_address_of_pointer_addr : forall (p:(pointer voidP)),
  (p = (voidP_of_pointer_address (pointer_address p))).

Axiom voidP_parenttag_bottom : (parenttag voidP_tag (bottom_tag:(tag_id
  voidP))).

Axiom voidP_tags : forall (x:(pointer voidP)),
  forall (voidP_tag_table:(tag_table voidP)), (instanceof voidP_tag_table x
  voidP_tag).

Axiom num_of_pos_empty : forall (intP_intM_t_1_at_L:(memory intP int32)),
  forall (i_0:Z), forall (j_0:Z), forall (t_0_0:(pointer intP)),
  (j_0 <= i_0)%Z -> ((num_of_pos i_0 j_0 t_0_0 intP_intM_t_1_at_L) = 0%Z).

Axiom num_of_pos_true_case : forall (intP_intM_t_1_at_L:(memory intP int32)),
  forall (i_1:Z), forall (j_1:Z), forall (t_1:(pointer intP)),
  ((i_1 <  j_1)%Z /\ (0%Z <  (integer_of_int32 (select intP_intM_t_1_at_L
  (shift t_1 (j_1 - 1%Z)%Z))))%Z) -> ((num_of_pos i_1 j_1 t_1
  intP_intM_t_1_at_L) = ((num_of_pos i_1 (j_1 - 1%Z)%Z t_1
  intP_intM_t_1_at_L) + 1%Z)%Z).

Axiom num_of_pos_false_case : forall (intP_intM_t_1_at_L:(memory intP
  int32)), forall (i_2:Z), forall (j_2:Z), forall (t_2:(pointer intP)),
  ((i_2 <  j_2)%Z /\ ~ (0%Z <  (integer_of_int32 (select intP_intM_t_1_at_L
  (shift t_2 (j_2 - 1%Z)%Z))))%Z) -> ((num_of_pos i_2 j_2 t_2
  intP_intM_t_1_at_L) = (num_of_pos i_2 (j_2 - 1%Z)%Z t_2
  intP_intM_t_1_at_L)).

Axiom num_of_pos_non_negative : forall (intP_intM_t_3_8_at_L:(memory intP
  int32)), forall (i_3:Z), forall (j_3:Z), forall (t_3:(pointer intP)),
  (0%Z <= (num_of_pos i_3 j_3 t_3 intP_intM_t_3_8_at_L))%Z.

Axiom num_of_pos_additive : forall (intP_intM_t_4_9_at_L:(memory intP
  int32)), forall (i_4:Z), forall (j_4:Z), forall (k_1:Z),
  forall (t_4:(pointer intP)), ((i_4 <= j_4)%Z /\ (j_4 <= k_1)%Z) ->
  ((num_of_pos i_4 k_1 t_4 intP_intM_t_4_9_at_L) = ((num_of_pos i_4 j_4 t_4
  intP_intM_t_4_9_at_L) + (num_of_pos j_4 k_1 t_4 intP_intM_t_4_9_at_L))%Z).

Axiom num_of_pos_increasing : forall (intP_intM_t_5_10_at_L:(memory intP
  int32)), forall (i_5:Z), forall (j_5:Z), forall (k_2:Z),
  forall (t_5:(pointer intP)), (j_5 <= k_2)%Z -> ((num_of_pos i_5 j_5 t_5
  intP_intM_t_5_10_at_L) <= (num_of_pos i_5 k_2 t_5
  intP_intM_t_5_10_at_L))%Z.

(* YOU MAY EDIT THE CONTEXT BELOW *)
Open Scope Z_scope.
(* DO NOT EDIT BELOW *)

Theorem num_of_pos_strictly_increasing : forall (intP_intM_t_6_11_at_L:(memory
  intP int32)), forall (i_6:Z), forall (n:Z), forall (t_6:(pointer intP)),
  ((0%Z <= i_6)%Z /\ ((i_6 <  n)%Z /\
  (0%Z <  (integer_of_int32 (select intP_intM_t_6_11_at_L (shift t_6
  i_6))))%Z)) -> ((num_of_pos 0%Z i_6 t_6
  intP_intM_t_6_11_at_L) <  (num_of_pos 0%Z n t_6 intP_intM_t_6_11_at_L))%Z.
(* YOU MAY EDIT THE PROOF BELOW *)
intros tMem i n t (Hi, (Hin, H)).
rewrite num_of_pos_additive with (k_1:=n) (j_4:= i); auto with zarith.
rewrite num_of_pos_additive with (k_1:=n) (j_4:= i+1); auto with zarith.
rewrite num_of_pos_true_case with (i_1:=i); 
  replace ((i + 1) - 1) with i by omega; 
  intuition.
generalize (num_of_pos_non_negative tMem 0 i t); intro.
generalize (num_of_pos_non_negative tMem i i t); intro.
generalize (num_of_pos_non_negative tMem (i+1) n t); intro.
omega.
Qed.
(* DO NOT EDIT BELOW *)


