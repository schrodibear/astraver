(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require bool.Bool.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.
Require map.Map.

(* Why3 assumption *)
Definition zwf_zero (a:Z) (b:Z): Prop := (0%Z <= a)%Z /\ (a < b)%Z.

Axiom alloc_table : forall (t:Type), Type.
Parameter alloc_table_WhyType : forall (t:Type) {t_WT:WhyType t},
  WhyType (alloc_table t).
Existing Instance alloc_table_WhyType.

Axiom pointer : forall (t:Type), Type.
Parameter pointer_WhyType : forall (t:Type) {t_WT:WhyType t},
  WhyType (pointer t).
Existing Instance pointer_WhyType.

Parameter offset_max: forall {t:Type} {t_WT:WhyType t}, (alloc_table t) ->
  (pointer t) -> Z.

Parameter offset_min: forall {t:Type} {t_WT:WhyType t}, (alloc_table t) ->
  (pointer t) -> Z.

(* Why3 assumption *)
Definition valid {t:Type} {t_WT:WhyType t} (a:(alloc_table t)) (p:(pointer
  t)): Prop := ((offset_min a p) <= 0%Z)%Z /\ (0%Z <= (offset_max a p))%Z.

Parameter same_block: forall {t:Type} {t_WT:WhyType t}, (pointer t) ->
  (pointer t) -> Prop.

Parameter sub_pointer: forall {t:Type} {t_WT:WhyType t}, (pointer t) ->
  (pointer t) -> Z.

Parameter shift: forall {t:Type} {t_WT:WhyType t}, (pointer t) -> Z ->
  (pointer t).

Parameter null: forall {t:Type} {t_WT:WhyType t}, (pointer t).

Axiom null_pointer : forall {t:Type} {t_WT:WhyType t}, forall (a:(alloc_table
  t)), ((offset_max a (null : (pointer t))) = (-2%Z)%Z) /\
  (((-2%Z)%Z < (offset_min a (null : (pointer t))))%Z /\ ((offset_min a
  (null : (pointer t))) = 0%Z)).

Axiom shift_zero : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer t)),
  ((shift p 0%Z) = p).

Axiom shift_shift : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer t)),
  forall (i:Z), forall (j:Z), ((shift (shift p i) j) = (shift p (i + j)%Z)).

Axiom offset_max_shift : forall {t:Type} {t_WT:WhyType t},
  forall (a:(alloc_table t)), forall (p:(pointer t)), forall (i:Z),
  ((offset_max a (shift p i)) = ((offset_max a p) - i)%Z).

Axiom offset_min_shift : forall {t:Type} {t_WT:WhyType t},
  forall (a:(alloc_table t)), forall (p:(pointer t)), forall (i:Z),
  ((offset_min a (shift p i)) = ((offset_min a p) - i)%Z).

Axiom neq_shift : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer t)),
  forall (i:Z), forall (j:Z), (~ (i = j)) -> ~ ((shift p i) = (shift p j)).

Axiom same_block_refl : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), (same_block p p).

Axiom same_block_shift : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (i:Z), (same_block p (shift p i)).

Axiom same_block_symm : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (q:(pointer t)), (same_block p q) <-> (same_block q p).

Axiom same_block_trans : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (q:(pointer t)), forall (r:(pointer t)), ((same_block p q) /\
  (same_block q r)) -> (same_block p r).

Axiom same_block_shift_right : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pointer t)), forall (i:Z), (same_block p
  q) -> (same_block p (shift q i)).

Axiom same_block_shift_left : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pointer t)), forall (i:Z), (same_block q
  p) -> (same_block (shift q i) p).

Axiom sub_pointer_shift : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)) (q:(pointer t)), (same_block p q) -> (p = (shift q
  (sub_pointer p q))).

Axiom sub_pointer_self : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), ((sub_pointer p p) = 0%Z).

Axiom sub_pointer_zero : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)) (q:(pointer t)), (same_block p q) -> (((sub_pointer p q) = 0%Z) ->
  (p = q)).

Axiom sub_pointer_shift_left : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)) (q:(pointer t)) (i:Z), (same_block p q) ->
  ((sub_pointer (shift p i) q) = ((sub_pointer p q) + i)%Z).

Axiom sub_pointer_shift_right : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)) (q:(pointer t)) (i:Z), (same_block p q) ->
  ((sub_pointer p (shift q i)) = ((sub_pointer p q) - i)%Z).

Axiom sub_pointer_neg : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)) (q:(pointer t)), ((sub_pointer p q) = (-(sub_pointer q p))%Z).

(* Why3 assumption *)
Definition memory (t:Type) (v:Type) := (map.Map.map (pointer t) v).

Axiom pset : forall (t:Type), Type.
Parameter pset_WhyType : forall (t:Type) {t_WT:WhyType t}, WhyType (pset t).
Existing Instance pset_WhyType.

Parameter pset_empty: forall {t:Type} {t_WT:WhyType t}, (pset t).

Parameter pset_singleton: forall {t:Type} {t_WT:WhyType t}, (pointer t) ->
  (pset t).

Parameter pset_deref: forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, (map.Map.map (pointer t) (pointer v)) -> (pset
  t) -> (pset v).

Parameter pset_union: forall {t:Type} {t_WT:WhyType t}, (pset t) -> (pset
  t) -> (pset t).

Parameter pset_all: forall {z:Type} {z_WT:WhyType z}, (pset z) -> (pset z).

Parameter pset_range: forall {t:Type} {t_WT:WhyType t}, (pset t) -> Z -> Z ->
  (pset t).

Parameter pset_range_left: forall {z:Type} {z_WT:WhyType z}, (pset z) -> Z ->
  (pset z).

Parameter pset_range_right: forall {z:Type} {z_WT:WhyType z}, (pset z) ->
  Z -> (pset z).

Parameter in_pset: forall {t:Type} {t_WT:WhyType t}, (pointer t) -> (pset
  t) -> Prop.

(* Why3 assumption *)
Definition pset_disjoint {t:Type} {t_WT:WhyType t} (ps1:(pset t)) (ps2:(pset
  t)): Prop := forall (p:(pointer t)), ~ ((in_pset p ps1) /\ (in_pset p
  ps2)).

Parameter pset_included: forall {t:Type} {t_WT:WhyType t}, (pset t) -> (pset
  t) -> Prop.

Axiom in_pset_empty : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), ~ (in_pset p (pset_empty : (pset t))).

Axiom in_pset_singleton : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pointer t)), (in_pset p
  (pset_singleton q)) <-> (p = q).

Axiom in_pset_deref : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (p:(pointer v)), forall (m:(map.Map.map
  (pointer t) (pointer v))), forall (q:(pset t)), (in_pset p (pset_deref m
  q)) <-> exists r:(pointer t), (in_pset r q) /\ (p = (map.Map.get m r)).

Axiom in_pset_deref_singleton : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (p:(pointer v)), forall (m:(map.Map.map
  (pointer t) (pointer v))), forall (q:(pointer t)), (in_pset p (pset_deref m
  (pset_singleton q))) <-> (p = (map.Map.get m q)).

Axiom in_pset_all : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer t)),
  forall (q:(pset t)), (in_pset p (pset_all q)) <-> exists r:(pointer t),
  (in_pset r q) /\ (same_block p r).

Axiom in_pset_all_singleton : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pointer t)), (in_pset p
  (pset_all (pset_singleton q))) <-> (same_block p q).

Axiom in_pset_range : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (q:(pset t)), forall (a:Z), forall (b:Z), (in_pset p
  (pset_range q a b)) <-> exists i:Z, exists r:(pointer t), (a <= i)%Z /\
  ((i <= b)%Z /\ ((in_pset r q) /\ (p = (shift r i)))).

Axiom in_pset_range_singleton : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pointer t)), forall (a:Z) (b:Z),
  (in_pset p (pset_range (pset_singleton q) a b)) <-> ((same_block p q) /\
  ((a <= (sub_pointer p q))%Z /\ ((sub_pointer p q) <= b)%Z)).

Axiom in_pset_range_left : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pset t)), forall (b:Z), (in_pset p
  (pset_range_left q b)) <-> exists i:Z, exists r:(pointer t), (i <= b)%Z /\
  ((in_pset r q) /\ (p = (shift r i))).

Axiom in_pset_range_right : forall {t:Type} {t_WT:WhyType t},
  forall (p:(pointer t)), forall (q:(pset t)), forall (a:Z), (in_pset p
  (pset_range_right q a)) <-> exists i:Z, exists r:(pointer t), (a <= i)%Z /\
  ((in_pset r q) /\ (p = (shift r i))).

Axiom in_pset_union : forall {t:Type} {t_WT:WhyType t}, forall (p:(pointer
  t)), forall (s1:(pset t)), forall (s2:(pset t)), (in_pset p (pset_union s1
  s2)) <-> ((in_pset p s1) \/ (in_pset p s2)).

Axiom in_pset_union_singleton : forall {t:Type} {t_WT:WhyType t},
  forall (p1:(pointer t)), forall (p2:(pointer t)), forall (p:(pointer t)),
  (in_pset p (pset_union (pset_singleton p1) (pset_singleton p2))) <->
  ((p = p1) \/ (p = p2)).

Axiom in_pset_union_all_singleton : forall {t:Type} {t_WT:WhyType t},
  forall (p1:(pointer t)), forall (p2:(pointer t)), forall (p:(pointer t)),
  (in_pset p (pset_union (pset_all (pset_singleton p1))
  (pset_all (pset_singleton p2)))) <-> ((same_block p p1) \/ (same_block p
  p2)).

(* Why3 assumption *)
Definition not_assigns {t:Type} {t_WT:WhyType t} {v:Type} {v_WT:WhyType v}
  (a1:(alloc_table t)) (a2:(alloc_table t)) (m1:(map.Map.map (pointer t) v))
  (m2:(map.Map.map (pointer t) v)) (l:(pset t)): Prop := forall (p:(pointer
  t)), ((valid a1 p) /\ (valid a2 p)) -> ((~ (in_pset p l)) ->
  ((map.Map.get m2 p) = (map.Map.get m1 p))).

Axiom not_assigns_refl : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (a1:(alloc_table t)),
  forall (a2:(alloc_table t)), forall (m:(map.Map.map (pointer t) v)),
  forall (l:(pset t)), (not_assigns a1 a2 m m l).

Axiom not_assigns_trans : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (a1:(alloc_table t)),
  forall (a2:(alloc_table t)), forall (m1:(map.Map.map (pointer t) v)),
  forall (m2:(map.Map.map (pointer t) v)), forall (m3:(map.Map.map (pointer
  t) v)), forall (l:(pset t)), (not_assigns a1 a2 m1 m2 l) -> ((not_assigns
  a1 a2 m2 m3 l) -> (not_assigns a1 a2 m1 m3 l)).

(* Why3 assumption *)
Definition not_assigns_strong {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v} (m1:(map.Map.map (pointer t) v)) (m2:(map.Map.map
  (pointer t) v)) (l:(pset t)): Prop := forall (p:(pointer t)), (~ (in_pset p
  l)) -> ((map.Map.get m2 p) = (map.Map.get m1 p)).

Axiom not_assigns_strong1 : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (m1:(map.Map.map (pointer t) v)),
  forall (m2:(map.Map.map (pointer t) v)), forall (l:(pset t)),
  (not_assigns_strong m1 m2 l) -> forall (a1:(alloc_table t)),
  forall (a2:(alloc_table t)), (not_assigns a1 a2 m1 m2 l).

Axiom tag_id : forall (t:Type), Type.
Parameter tag_id_WhyType : forall (t:Type) {t_WT:WhyType t},
  WhyType (tag_id t).
Existing Instance tag_id_WhyType.

(* Why3 assumption *)
Definition tag_table (t:Type) := (map.Map.map (pointer t) (tag_id t)).

Parameter store_tags: forall {t:Type} {t_WT:WhyType t}, (map.Map.map (pointer
  t) (tag_id t)) -> (pointer t) -> (tag_id t) -> (map.Map.map (pointer t)
  (tag_id t)).

Axiom store_tags1 : forall {t:Type} {t_WT:WhyType t}, forall (t1:(map.Map.map
  (pointer t) (tag_id t))), forall (p:(pointer t)), forall (s:(tag_id t)),
  forall (q:(pointer t)), let result := (map.Map.get (store_tags t1 p s)
  q) in (((same_block p q) -> (result = s)) /\ ((~ (same_block p q)) ->
  (result = (map.Map.get t1 q)))).

Parameter int_of_tag: forall {t:Type} {t_WT:WhyType t}, (tag_id t) -> Z.

Parameter parenttag: forall {t:Type} {t_WT:WhyType t}, (tag_id t) -> (tag_id
  t) -> Prop.

Axiom proper_parenttag : forall {t:Type} {t_WT:WhyType t}, forall (t1:(tag_id
  t)), forall (t2:(tag_id t)), (parenttag t1 t2) -> ~ (t1 = t2).

Axiom int_of_parent_tag : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(tag_id t)), forall (t2:(tag_id t)), (parenttag t1 t2) ->
  ((int_of_tag t2) < (int_of_tag t1))%Z.

Parameter subtag: forall {t:Type} {t_WT:WhyType t}, (tag_id t) -> (tag_id
  t) -> Prop.

Parameter cast_factor: forall {t:Type} {t_WT:WhyType t}, (tag_id t) ->
  (tag_id t) -> Z.

Parameter subtag_bool: forall {t:Type} {t_WT:WhyType t}, (tag_id t) ->
  (tag_id t) -> bool.

Axiom subtag_bool_def : forall {t:Type} {t_WT:WhyType t}, forall (t1:(tag_id
  t)), forall (t2:(tag_id t)), ((subtag_bool t1 t2) = true) <-> (subtag t1
  t2).

Axiom subtag_refl : forall {t:Type} {t_WT:WhyType t}, forall (t1:(tag_id t)),
  (subtag t1 t1).

Axiom subtag_parent : forall {t:Type} {t_WT:WhyType t}, forall (t1:(tag_id
  t)), forall (t2:(tag_id t)), forall (t3:(tag_id t)), (subtag t1 t2) ->
  ((parenttag t2 t3) -> (subtag t1 t3)).

Axiom cast_factor_trans : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(tag_id t)), forall (t2:(tag_id t)), forall (t3:(tag_id t)),
  let c12 := (cast_factor t1 t2) in let c23 := (cast_factor t2 t3) in
  let c13 := (cast_factor t1 t3) in ((((0%Z < c12)%Z /\ (0%Z < c23)%Z) ->
  (c13 = (c12 * c23)%Z)) /\ ((((0%Z < c12)%Z /\ ((c23 < 0%Z)%Z /\
  (((-c23)%Z < c12)%Z /\ ((ZArith.BinInt.Z.rem c12 (-c23)%Z) = 0%Z)))) ->
  (c13 = (ZArith.BinInt.Z.quot c12 (-c23)%Z))) /\ ((((0%Z < c12)%Z /\
  ((c23 < 0%Z)%Z /\ ((c12 < (-c23)%Z)%Z /\
  ((ZArith.BinInt.Z.rem (-c23)%Z c12) = 0%Z)))) ->
  (c13 = (-(ZArith.BinInt.Z.quot (-c23)%Z c12))%Z)) /\ ((((c12 < 0%Z)%Z /\
  ((0%Z < c23)%Z /\ (((-c12)%Z < c23)%Z /\
  ((ZArith.BinInt.Z.rem c23 (-c12)%Z) = 0%Z)))) ->
  (c13 = (ZArith.BinInt.Z.quot c23 (-c12)%Z))) /\ ((((c12 < 0%Z)%Z /\
  ((0%Z < c23)%Z /\ ((c23 < (-c12)%Z)%Z /\
  ((ZArith.BinInt.Z.rem (-c12)%Z c23) = 0%Z)))) ->
  (c13 = (-(ZArith.BinInt.Z.quot (-c12)%Z c23))%Z)) /\ (((c12 < 0%Z)%Z /\
  (c23 < 0%Z)%Z) -> (c13 = ((-c12)%Z * c23)%Z))))))).

(* Why3 assumption *)
Definition instanceof {t:Type} {t_WT:WhyType t} (t1:(map.Map.map (pointer t)
  (tag_id t))) (p:(pointer t)) (s:(tag_id t)): Prop := (subtag
  (map.Map.get t1 p) s).

Parameter instanceof_bool: forall {t:Type} {t_WT:WhyType t}, (map.Map.map
  (pointer t) (tag_id t)) -> (pointer t) -> (tag_id t) -> bool.

Axiom instanceof_bool_def : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (pointer t) (tag_id t))) (p:(pointer t)) (s:(tag_id
  t)), ((instanceof t1 p s) -> ((instanceof_bool t1 p s) = true)) /\
  ((~ (instanceof t1 p s)) -> ((instanceof_bool t1 p s) = false)).

Parameter downcast: forall {t:Type} {t_WT:WhyType t}, (map.Map.map (pointer
  t) (tag_id t)) -> (pointer t) -> (tag_id t) -> (pointer t).

Axiom downcast_reduce : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (pointer t) (tag_id t))), forall (p:(pointer t)),
  forall (s2:(tag_id t)), forall (s1:(tag_id t)), (~ ((cast_factor s1
  s2) = 0%Z)) -> ((downcast t1 (downcast t1 p s1) s2) = (downcast t1 p s2)).

Axiom downcast_instanceof : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (pointer t) (tag_id t))), forall (p:(pointer t)),
  forall (s:(tag_id t)), (instanceof t1 p s) -> ((downcast t1 p s) = p).

Axiom typeof_sidecast : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (pointer t) (tag_id t))), forall (p:(pointer t)),
  forall (s1:(tag_id t)), forall (s2:(tag_id t)), (~ ((cast_factor s1
  s2) = 0%Z)) -> (((map.Map.get t1 p) = s1) -> ((map.Map.get t1 (downcast t1
  p s2)) = s2)).

Parameter bottom_tag: forall {a:Type} {a_WT:WhyType a}, (tag_id a).

Axiom bottom_tag_axiom : forall {t:Type} {t_WT:WhyType t}, forall (t1:(tag_id
  t)), (subtag t1 (bottom_tag : (tag_id t))).

Axiom root_subtag : forall {t:Type} {t_WT:WhyType t}, forall (a:(tag_id t)),
  forall (b:(tag_id t)), forall (c:(tag_id t)), (parenttag a
  (bottom_tag : (tag_id t))) -> ((parenttag b (bottom_tag : (tag_id t))) ->
  ((~ (a = b)) -> ((subtag c a) -> ~ (subtag c b)))).

(* Why3 assumption *)
Definition reinterpret_cast_merge {t:Type} {t_WT:WhyType t} (t1:(map.Map.map
  (pointer t) (tag_id t))) (a1:(alloc_table t)) (a2:(alloc_table t))
  (p:(pointer t)) (s:(tag_id t)) (c:Z): Prop := let ps := (downcast t1 p
  s) in ((forall (i:Z), ((ZArith.BinInt.Z.rem i c) = 0%Z) -> ((downcast t1
  (shift p i) s) = (shift ps (ZArith.BinInt.Z.quot i c)))) /\ ((forall (i:Z),
  ((downcast t1 (shift p (i * c)%Z) s) = (shift ps i))) /\ (((offset_min a2
  ps) = (ZArith.BinInt.Z.quot (offset_min a1 p) c)) /\ ((offset_max a2
  ps) = ((ZArith.BinInt.Z.quot ((offset_max a1 p) + 1%Z)%Z c) - 1%Z)%Z)))).

(* Why3 assumption *)
Definition reinterpret_cast_split {t:Type} {t_WT:WhyType t} (t1:(map.Map.map
  (pointer t) (tag_id t))) (a1:(alloc_table t)) (a2:(alloc_table t))
  (p:(pointer t)) (s:(tag_id t)) (c:Z): Prop := let ps := (downcast t1 p
  s) in ((forall (i:Z), ((downcast t1 (shift p i) s) = (shift ps
  (i * c)%Z))) /\ ((forall (i:Z), ((ZArith.BinInt.Z.rem i c) = 0%Z) ->
  ((downcast t1 (shift p (ZArith.BinInt.Z.quot i c)) s) = (shift ps i))) /\
  (((offset_min a2 ps) = (c * (offset_min a1 p))%Z) /\ ((offset_max a2
  ps) = ((c * ((offset_max a1 p) + 1%Z)%Z)%Z - 1%Z)%Z)))).

(* Why3 assumption *)
Definition reinterpret_cast_retain {t:Type} {t_WT:WhyType t} (t1:(map.Map.map
  (pointer t) (tag_id t))) (a1:(alloc_table t)) (a2:(alloc_table t))
  (p:(pointer t)) (s:(tag_id t)): Prop := let ps := (downcast t1 p s) in
  ((forall (i:Z), ((downcast t1 (shift p i) s) = (shift ps i))) /\
  (((offset_min a2 ps) = (offset_min a1 p)) /\ ((offset_max a2
  ps) = (offset_max a1 p)))).

Parameter bw_compl: Z -> Z.

Parameter bw_and: Z -> Z -> Z.

Axiom bw_and_not_null : forall (a:Z), forall (b:Z), (~ ((bw_and a
  b) = 0%Z)) -> ((~ (a = 0%Z)) /\ ~ (b = 0%Z)).

Parameter bw_xor: Z -> Z -> Z.

Parameter bw_or: Z -> Z -> Z.

Parameter pow2: Z -> Z.

Axiom pow2_definition : ((pow2 0%Z) = 1%Z) /\ (((pow2 1%Z) = 2%Z) /\
  (((pow2 2%Z) = 4%Z) /\ (((pow2 3%Z) = 8%Z) /\ (((pow2 4%Z) = 16%Z) /\
  (((pow2 5%Z) = 32%Z) /\ (((pow2 6%Z) = 64%Z) /\ (((pow2 7%Z) = 128%Z) /\
  (((pow2 8%Z) = 256%Z) /\ (((pow2 9%Z) = 512%Z) /\
  (((pow2 10%Z) = 1024%Z) /\ (((pow2 11%Z) = 2048%Z) /\
  (((pow2 12%Z) = 4096%Z) /\ (((pow2 13%Z) = 8192%Z) /\
  (((pow2 14%Z) = 16384%Z) /\ (((pow2 15%Z) = 32768%Z) /\
  (((pow2 16%Z) = 65536%Z) /\ (((pow2 17%Z) = 131072%Z) /\
  (((pow2 18%Z) = 262144%Z) /\ (((pow2 19%Z) = 524288%Z) /\
  (((pow2 20%Z) = 1048576%Z) /\ (((pow2 21%Z) = 2097152%Z) /\
  (((pow2 22%Z) = 4194304%Z) /\ (((pow2 23%Z) = 8388608%Z) /\
  (((pow2 24%Z) = 16777216%Z) /\ (((pow2 25%Z) = 33554432%Z) /\
  (((pow2 26%Z) = 67108864%Z) /\ (((pow2 27%Z) = 134217728%Z) /\
  (((pow2 28%Z) = 268435456%Z) /\ (((pow2 29%Z) = 536870912%Z) /\
  (((pow2 30%Z) = 1073741824%Z) /\
  ((pow2 31%Z) = 2147483648%Z))))))))))))))))))))))))))))))).

Axiom bw_or_plus : forall (a:Z), forall (b:Z), ((0%Z <= a)%Z /\
  ((0%Z <= b)%Z /\ ((bw_and a b) = 0%Z))) -> ((bw_or a b) = (a + b)%Z).

Axiom bw_and_mod : forall (a:Z) (m:Z), ((0%Z <= a)%Z /\ (0%Z <= m)%Z) ->
  ((exists k:Z, ((m + 1%Z)%Z = (pow2 k))) -> ((bw_and a
  m) = (ZArith.BinInt.Z.rem a (m + 1%Z)%Z))).

Parameter bw_set: Z -> Z -> Prop.

Axiom bw_set1 : forall (pos:Z) (n:Z), ((0%Z <= pos)%Z /\ (0%Z <= n)%Z) ->
  ((bw_set pos n) <-> ~ ((bw_and (pow2 pos) n) = 0%Z)).

Axiom pow2_bw_set : forall (n:Z), forall (m:Z), ((0%Z <= n)%Z /\
  (0%Z <= m)%Z) -> ((bw_set n (pow2 m)) <-> (n = m)).

Axiom zero_bw_set : forall (n:Z), (0%Z <= n)%Z -> ~ (bw_set n 0%Z).

Axiom zero_bw_set_iff1 : forall (a:Z), forall (n:Z), ((a = 0%Z) /\
  (0%Z <= n)%Z) -> ~ (bw_set n a).

Axiom zero_bw_set_iff2 : forall (a:Z), forall (n:Z), ((0%Z <= a)%Z /\
  ((0%Z <= n)%Z /\ (bw_set n a))) -> ~ (a = 0%Z).

Axiom bw_and_self : forall (a:Z), ((bw_and a a) = a).

Axiom bw_or_self : forall (a:Z), ((bw_or a a) = a).

Axiom bw_and_definition : forall (n:Z), forall (a:Z), forall (b:Z),
  ((0%Z <= n)%Z /\ ((0%Z <= a)%Z /\ (0%Z <= b)%Z)) -> ((bw_set n (bw_and a
  b)) <-> ((bw_set n a) /\ (bw_set n b))).

Axiom bw_or_definition : forall (n:Z), forall (a:Z), forall (b:Z),
  ((0%Z <= n)%Z /\ ((0%Z <= a)%Z /\ (0%Z <= b)%Z)) -> ((bw_set n (bw_or a
  b)) <-> ((bw_set n a) \/ (bw_set n b))).

Axiom bw_xor_definition : forall (n:Z), forall (a:Z), forall (b:Z),
  ((0%Z <= n)%Z /\ ((0%Z <= a)%Z /\ (0%Z <= b)%Z)) -> ((bw_set n (bw_xor a
  b)) <-> ~ ((bw_set n a) <-> (bw_set n b))).

Axiom bw_and_assoc : forall (a:Z), forall (b:Z), forall (c:Z),
  ((bw_and (bw_and a b) c) = (bw_and a (bw_and b c))).

Axiom bw_or_assoc : forall (a:Z), forall (b:Z), forall (c:Z),
  ((bw_or (bw_or a b) c) = (bw_or a (bw_or b c))).

Axiom bw_xor_assoc : forall (a:Z), forall (b:Z), forall (c:Z),
  ((bw_xor (bw_xor a b) c) = (bw_xor a (bw_xor b c))).

Axiom bw_and_comm : forall (a:Z), forall (b:Z), ((bw_and a b) = (bw_and b
  a)).

Axiom bw_or_comm : forall (a:Z), forall (b:Z), ((bw_or a b) = (bw_or b a)).

Axiom bw_xor_comm : forall (a:Z), forall (b:Z), ((bw_xor a b) = (bw_xor b
  a)).

Axiom bw_and_or_distr : forall (a:Z), forall (b:Z), forall (c:Z), ((bw_and a
  (bw_or b c)) = (bw_or (bw_and a b) (bw_and a c))).

Axiom bw_or_and_distr : forall (a:Z), forall (b:Z), forall (c:Z), ((bw_or a
  (bw_and b c)) = (bw_and (bw_or a b) (bw_or a c))).

Axiom bw_and_mono : forall (a:Z), forall (b:Z), ((0%Z <= a)%Z /\
  (0%Z <= b)%Z) -> (((bw_and a b) <= a)%Z /\ ((bw_and a b) <= b)%Z).

Axiom bw_or_mono : forall (a:Z), forall (b:Z), ((0%Z <= a)%Z /\
  (0%Z <= b)%Z) -> ((a <= (bw_or a b))%Z /\ (b <= (bw_or a b))%Z).

Axiom bw_or_nooverflow_signed : forall (a:Z), forall (b:Z),
  ((((-128%Z)%Z <= a)%Z /\ ((a <= 127%Z)%Z /\ (((-128%Z)%Z <= b)%Z /\
  (b <= 127%Z)%Z))) -> (((-128%Z)%Z <= (bw_or a b))%Z /\ ((bw_or a
  b) <= 127%Z)%Z)) /\ (((((-32768%Z)%Z <= a)%Z /\ ((a <= 32767%Z)%Z /\
  (((-32768%Z)%Z <= b)%Z /\ (b <= 32767%Z)%Z))) -> (((-32768%Z)%Z <= (bw_or a
  b))%Z /\ ((bw_or a b) <= 32767%Z)%Z)) /\ (((((-2147483648%Z)%Z <= a)%Z /\
  ((a <= 2147483647%Z)%Z /\ (((-2147483648%Z)%Z <= b)%Z /\
  (b <= 2147483647%Z)%Z))) -> (((-2147483648%Z)%Z <= (bw_or a b))%Z /\
  ((bw_or a b) <= 2147483647%Z)%Z)) /\
  ((((-9223372036854775808%Z)%Z <= a)%Z /\ ((a <= 9223372036854775807%Z)%Z /\
  (((-9223372036854775808%Z)%Z <= b)%Z /\
  (b <= 9223372036854775807%Z)%Z))) ->
  (((-9223372036854775808%Z)%Z <= (bw_or a b))%Z /\ ((bw_or a
  b) <= 9223372036854775807%Z)%Z)))).

Axiom bw_and_nooverflow_signed : forall (a:Z), forall (b:Z),
  ((((-128%Z)%Z <= a)%Z /\ ((a <= 127%Z)%Z /\ (((-128%Z)%Z <= b)%Z /\
  (b <= 127%Z)%Z))) -> (((-128%Z)%Z <= (bw_and a b))%Z /\ ((bw_and a
  b) <= 127%Z)%Z)) /\ (((((-32768%Z)%Z <= a)%Z /\ ((a <= 32767%Z)%Z /\
  (((-32768%Z)%Z <= b)%Z /\ (b <= 32767%Z)%Z))) ->
  (((-32768%Z)%Z <= (bw_and a b))%Z /\ ((bw_and a b) <= 32767%Z)%Z)) /\
  (((((-2147483648%Z)%Z <= a)%Z /\ ((a <= 2147483647%Z)%Z /\
  (((-2147483648%Z)%Z <= b)%Z /\ (b <= 2147483647%Z)%Z))) ->
  (((-2147483648%Z)%Z <= (bw_and a b))%Z /\ ((bw_and a
  b) <= 2147483647%Z)%Z)) /\ ((((-9223372036854775808%Z)%Z <= a)%Z /\
  ((a <= 9223372036854775807%Z)%Z /\ (((-9223372036854775808%Z)%Z <= b)%Z /\
  (b <= 9223372036854775807%Z)%Z))) ->
  (((-9223372036854775808%Z)%Z <= (bw_and a b))%Z /\ ((bw_and a
  b) <= 9223372036854775807%Z)%Z)))).

Axiom bw_xor_nooverflow_signed : forall (a:Z), forall (b:Z),
  ((((-128%Z)%Z <= a)%Z /\ ((a <= 127%Z)%Z /\ (((-128%Z)%Z <= b)%Z /\
  (b <= 127%Z)%Z))) -> (((-128%Z)%Z <= (bw_xor a b))%Z /\ ((bw_xor a
  b) <= 127%Z)%Z)) /\ (((((-32768%Z)%Z <= a)%Z /\ ((a <= 32767%Z)%Z /\
  (((-32768%Z)%Z <= b)%Z /\ (b <= 32767%Z)%Z))) ->
  (((-32768%Z)%Z <= (bw_xor a b))%Z /\ ((bw_xor a b) <= 32767%Z)%Z)) /\
  (((((-2147483648%Z)%Z <= a)%Z /\ ((a <= 2147483647%Z)%Z /\
  (((-2147483648%Z)%Z <= b)%Z /\ (b <= 2147483647%Z)%Z))) ->
  (((-2147483648%Z)%Z <= (bw_xor a b))%Z /\ ((bw_xor a
  b) <= 2147483647%Z)%Z)) /\ ((((-9223372036854775808%Z)%Z <= a)%Z /\
  ((a <= 9223372036854775807%Z)%Z /\ (((-9223372036854775808%Z)%Z <= b)%Z /\
  (b <= 9223372036854775807%Z)%Z))) ->
  (((-9223372036854775808%Z)%Z <= (bw_xor a b))%Z /\ ((bw_xor a
  b) <= 9223372036854775807%Z)%Z)))).

Axiom bw_or_nooverflow_unsigned : forall (a:Z), forall (b:Z),
  (((0%Z <= a)%Z /\ ((a <= 255%Z)%Z /\ ((0%Z <= b)%Z /\ (b <= 255%Z)%Z))) ->
  ((0%Z <= (bw_or a b))%Z /\ ((bw_or a b) <= 255%Z)%Z)) /\ ((((0%Z <= a)%Z /\
  ((a <= 65535%Z)%Z /\ ((0%Z <= b)%Z /\ (b <= 65535%Z)%Z))) ->
  ((0%Z <= (bw_or a b))%Z /\ ((bw_or a b) <= 65535%Z)%Z)) /\
  ((((0%Z <= a)%Z /\ ((a <= 4294967295%Z)%Z /\ ((0%Z <= b)%Z /\
  (b <= 4294967295%Z)%Z))) -> ((0%Z <= (bw_or a b))%Z /\ ((bw_or a
  b) <= 4294967295%Z)%Z)) /\ (((0%Z <= a)%Z /\
  ((a <= 18446744073709551615%Z)%Z /\ ((0%Z <= b)%Z /\
  (b <= 18446744073709551615%Z)%Z))) -> ((0%Z <= (bw_or a b))%Z /\ ((bw_or a
  b) <= 18446744073709551615%Z)%Z)))).

Axiom bw_and_nooverflow_unsigned : forall (a:Z), forall (b:Z),
  (((0%Z <= a)%Z /\ ((a <= 255%Z)%Z /\ ((0%Z <= b)%Z /\ (b <= 255%Z)%Z))) ->
  ((0%Z <= (bw_and a b))%Z /\ ((bw_and a b) <= 255%Z)%Z)) /\
  ((((0%Z <= a)%Z /\ ((a <= 65535%Z)%Z /\ ((0%Z <= b)%Z /\
  (b <= 65535%Z)%Z))) -> ((0%Z <= (bw_and a b))%Z /\ ((bw_and a
  b) <= 65535%Z)%Z)) /\ ((((0%Z <= a)%Z /\ ((a <= 4294967295%Z)%Z /\
  ((0%Z <= b)%Z /\ (b <= 4294967295%Z)%Z))) -> ((0%Z <= (bw_and a b))%Z /\
  ((bw_and a b) <= 4294967295%Z)%Z)) /\ (((0%Z <= a)%Z /\
  ((a <= 18446744073709551615%Z)%Z /\ ((0%Z <= b)%Z /\
  (b <= 18446744073709551615%Z)%Z))) -> ((0%Z <= (bw_and a b))%Z /\
  ((bw_and a b) <= 18446744073709551615%Z)%Z)))).

Axiom bw_xor_nooverflow_unsigned : forall (a:Z), forall (b:Z),
  (((0%Z <= a)%Z /\ ((a <= 255%Z)%Z /\ ((0%Z <= b)%Z /\ (b <= 255%Z)%Z))) ->
  ((0%Z <= (bw_xor a b))%Z /\ ((bw_xor a b) <= 255%Z)%Z)) /\
  ((((0%Z <= a)%Z /\ ((a <= 65535%Z)%Z /\ ((0%Z <= b)%Z /\
  (b <= 65535%Z)%Z))) -> ((0%Z <= (bw_xor a b))%Z /\ ((bw_xor a
  b) <= 65535%Z)%Z)) /\ ((((0%Z <= a)%Z /\ ((a <= 4294967295%Z)%Z /\
  ((0%Z <= b)%Z /\ (b <= 4294967295%Z)%Z))) -> ((0%Z <= (bw_xor a b))%Z /\
  ((bw_xor a b) <= 4294967295%Z)%Z)) /\ (((0%Z <= a)%Z /\
  ((a <= 18446744073709551615%Z)%Z /\ ((0%Z <= b)%Z /\
  (b <= 18446744073709551615%Z)%Z))) -> ((0%Z <= (bw_xor a b))%Z /\
  ((bw_xor a b) <= 18446744073709551615%Z)%Z)))).

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

Axiom lsl_definition : forall (m:Z), forall (a:Z), forall (n:Z),
  ((0%Z <= m)%Z /\ ((0%Z <= a)%Z /\ (0%Z <= n)%Z)) -> ((~ (bw_set n (lsl a
  m))) <-> ((~ (bw_set (n - m)%Z a)) \/ (n < m)%Z)).

Axiom lsr_definition : forall (m:Z), forall (a:Z), forall (n:Z),
  ((0%Z <= m)%Z /\ ((0%Z <= a)%Z /\ (0%Z <= n)%Z)) -> ((bw_set n (lsr a
  m)) <-> (bw_set (n + m)%Z a)).

Axiom lsl_induction : forall (a:Z), forall (n:Z), forall (m:Z), forall (k:Z),
  ((0%Z <= k)%Z /\ ((0%Z <= n)%Z /\ ((0%Z <= m)%Z /\ (k = (n + m)%Z)))) ->
  ((lsl a k) = (lsl (lsl a n) m)).

Axiom lsr_induction : forall (a:Z), forall (n:Z), forall (m:Z), forall (k:Z),
  ((0%Z <= k)%Z /\ ((0%Z <= n)%Z /\ ((0%Z <= m)%Z /\ (k = (n + m)%Z)))) ->
  ((lsr a k) = (lsr (lsr a n) m)).

Axiom lsl_assoc : forall (n:Z), forall (m:Z), forall (a:Z), ((0%Z <= n)%Z /\
  (0%Z <= m)%Z) -> ((lsl (lsl a m) n) = (lsl (lsl a n) m)).

Axiom lsr_assoc : forall (n:Z), forall (m:Z), forall (a:Z), ((0%Z <= n)%Z /\
  (0%Z <= m)%Z) -> ((lsr (lsr a m) n) = (lsr (lsr a n) m)).

Axiom lsl_init : forall (a:Z), (0%Z <= a)%Z -> ((lsl a 1%Z) = (a * 2%Z)%Z).

Axiom lsl_multiply : forall (a:Z), forall (n:Z), ((0%Z <= a)%Z /\
  (0%Z <= n)%Z) -> ((lsl a n) = (a * (pow2 n))%Z).

Axiom lsr_init : forall (a:Z), (0%Z <= a)%Z -> ((lsr a
  1%Z) = (ZArith.BinInt.Z.quot a 2%Z)).

Axiom lsr_divide : forall (a:Z), forall (n:Z), ((0%Z <= a)%Z /\
  (0%Z <= n)%Z) -> ((lsr a n) = (ZArith.BinInt.Z.quot a (pow2 n))).

(* Why3 assumption *)
Definition allocable {t:Type} {t_WT:WhyType t} (a:(alloc_table t))
  (p:(pointer t)): Prop := ((offset_max a p) = (-1%Z)%Z) /\
  (((-1%Z)%Z < (offset_min a p))%Z /\ ((offset_min a p) = 0%Z)).

(* Why3 assumption *)
Definition freeable {t:Type} {t_WT:WhyType t} (a:(alloc_table t)) (p:(pointer
  t)): Prop := ((offset_min a p) = 0%Z) /\ (0%Z <= (offset_max a p))%Z.

(* Why3 assumption *)
Definition allocated {t:Type} {t_WT:WhyType t} (a:(alloc_table t))
  (p:(pointer t)): Prop := ((offset_min a p) <= (offset_max a p))%Z.

(* Why3 assumption *)
Definition tag_fresh {t:Type} {t_WT:WhyType t} (t1:(map.Map.map (pointer t)
  (tag_id t))) (p:(pointer t)): Prop := ((map.Map.get t1
  p) = (bottom_tag : (tag_id t))).

Axiom alloc_fresh_not_same_block : forall {t:Type} {t_WT:WhyType t},
  forall (p1:(pointer t)), forall (p2:(pointer t)), forall (a:(alloc_table
  t)), ((allocable a p1) /\ (freeable a p2)) -> ~ (same_block p1 p2).

Axiom tag_fresh_not_same_block : forall {t:Type} {t_WT:WhyType t},
  forall (p1:(pointer t)), forall (p2:(pointer t)), forall (t1:(map.Map.map
  (pointer t) (tag_id t))), (((map.Map.get t1 p1) = (bottom_tag : (tag_id
  t))) /\ ~ ((map.Map.get t1 p2) = (bottom_tag : (tag_id t)))) ->
  ~ (same_block p1 p2).

(* Why3 assumption *)
Definition alloc_extends {t:Type} {t_WT:WhyType t} (a1:(alloc_table t))
  (a2:(alloc_table t)): Prop := forall (p:(pointer t)), (valid a1 p) ->
  (((offset_min a1 p) = (offset_min a2 p)) /\ ((offset_max a1
  p) = (offset_max a2 p))).

(* Why3 assumption *)
Definition free_extends {t:Type} {t_WT:WhyType t} (a1:(alloc_table t))
  (a2:(alloc_table t)): Prop := forall (p:(pointer t)), (~ (allocated a1
  p)) -> (((offset_min a1 p) = (offset_min a2 p)) /\ ((offset_max a1
  p) = (offset_max a2 p))).

(* Why3 assumption *)
Definition alloc_block {t:Type} {t_WT:WhyType t} (a1:(alloc_table t))
  (a2:(alloc_table t)) (p:(pointer t)) (n:Z): Prop := forall (q:(pointer t)),
  ((~ (same_block q p)) -> (((offset_min a2 q) = (offset_min a1 q)) /\
  ((offset_max a2 q) = (offset_max a1 q)))) /\ ((same_block q p) ->
  (((offset_min a2 q) = (0%Z - (sub_pointer q p))%Z) /\ ((offset_max a2
  q) = ((n - 1%Z)%Z - (sub_pointer q p))%Z))).

(* Why3 assumption *)
Definition free_block {t:Type} {t_WT:WhyType t} (a1:(alloc_table t))
  (a2:(alloc_table t)) (p:(pointer t)): Prop := forall (q:(pointer t)),
  ((~ (same_block q p)) -> (((offset_min a2 q) = (offset_min a1 q)) /\
  ((offset_max a2 q) = (offset_max a1 q)))) /\ ((same_block q p) ->
  (((offset_min a2 q) = (0%Z - (sub_pointer q p))%Z) /\ ((offset_max a2
  q) = ((-1%Z)%Z - (sub_pointer q p))%Z))).

(* Why3 assumption *)
Definition switch_blocks {t:Type} {t_WT:WhyType t} (a1:(alloc_table t))
  (a2:(alloc_table t)) (p:(pointer t)) (q:(pointer t)) (n:Z): Prop :=
  forall (r:(pointer t)), (((~ (same_block r p)) /\ ~ (same_block r q)) ->
  (((offset_min a2 r) = (offset_min a1 r)) /\ ((offset_max a2
  r) = (offset_max a1 r)))) /\ (((same_block r p) -> (((offset_min a2
  r) = (0%Z - (sub_pointer r p))%Z) /\ ((offset_max a2
  r) = ((-1%Z)%Z - (sub_pointer r p))%Z))) /\ ((same_block r q) ->
  (((offset_min a2 r) = (0%Z - (sub_pointer r q))%Z) /\ ((offset_max a2
  r) = ((n - 1%Z)%Z - (sub_pointer r q))%Z)))).

Parameter rmem: forall {t:Type} {t_WT:WhyType t} {v1:Type} {v1_WT:WhyType v1}
  {v2:Type} {v2_WT:WhyType v2}, (map.Map.map (pointer t) v1) -> (map.Map.map
  (pointer t) v2).

Parameter rfactor: forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, (map.Map.map (pointer t) v) -> Z.

Parameter rpointer_new: forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, (map.Map.map (pointer t) v) -> (pointer t) ->
  (pointer t).

Parameter pset_reinterpret: forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, (map.Map.map (pointer t) v) -> (pset t) -> (pset
  t).

Axiom pset_reinterpret_empty : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (m:(map.Map.map (pointer t) v)),
  ((pset_reinterpret m (pset_empty : (pset t))) = (pset_empty : (pset t))).

Axiom pset_reinterpret_pset_range : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (m:(map.Map.map (pointer t) v)),
  forall (p:(pointer t)), forall (a:Z) (b:Z), ((0%Z < (rfactor m))%Z ->
  ((pset_reinterpret m (pset_range (pset_singleton p) a
  b)) = (pset_range (pset_singleton (rpointer_new m p)) (a * (rfactor m))%Z
  (((b + 1%Z)%Z * (rfactor m))%Z - 1%Z)%Z))) /\ (((((rfactor m) < 0%Z)%Z /\
  (((ZArith.BinInt.Z.rem a (rfactor m)) = 0%Z) /\
  ((ZArith.BinInt.Z.rem (b + 1%Z)%Z (rfactor m)) = 0%Z))) ->
  ((pset_reinterpret m (pset_range (pset_singleton p) a
  b)) = (pset_range (pset_singleton (rpointer_new m p))
  (ZArith.BinInt.Z.quot a (rfactor m))
  ((ZArith.BinInt.Z.quot (b + 1%Z)%Z (rfactor m)) - 1%Z)%Z))) /\
  (((rfactor m) = 0%Z) -> ((pset_reinterpret m (pset_range (pset_singleton p)
  a b)) = (pset_range (pset_singleton (rpointer_new m p)) a b)))).

Axiom pset_reinterpret_pset_union_distrib : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (m:(map.Map.map (pointer t) v)),
  forall (l1:(pset t)) (l2:(pset t)), ((pset_reinterpret m (pset_union l1
  l2)) = (pset_union (pset_reinterpret m l1) (pset_reinterpret m l2))).

Axiom rmem_not_assigns : forall {t:Type} {t_WT:WhyType t}
  {v1:Type} {v1_WT:WhyType v1} {v2:Type} {v2_WT:WhyType v2},
  forall (m1:(map.Map.map (pointer t) v1)), forall (m3:(map.Map.map (pointer
  t) v2)), forall (a1:(alloc_table t)) (a2:(alloc_table t)), forall (l:(pset
  t)), ((not_assigns a1 a2 (rmem m1: (map.Map.map (pointer t) v2)) m3 l) <->
  (not_assigns a1 a2 m1 (rmem m3: (map.Map.map (pointer t) v1))
  (pset_reinterpret m3 l))) /\ ((not_assigns a1 a2 (rmem m1: (map.Map.map
  (pointer t) v2)) m3 (pset_reinterpret m1 l)) <-> (not_assigns a1 a2 m1
  (rmem m3: (map.Map.map (pointer t) v1)) l)).

(* Why3 assumption *)
Definition alloc_same_except {t:Type} {t_WT:WhyType t} (a1:(alloc_table t))
  (a2:(alloc_table t)) (l:(pset t)): Prop := forall (p:(pointer t)),
  (~ (in_pset p l)) -> (((offset_min a1 p) = (offset_min a2 p)) /\
  ((offset_max a1 p) = (offset_max a2 p))).

Axiom alloc_same_except_included : forall {t:Type} {t_WT:WhyType t},
  forall (a1:(alloc_table t)), forall (a2:(alloc_table t)), forall (l1:(pset
  t)), forall (l2:(pset t)), ((pset_included l1 l2) /\ (alloc_same_except a1
  a2 l1)) -> (alloc_same_except a1 a2 l2).

Axiom alloc_same_except_trans : forall {t:Type} {t_WT:WhyType t},
  forall (l:(pset t)), forall (a1:(alloc_table t)), forall (a2:(alloc_table
  t)), forall (a3:(alloc_table t)), ((alloc_same_except a1 a2 l) /\
  (alloc_same_except a2 a3 l)) -> (alloc_same_except a1 a3 l).

(* Why3 assumption *)
Definition alloc_blockset {t:Type} {t_WT:WhyType t} (a1:(alloc_table t))
  (a2:(alloc_table t)) (q:(pset t)): Prop := forall (p:(pointer t)),
  (forall (r:(pointer t)), (in_pset r q) -> ~ (same_block p r)) ->
  (((offset_min a1 p) = (offset_min a2 p)) /\ ((offset_max a1
  p) = (offset_max a2 p))).

(* Why3 assumption *)
Definition tag_extends {t:Type} {t_WT:WhyType t} (t1:(map.Map.map (pointer t)
  (tag_id t))) (t2:(map.Map.map (pointer t) (tag_id t))): Prop :=
  forall (p:(pointer t)), (~ ((map.Map.get t1 p) = (bottom_tag : (tag_id
  t)))) -> ((map.Map.get t2 p) = (map.Map.get t1 p)).

(* Why3 assumption *)
Definition tag_same_except {t:Type} {t_WT:WhyType t} (t1:(map.Map.map
  (pointer t) (tag_id t))) (t2:(map.Map.map (pointer t) (tag_id t))) (l:(pset
  t)): Prop := forall (p:(pointer t)), (~ ((map.Map.get t1
  p) = (bottom_tag : (tag_id t)))) -> ((map.Map.get t2 p) = (map.Map.get t1
  p)).

Axiom tag_same_except_refl : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (pointer t) (tag_id t))), forall (l:(pset t)),
  (tag_same_except t1 t1 l).

(* Why3 assumption *)
Definition alloc_tag_blockset {t:Type} {t_WT:WhyType t} (t1:(map.Map.map
  (pointer t) (tag_id t))) (t2:(map.Map.map (pointer t) (tag_id t))) (q:(pset
  t)): Prop := forall (p:(pointer t)), (~ ((map.Map.get t1
  p) = (bottom_tag : (tag_id t)))) -> ((map.Map.get t2 p) = (map.Map.get t1
  p)).

