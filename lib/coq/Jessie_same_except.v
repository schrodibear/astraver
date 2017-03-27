(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require Jessie_pointer.
Require int.Int.
Require Jessie_alloc_table.
Require map.Map.
Require Jessie_pset.
Require Jessie_tag_id.
Require Jessie_tag.
Require Jessie_tag_table_type.
Require Jessie_tag_table.

(* Why3 assumption *)
Definition alloc_same_except {t:Type} {t_WT:WhyType t}
  (a1:(Jessie_alloc_table.alloc_table t)) (a2:(Jessie_alloc_table.alloc_table
  t)) (l:(Jessie_pset.pset t)): Prop := forall (p:(Jessie_pointer.pointer
  t)), (~ (Jessie_pset.in_pset p l)) -> (((Jessie_alloc_table.offset_min a1
  p) = (Jessie_alloc_table.offset_min a2 p)) /\
  ((Jessie_alloc_table.offset_max a1 p) = (Jessie_alloc_table.offset_max a2
  p))).

Axiom Alloc_same_except_trans : forall {t:Type} {t_WT:WhyType t},
  forall (l:(Jessie_pset.pset t)), forall (a1:(Jessie_alloc_table.alloc_table
  t)), forall (a2:(Jessie_alloc_table.alloc_table t)),
  forall (a3:(Jessie_alloc_table.alloc_table t)), ((alloc_same_except a1 a2
  l) /\ (alloc_same_except a2 a3 l)) -> (alloc_same_except a1 a3 l).

(* Why3 assumption *)
Definition tag_same_except {t:Type} {t_WT:WhyType t} (t1:(map.Map.map
  (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id t))) (t2:(map.Map.map
  (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id t))) (l:(Jessie_pset.pset
  t)): Prop := forall (p:(Jessie_pointer.pointer t)), (~ ((map.Map.get t1
  p) = (Jessie_tag.bottom_tag : (Jessie_tag_id.tag_id t)))) ->
  ((map.Map.get t2 p) = (map.Map.get t1 p)).

Axiom Tag_same_except_refl : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id
  t))), forall (l:(Jessie_pset.pset t)), (tag_same_except t1 t1 l).
