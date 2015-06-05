(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require Jessie_pointer.
Require int.Int.
Require Jessie_alloc_table.
Require Jessie_memory.
Require map.Map.
Require Jessie_pset.

(* Why3 assumption *)
Definition not_assigns {t:Type} {t_WT:WhyType t} {v:Type} {v_WT:WhyType v}
  (a1:(Jessie_alloc_table.alloc_table t)) (a2:(Jessie_alloc_table.alloc_table
  t)) (m1:(map.Map.map (Jessie_pointer.pointer t) v)) (m2:(map.Map.map
  (Jessie_pointer.pointer t) v)) (l:(Jessie_pset.pset t)): Prop :=
  forall (p:(Jessie_pointer.pointer t)), ((Jessie_alloc_table.valid a1 p) /\
  (Jessie_alloc_table.valid a2 p)) -> ((~ (Jessie_pset.in_pset p l)) ->
  ((map.Map.get m2 p) = (map.Map.get m1 p))).

Axiom Not_assigns_refl : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (a1:(Jessie_alloc_table.alloc_table t)),
  forall (a2:(Jessie_alloc_table.alloc_table t)), forall (m:(map.Map.map
  (Jessie_pointer.pointer t) v)), forall (l:(Jessie_pset.pset t)),
  (not_assigns a1 a2 m m l).

Axiom Not_assigns_trans : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (a1:(Jessie_alloc_table.alloc_table t)),
  forall (a2:(Jessie_alloc_table.alloc_table t)), forall (m1:(map.Map.map
  (Jessie_pointer.pointer t) v)), forall (m2:(map.Map.map
  (Jessie_pointer.pointer t) v)), forall (m3:(map.Map.map
  (Jessie_pointer.pointer t) v)), forall (l:(Jessie_pset.pset t)),
  (not_assigns a1 a2 m1 m2 l) -> ((not_assigns a1 a2 m2 m3 l) -> (not_assigns
  a1 a2 m1 m3 l)).

