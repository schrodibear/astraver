(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require Jessie_pointer.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.
Require Jessie_alloc_table.
Require Jessie_memory.
Require map.Map.
Require Jessie_pset.
Require Jessie_pset_range.
Require Jessie_pset_union.
Require Jessie_assigns.

Parameter rmem: forall {t:Type} {t_WT:WhyType t} {v1:Type} {v1_WT:WhyType v1}
  {v2:Type} {v2_WT:WhyType v2}, (map.Map.map (Jessie_pointer.pointer t)
  v1) -> (map.Map.map (Jessie_pointer.pointer t) v2).

Parameter rfactor: forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, (map.Map.map (Jessie_pointer.pointer t) v) -> Z.

Parameter rpointer_new: forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, (map.Map.map (Jessie_pointer.pointer t) v) ->
  (Jessie_pointer.pointer t) -> (Jessie_pointer.pointer t).

Parameter pset_reinterpret: forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, (map.Map.map (Jessie_pointer.pointer t) v) ->
  (Jessie_pset.pset t) -> (Jessie_pset.pset t).

Axiom Pset_reinterpret_empty : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (m:(map.Map.map (Jessie_pointer.pointer
  t) v)), ((pset_reinterpret m (Jessie_pset.pset_empty : (Jessie_pset.pset
  t))) = (Jessie_pset.pset_empty : (Jessie_pset.pset t))).

Axiom Pset_reinterpret_pset_range : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (m:(map.Map.map (Jessie_pointer.pointer
  t) v)), forall (p:(Jessie_pointer.pointer t)), forall (a:Z) (b:Z),
  ((0%Z < (rfactor m))%Z -> ((pset_reinterpret m
  (Jessie_pset_range.pset_range (Jessie_pset.pset_singleton p) a
  b)) = (Jessie_pset_range.pset_range (Jessie_pset.pset_singleton (rpointer_new m
  p)) (a * (rfactor m))%Z (((b + 1%Z)%Z * (rfactor m))%Z - 1%Z)%Z))) /\
  (((((rfactor m) < 0%Z)%Z /\ (((ZArith.BinInt.Z.rem a (rfactor m)) = 0%Z) /\
  ((ZArith.BinInt.Z.rem (b + 1%Z)%Z (rfactor m)) = 0%Z))) ->
  ((pset_reinterpret m
  (Jessie_pset_range.pset_range (Jessie_pset.pset_singleton p) a
  b)) = (Jessie_pset_range.pset_range (Jessie_pset.pset_singleton (rpointer_new m
  p)) (ZArith.BinInt.Z.quot a (rfactor m))
  ((ZArith.BinInt.Z.quot (b + 1%Z)%Z (rfactor m)) - 1%Z)%Z))) /\
  (((rfactor m) = 0%Z) -> ((pset_reinterpret m
  (Jessie_pset_range.pset_range (Jessie_pset.pset_singleton p) a
  b)) = (Jessie_pset_range.pset_range (Jessie_pset.pset_singleton (rpointer_new m
  p)) a b)))).

Axiom Pset_reinterpret_pset_union_distrib : forall {t:Type} {t_WT:WhyType t}
  {v:Type} {v_WT:WhyType v}, forall (m:(map.Map.map (Jessie_pointer.pointer
  t) v)), forall (l1:(Jessie_pset.pset t)) (l2:(Jessie_pset.pset t)),
  ((pset_reinterpret m (Jessie_pset_union.pset_union l1
  l2)) = (Jessie_pset_union.pset_union (pset_reinterpret m l1)
  (pset_reinterpret m l2))).

Axiom Rmem_not_assigns : forall {t:Type} {t_WT:WhyType t}
  {v1:Type} {v1_WT:WhyType v1} {v2:Type} {v2_WT:WhyType v2},
  forall (m1:(map.Map.map (Jessie_pointer.pointer t) v1)),
  forall (m3:(map.Map.map (Jessie_pointer.pointer t) v2)),
  forall (a1:(Jessie_alloc_table.alloc_table t))
  (a2:(Jessie_alloc_table.alloc_table t)), forall (l:(Jessie_pset.pset t)),
  ((Jessie_assigns.not_assigns a1 a2 (rmem m1: (map.Map.map
  (Jessie_pointer.pointer t) v2)) m3 l) <-> (Jessie_assigns.not_assigns a1 a2
  m1 (rmem m3: (map.Map.map (Jessie_pointer.pointer t) v1))
  (pset_reinterpret m3 l))) /\ ((Jessie_assigns.not_assigns a1 a2
  (rmem m1: (map.Map.map (Jessie_pointer.pointer t) v2)) m3
  (pset_reinterpret m1 l)) <-> (Jessie_assigns.not_assigns a1 a2 m1
  (rmem m3: (map.Map.map (Jessie_pointer.pointer t) v1)) l)).

