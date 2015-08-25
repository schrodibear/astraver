(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require Jessie_pointer.
Require int.Int.
Require map.Map.
Require Jessie_tag_id.
Require Jessie_tag.
Require Jessie_tag_table_type.
Require Jessie_tag_table.

Parameter sidecast: forall {t:Type} {t_WT:WhyType t}, (map.Map.map
  (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id t)) ->
  (Jessie_pointer.pointer t) -> (Jessie_tag_id.tag_id t) ->
  (Jessie_pointer.pointer t).

Axiom Sidecast_refl : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id
  t))), forall (p:(Jessie_pointer.pointer t)),
  forall (s2:(Jessie_tag_id.tag_id t)), ((map.Map.get t1 p) = s2) ->
  ((sidecast t1 p s2) = p).

Axiom Sidecast_extensionality : forall {t:Type} {t_WT:WhyType t},
  forall (p:(Jessie_pointer.pointer t)), forall (t1:(map.Map.map
  (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id t))),
  forall (t2:(map.Map.map (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id
  t))), forall (s:(Jessie_tag_id.tag_id t)), ((map.Map.get t1
  p) = (map.Map.get t2 p)) -> ((sidecast t1 p s) = (sidecast t2 p s)).

Axiom Sidecast_reduce : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id
  t))), forall (p:(Jessie_pointer.pointer t)),
  forall (s1:(Jessie_tag_id.tag_id t)), forall (s2:(Jessie_tag_id.tag_id t)),
  ((sidecast t1 (sidecast t1 p s1) s2) = (sidecast t1 p s2)).

Axiom Typeof_sidecast : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id
  t))), forall (p:(Jessie_pointer.pointer t)),
  forall (s2:(Jessie_tag_id.tag_id t)), (~ ((map.Map.get t1
  p) = (Jessie_tag.bottom_tag : (Jessie_tag_id.tag_id t)))) ->
  ((~ (s2 = (Jessie_tag.bottom_tag : (Jessie_tag_id.tag_id t)))) ->
  ((map.Map.get t1 (sidecast t1 p s2)) = s2)).

Axiom Sidecast_null : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id
  t))), forall (s:(Jessie_tag_id.tag_id t)), ((sidecast t1
  (Jessie_pointer.null : (Jessie_pointer.pointer t))
  s) = (Jessie_pointer.null : (Jessie_pointer.pointer t))).

Axiom Typeof_sidecast_fresh : forall {t:Type} {t_WT:WhyType t},
  forall (t1:(map.Map.map (Jessie_pointer.pointer t) (Jessie_tag_id.tag_id
  t))), forall (p:(Jessie_pointer.pointer t)),
  forall (s2:(Jessie_tag_id.tag_id t)), ((map.Map.get t1
  p) = (Jessie_tag.bottom_tag : (Jessie_tag_id.tag_id t))) ->
  ((map.Map.get t1 (sidecast t1 p
  s2)) = (Jessie_tag.bottom_tag : (Jessie_tag_id.tag_id t))).

