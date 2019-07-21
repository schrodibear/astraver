(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require Pointer.
Require int.Int.
Require Pset.

Parameter pset_union: forall {t:Type} {t_WT:WhyType t}, (Pset.pset t) ->
  (Pset.pset t) -> (Pset.pset t).

Axiom In_pset_union : forall {t:Type} {t_WT:WhyType t},
  forall (p:(Pointer.pointer t)), forall (s1:(Pset.pset t)),
  forall (s2:(Pset.pset t)), (Pset.in_pset p (pset_union s1 s2)) <->
  ((Pset.in_pset p s1) \/ (Pset.in_pset p s2)).

Axiom In_pset_union_singleton : forall {t:Type} {t_WT:WhyType t},
  forall (p1:(Pointer.pointer t)), forall (p2:(Pointer.pointer t)),
  forall (p:(Pointer.pointer t)), (Pset.in_pset p
  (pset_union (Pset.pset_singleton p1) (Pset.pset_singleton p2))) <->
  ((p = p1) \/ (p = p2)).
