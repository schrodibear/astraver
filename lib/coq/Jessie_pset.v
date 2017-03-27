(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require Jessie_pointer.
Require int.Int.

Axiom pset : forall (t:Type), Type.
Parameter pset_WhyType : forall (t:Type) {t_WT:WhyType t}, WhyType (pset t).
Existing Instance pset_WhyType.

Parameter pset_empty: forall {t:Type} {t_WT:WhyType t}, (pset t).

Parameter pset_singleton: forall {t:Type} {t_WT:WhyType t},
  (Jessie_pointer.pointer t) -> (pset t).

Parameter in_pset: forall {t:Type} {t_WT:WhyType t}, (Jessie_pointer.pointer
  t) -> (pset t) -> Prop.

Axiom In_pset_empty : forall {t:Type} {t_WT:WhyType t},
  forall (p:(Jessie_pointer.pointer t)), ~ (in_pset p (pset_empty : (pset
  t))).

Axiom In_pset_singleton : forall {t:Type} {t_WT:WhyType t},
  forall (p:(Jessie_pointer.pointer t)), forall (q:(Jessie_pointer.pointer
  t)), (in_pset p (pset_singleton q)) <-> (p = q).
