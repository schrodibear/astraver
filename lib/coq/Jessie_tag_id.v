(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.

Axiom tag_id : forall (t:Type), Type.
Parameter tag_id_WhyType : forall (t:Type) {t_WT:WhyType t},
  WhyType (tag_id t).
Existing Instance tag_id_WhyType.

Parameter int_of_tag: forall {t:Type} {t_WT:WhyType t}, (tag_id t) -> Z.

