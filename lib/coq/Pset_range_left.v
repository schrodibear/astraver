(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require Pointer.
Require int.Int.
Require Pset.

Parameter pset_range_left: forall {z:Type} {z_WT:WhyType z}, (Pset.pset z) ->
  Numbers.BinNums.Z -> (Pset.pset z).

Axiom In_pset_range_left : forall {t:Type} {t_WT:WhyType t},
  forall (p:(Pointer.pointer t)), forall (q:(Pset.pset t)),
  forall (b:Numbers.BinNums.Z), (Pset.in_pset p (pset_range_left q b)) <->
  exists i:Numbers.BinNums.Z, exists r:(Pointer.pointer t), (i <= b)%Z /\
  ((Pset.in_pset r q) /\ (p = (Pointer.shift r i))).

