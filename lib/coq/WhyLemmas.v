(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: WhyLemmas.v,v 1.2 2002-11-14 08:54:02 filliatr Exp $ *)

Implicit Arguments On.

Lemma loop_variant_1 : 
  (A:Set)(v,phi0:A)(I:Prop)(P:A->Prop)
  v=phi0 -> (I /\ (P phi0)) -> (P v).
Proof.
Intros. Rewrite H. Tauto.
Save.

