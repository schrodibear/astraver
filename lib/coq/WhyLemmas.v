(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: WhyLemmas.v,v 1.1 2002-11-13 16:12:31 filliatr Exp $ *)

Implicit Arguments On.

Lemma loop_discharge_1 : 
  (A:Set)(v,phi0:A)(I:Prop)(P:A->Prop)
  v=phi0 -> (I /\ (P phi0)) -> (P v).
Proof.
Intros. Rewrite H. Tauto.
Save.

