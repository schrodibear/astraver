(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(* $Id: WhyLemmas.v,v 1.6 2003-02-19 10:28:35 filliatr Exp $ *)

(* lemmas used to build automatic proofs *)

(* lemmas used to build automatic proofs *)

Implicit Arguments On.

Lemma loop_variant_1 : 
  (A:Set)(v,phi0:A)(I:Prop)(P:A->Prop)
  v=phi0 -> (I /\ (P phi0)) -> (P v).
Proof.
Intros. Rewrite H. Tauto.
Save.

Lemma why_rewrite_var :
  (A:Set)(x,t:A)x=t->(P:A->Prop)(P x)->(P t).
Proof.
Intros; Case H; Trivial.
Save.
Implicits why_rewrite_var [1 2 3].

Lemma why_boolean_case :
  (A,B,C,D:Prop)
  (b:bool)(if b then A else B)->(A->C)->(B->D)->(if b then C else D).
Proof.
Destruct b; Intuition.
Save.
