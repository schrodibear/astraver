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

(* $Id: WhyLemmas.v,v 1.4 2003-02-18 13:32:19 filliatr Exp $ *)

Implicit Arguments On.

Lemma loop_variant_1 : 
  (A:Set)(v,phi0:A)(I:Prop)(P:A->Prop)
  v=phi0 -> (I /\ (P phi0)) -> (P v).
Proof.
Intros. Rewrite H. Tauto.
Save.

Lemma test_annot :
  (A:Set)(x,t:A)x=t->(P:A->Prop)(P x)->(P t).
Proof.
Intros; Case H; Trivial.
Save.

Implicits test_annot [1 2 3].
