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

(* $Id: WhyCM.v,v 1.1 2003-04-10 14:37:43 filliatr Exp $ *)

Require Export WhyArrays.

(* A low level C model *)

Implicit Arguments On.

(* Addresses *)

Parameter adr : Set.

Axiom eq_adr_dec : (a1,a2:adr) { a1=a2 } + { ~a1=a2 }.

Parameter dummy_adr : adr.

(* Pointers *)

Inductive pointer : Set :=
  | null : pointer
  | Ref : adr -> Z -> pointer.

Lemma eq_null_dec : (p:pointer) { p=null } + { ~p=null }.
Proof.
Destruct p; Intuition.
Right; Intro H; Discriminate H.
Save.

(* Stores *)

Section Stores.

Variable T:Set.

Definition cstore : Set := adr -> (array T).

Definition paccess [s:cstore; p:pointer] : T :=
  Cases p of
  | null => (access (s dummy_adr) `0`)
  | (Ref a ofs) => (access (s a) ofs) end.

Definition cstore_update [s:cstore; a:adr; v:(array T)] : cstore :=
  [a':adr]Cases (eq_adr_dec a' a) of 
          | (left _) => v
          | (right _) => (s a') end.

Definition pupdate [s:cstore; p:pointer; v:T] : cstore :=
  Cases p of 
  | null => s
  | (Ref a ofs) => (cstore_update s a (store (s a) ofs v)) end.

(* Pointer validity *)

Definition is_valid [s:cstore; p:pointer] : Prop :=
  Cases p of 
  | null => False
  | (Ref a ofs) => `0 <= ofs < (array_length (s a))` end.

(* access/update lemmas *)

Lemma cstore_update_same : 
  (s:cstore)(a:adr)(v:(array T))
  ((cstore_update s a v) a) = v.
Proof.
Intros. Unfold cstore_update; Case (eq_adr_dec a a); Intuition.
Save.

Lemma pupdate_paccess_same : 
  (s:cstore)(p:pointer)(v:T)
  (is_valid s p) -> (paccess (pupdate s p v) p) = v.
Proof.
Destruct p; Simpl; Intuition.
Unfold cstore_update; Case (eq_adr_dec a a); Intuition.
Save.

Lemma pupdate_paccess_eq : 
  (s:cstore)(p1,p2:pointer)(v:T)
  (is_valid s p1) -> p1=p2 -> (paccess (pupdate s p1 v) p2) = v.
Proof.
Destruct p1; Destruct p2; Simpl; Intuition.
Discriminate H0.
Injection H0; Intros.
Unfold cstore_update; Subst a z; Case (eq_adr_dec a0 a0); Intuition.
Save.

Lemma pupdate_paccess_other : 
  (s:cstore)(p1,p2:pointer)(v:T)
  (is_valid s p1) -> (is_valid s p2) -> ~p1=p2 -> 
  (paccess (pupdate s p1 v) p2) = (paccess s p2).
Proof.
Destruct p1; Destruct p2; Simpl; Intuition.
Unfold cstore_update; Case (eq_adr_dec a0 a); Intuition.
Assert z=z0 \/ ~z=z0. Omega. Intuition.
Subst a0 z; Intuition.
Rewrite store_def_2; Subst a0; Intuition.
Save.

(* lemmas about [is_valid] *)

Lemma is_valid_update : 
  (s:cstore)(p1,p2:pointer)(v:T)
  (is_valid s p1) -> (is_valid (pupdate s p2 v) p1).
Proof.
Unfold is_valid; Destruct p1; Intuition.
Unfold pupdate; Case p2; Intuition.
Unfold cstore_update; Case (eq_adr_dec a a0); Intuition.
Subst a; WhyArrays; Trivial.
Save.

Hints Resolve is_valid_update.

End Stores.

(* Instanciations on integers and pointers *)

Definition int_store := (cstore Z).
Definition access_int : int_store -> pointer -> Z := (!paccess Z).
Definition update_int : int_store -> pointer -> Z -> int_store := (!pupdate Z).
Definition is_valid_int := (!is_valid Z).

Definition pointer_store := (cstore pointer).
Definition access_pointer : pointer_store -> pointer -> pointer := (!paccess pointer).
Definition update_pointer : pointer_store -> pointer -> pointer -> pointer_store := (!pupdate pointer).
Definition is_valid_pointer := (!is_valid pointer).
Definition is_valid_update_pointer : 
  (s:pointer_store)(p1,p2:pointer)(v:pointer)
  (is_valid_pointer s p1) -> (is_valid_pointer (update_pointer s p2 v) p1)
:= (!is_valid_update pointer).
Hints Resolve is_valid_update_pointer.

(* The set of allocated addresses *)

Definition allocated := adr -> bool.
