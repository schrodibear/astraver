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

(* $Id: WhyCM.v,v 1.7 2003-10-27 09:43:10 filliatr Exp $ *)

Require Export WhyArrays.

(* A low level C model *)

Set Implicit Arguments.
Unset Strict Implicit.

(* Addresses *)

Parameter adr : Set.

Axiom eq_adr_dec : forall a1 a2:adr, {a1 = a2} + {a1 <> a2}.

Parameter dummy_adr : adr.

(* Pointers *)

Inductive pointer : Set :=
  | null : pointer
  | Ref : adr -> Z -> pointer.

Lemma eq_null_dec : forall p:pointer, {p = null} + {p <> null}.
Proof.
simple_destruct p; intuition.
right; intro H; discriminate H.
Qed.

(* Polymorphic Stores *)

Module Type AnySet.
  Parameter T : Set.
End AnySet.

Module Store (X: AnySet).

Definition cstore : Set := adr -> array X.T.

   Definition get (s:cstore) (p:pointer) : X.T :=
     match p with
     | null => access (s dummy_adr) 0
     | Ref a ofs => access (s a) ofs
     end.

  Definition cstore_update (s:cstore) (a:adr) (v:array X.T) : cstore :=
    fun a':adr =>
      match eq_adr_dec a' a with
      | left _ => v
      | right _ => s a'
      end.

  Definition set (s:cstore) (p:pointer) (v:X.T) : cstore :=
    match p with
    | null => s
    | Ref a ofs => cstore_update s a (store (s a) ofs v)
    end.

(* Pointer validity *)

Definition is_valid (s:cstore) (p:pointer) : Prop :=
  match p with
  | null => False
  | Ref a ofs => (0 <= ofs < array_length (s a))%Z
  end.

(* access/update lemmas *)

  Lemma cstore_update_same :
   forall (s:cstore) (a:adr) (v:array X.T), cstore_update s a v a = v.
Proof.
intros.
 unfold cstore_update; case (eq_adr_dec a a); intuition.
Qed.

  Lemma get_set_same :
   forall (s:cstore) (p:pointer) (v:X.T),
     is_valid s p -> get (set s p v) p = v.
Proof.
simple_destruct p; simpl; intuition.
unfold cstore_update; case (eq_adr_dec a a); intuition.
Qed.

  Lemma get_set_eq :
   forall (s:cstore) (p1 p2:pointer) (v:X.T),
     is_valid s p1 -> p1 = p2 -> get (set s p1 v) p2 = v.
Proof.
simple_destruct p1; simple_destruct p2; simpl; intuition.
discriminate H0.
injection H0; intros.
unfold cstore_update; subst a z; case (eq_adr_dec a0 a0); intuition.
Qed.

  Lemma get_set_other :
   forall (s:cstore) (p1 p2:pointer) (v:X.T),
     is_valid s p1 ->
     is_valid s p2 -> p1 <> p2 -> get (set s p1 v) p2 = get s p2.
Proof.
simple_destruct p1; simple_destruct p2; simpl; intuition.
unfold cstore_update; case (eq_adr_dec a0 a); intuition.
assert (z = z0 \/ z <> z0).
 omega.
 intuition.
subst a0 z; intuition.
rewrite store_def_2; subst a0; intuition.
Qed.

(* lemmas about [is_valid] *)

  Lemma is_valid_set :
   forall (s:cstore) (p1 p2:pointer) (v:X.T),
     is_valid s p1 -> is_valid (set s p2 v) p1.
Proof.
unfold is_valid; simple_destruct p1; intuition.
unfold set; case p2; intuition.
unfold cstore_update; case (eq_adr_dec a a0); intuition.
subst a; WhyArrays; trivial.
Qed.

Hint Resolve is_valid_set .

End Store.

(* Instanciations on integers and pointers *)

Module Int : AnySet with Definition T := Z.
  Definition T := Z.
End Int.
Module IntStore := Store Int.

Definition int_store := IntStore.cstore.
Definition get_int := IntStore.get.
Definition set_int := IntStore.set.
Definition is_valid_int := IntStore.is_valid.

Module Pointer : AnySet with Definition T := pointer.
  Definition T := pointer.
End Pointer.
Module PointerStore := Store Pointer.

Definition pointer_store := PointerStore.cstore.
Definition pget := PointerStore.get.
Definition pset := PointerStore.set.
Definition is_valid_pointer := PointerStore.is_valid.
Hint Unfold pget pset is_valid_pointer .

(* The set of allocated addresses *)

Definition allocated := adr -> bool.
