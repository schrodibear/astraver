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

(* $Id: WhyArrays.v,v 1.3 2002-11-14 09:38:05 filliatr Exp $ *)

(**************************************)
(* Functional arrays, for use in Why. *)
(**************************************)

(* This is an axiomatization of arrays.
 *
 * The type (array N T) is the type of arrays ranging from 0 to N-1 
 * which elements are of type T.
 *
 * Arrays are created with new, accessed with access and modified with store. 
 *
 * Operations of accessing and storing are not guarded, but axioms are.
 * So these arrays can be viewed as arrays where accessing and storing
 * out of the bounds has no effect.
 *)


Require Export WhyInt.

Implicit Arguments On.


(* The type of arrays *)

Parameter array : Z -> Set -> Set.


(* Functions to create, access and modify arrays *)

Parameter new : (n:Z)(T:Set) T -> (array n T).

Parameter access : (n:Z)(T:Set) (array n T) -> Z -> T.

Parameter store : (n:Z)(T:Set) (array n T) -> Z -> T -> (array n T).


(* Axioms *)

Axiom new_def : (n:Z)(T:Set)(v0:T)
                (i:Z) `0<=i<n` -> (access (new n v0) i) = v0.

Axiom store_def_1 : (n:Z)(T:Set)(t:(array n T))(v:T)
                    (i:Z) `0<=i<n` ->
                    (access (store t i v) i) = v.

Axiom store_def_2 : (n:Z)(T:Set)(t:(array n T))(v:T)
                    (i:Z)(j:Z) `0<=i<n` -> `0<=j<n` ->
		    `i <> j` ->
                    (access (store t i v) j) = (access t j).

Hints Resolve new_def store_def_1 store_def_2 : datatypes v62.

(* A tactic to simplify access in arrays *)

Tactic Definition ArrayAccess i j H :=
    Elim (Z_eq_dec i j); [ 
      Intro H; Rewrite H; Rewrite store_def_1
    | Intro H; Rewrite store_def_2; [ Idtac | Idtac | Idtac | Exact H ] ].

(* Syntax and pretty-print for arrays *)

Grammar constr constr0 :=
  array_access
    [ "#" ident($t) "[" constr($c) "]" ] -> [ (access $t $c) ].

Syntax constr level 0 :
  array_access
    [ << (access ($VAR $t) $c) >> ] -> [ "#" $t "[" $c:L "]" ].
