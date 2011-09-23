(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



(*s Abstract syntax of imperative programs. *)

open Logic
open Types

type variable = Ident.t

type label = string

type variant = Loc.position * term * pure_type * variable

type exn_pattern = Ptree.exn_pattern

type assertion = { 
  a_name : Ident.t;
  a_value : predicate;
  a_loc : Loc.position;
  mutable a_proof : Cc.proof option;
}

type precondition = assertion

type postcondition = assertion * (Ident.t * assertion) list

type assert_kind = [ `ABSURD | `ASSERT | `PRE | `CHECK ]

(* ['a] is the type of information associated to the nodes. 
   It will be defined later in module [Env] *)
type 'a t = 
  { desc : 'a t_desc;
    info : 'a }

and 'a t_desc =
  | Expression of term (* pure terms including !x *)
  | Var of variable (* only for impure functions *)
  | Seq of 'a t * 'a t
  | Loop of assertion option * variant option * 'a t (* infinite loop *)
  | If of 'a t * 'a t * 'a t
  | LetRef of variable * 'a t * 'a t
  | LetIn of variable * 'a t * 'a t
  | Absurd
  (* assertion *)
  | Label of label * 'a t
  | Assertion of assert_kind * assertion list * 'a t
  | Post of 'a t * postcondition * transp
  (* exceptions *)
  | Raise of variable * 'a t option
  | Try of 'a t * (exn_pattern * 'a t) list 
  (* functions and applications *)
  | Lam of type_v binder list * precondition list * 'a t
  | Rec of variable * type_v binder list * type_v * variant option * 
      precondition list * 'a t
  | AppRef of 'a t * variable * 'a
  | AppTerm of 'a t * term * 'a
  (* undeterministic expression *)
  | Any of type_c

