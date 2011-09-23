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


val inductive_inverse_body : 
    Ident.t ->  (* predicate name *)
    (Ident.t * Logic.pure_type) list -> (* binders *)
    (Ident.t * Logic.predicate) list -> (* inductive cases *) 
      Logic.predicate (* predicate body *)

val function_def :
  Logic_decl.loc -> Ident.t -> Logic.function_def Env.scheme
  -> Logic_decl.t list

val predicate_def :
  Logic_decl.loc -> Ident.t -> Logic.predicate_def Env.scheme
  -> Logic_decl.t list

val inductive_def : 
  Logic_decl.loc -> Ident.t -> Logic.inductive_def Env.scheme 
  -> Logic_decl.t list

val algebraic_type :
  (Logic_decl.loc * Ident.t * Logic.alg_type_def Env.scheme) list
  -> Logic_decl.t list

val push: recursive_expand:bool -> Logic_decl.t -> Logic_decl.t

