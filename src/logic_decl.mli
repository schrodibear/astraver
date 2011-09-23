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



(*s Logical declarations. 
    This is what is sent to the various provers (see main.ml and the provers
    interfaces). *)

open Cc
open Logic

type loc = Loc.floc
type 'a scheme = 'a Env.scheme

type expl_kind = 
  | EKAbsurd
  | EKAssert
  | EKCheck
  | EKLoopInvInit of string
  | EKLoopInvPreserv of string
  | EKPost
  | EKPre of string
  | EKOther of string
  | EKVarDecr
  | EKWfRel 
  | EKLemma
      
type vc_expl =
    { lemma_or_fun_name : string;
      behavior : string;
      vc_loc : Loc.floc;
      vc_kind : expl_kind;
      vc_label : string option
    }

type obligation = Loc.floc * bool * vc_expl * string * sequent
    (* loc, is_lemma, explanation, id, sequent *) 

type t =
  | Dtype          of loc * Ident.t * string list
  | Dalgtype       of (loc * Ident.t * alg_type_def scheme) list
  | Dlogic         of loc * Ident.t * logic_type scheme
  | Dpredicate_def of loc * Ident.t * predicate_def scheme
  | Dinductive_def of loc * Ident.t * inductive_def scheme
  | Dfunction_def  of loc * Ident.t * function_def scheme
  | Daxiom         of loc * string * predicate scheme
  | Dgoal          of loc * bool * vc_expl * string * sequent scheme
      (* bool is true when goal is a lemma, that is it must be present
      in the context of the next goals *)
