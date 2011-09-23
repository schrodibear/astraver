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



(*s Parse trees. *)

open Logic
open Types

type loc = Loc.position

(*s Logical expressions (for both terms and predicates) *)

type pp_infix = 
  PPand | PPor | PPimplies | PPiff |
  PPlt | PPle | PPgt | PPge | PPeq | PPneq |
  PPadd | PPsub | PPmul | PPdiv 

type pp_prefix = 
  PPneg | PPnot

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTvarid of Ident.t * Loc.position
  | PPTexternal of ppure_type list * Ident.t * Loc.position

type lexpr = 
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of Ident.t
  | PPapp of Ident.t * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of Ident.t * ppure_type * lexpr list list * lexpr
  | PPexists of Ident.t * ppure_type * lexpr
  | PPnamed of string * lexpr
  | PPlet of Ident.t * lexpr * lexpr
  | PPmatch of lexpr * ((Ident.t * Ident.t list * loc) * lexpr) list

type assertion = { 
  pa_name : Ident.name; 
  pa_value : lexpr; 
  pa_loc : Loc.position;
}

type postcondition = assertion * (Ident.t * assertion) list

(*s Parsed types *)

type peffect = { 
  pe_reads : Ident.t list;
  pe_writes : Ident.t list;
  pe_raises : Ident.t list
}

type ptype_v =
  | PVpure  of ppure_type
  | PVref   of ppure_type
  | PVarrow of ptype_v binder list * ptype_c

and ptype_c =
  { pc_result_name : Ident.t;
    pc_result_type : ptype_v;
    pc_effect : peffect;
    pc_pre    : assertion list;
    pc_post   : postcondition option }

(*s Parsed program. *)

type variable = Ident.t

type label = string

type variant = lexpr * variable

type exn_pattern = variable * variable option

type assert_kind = [`ASSERT | `CHECK]

type t = 
  { pdesc : t_desc;
    ploc : loc }

and t_desc =
  | Svar of variable
  | Sderef of variable
  | Sloop of assertion option * variant option * t
  | Sif of t * t * t
  | Slazy_and of t * t
  | Slazy_or of t * t
  | Snot of t
  | Sapp of t * t
  | Sletref of variable * t * t
  | Sletin of variable * t * t
  | Sseq of t * t
  | Slam of ptype_v binder list * assertion list * t
  | Srec of 
      variable * ptype_v binder list * ptype_v * variant option * 
	assertion list * t
  | Sraise of variable * t option * ptype_v option
  | Stry of t * (exn_pattern * t) list
  | Sconst of constant
  | Sabsurd of ptype_v option
  | Sany of ptype_c
  | Slabel of label * t
  | Sassert of assert_kind * assertion list * t
  | Spost of t * postcondition * transp

type parsed_program = t

(*s Declarations. *)

type external_ = bool

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type goal_kind = KLemma | KAxiom | KGoal

type decl = 
  | Include of loc * string
  | Program of loc * Ident.t * parsed_program
  | Parameter of loc * external_ * Ident.t list * ptype_v
  | Exception of loc * Ident.t * ppure_type option
  | Logic of loc * external_ * Ident.t list * plogic_type
  | Predicate_def of loc * Ident.t * (loc * Ident.t * ppure_type) list * lexpr
  | Inductive_def of loc * Ident.t * plogic_type * (loc * Ident.t * lexpr) list
  | Function_def 
      of loc * Ident.t * (loc * Ident.t * ppure_type) list * ppure_type * lexpr
  | Goal of loc * goal_kind * Ident.t * lexpr
  | TypeDecl of loc * external_ * Ident.t list * Ident.t
  | AlgType of (loc * Ident.t list * Ident.t
      * (loc * Ident.t * ppure_type list) list) list

type file = decl list
