(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  Jessie2 fork:                                                         *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

open Lexing
open Format

type constant =
  | Prim_void
  | Prim_int of string
  | Prim_real of string
  | Prim_bool of bool

type logic_type = {
  lt_name : string;
  lt_args : logic_type list;
}

type vc_kind =
  | JCVCvar_decr
  | JCVCarith_overflow
  | JCVCdowncast
  | JCVCpointer_deref
  | JCVCpointer_deref_bounds
  | JCVCpointer_shift
  | JCVCseparation
  | JCVCindex_bounds
  | JCVCuser_call of string
  | JCVCdiv_by_zero
  | JCVCalloc_size
  | JCVCpack
  | JCVCunpack
  | JCVCfp_overflow
  | JCVCpre of string
  | JCVCassigns
  | JCVCallocates
  | JCVCensures
  | JCVCassertion of Position.t
  | JCVCcheck of string
  | JCVCpost
  | JCVCglobal_invariant of string
  | JCVCrequires

type why_label = {
  l_kind     : vc_kind option;
  l_behavior : string;
  l_pos      : Position.t
}

type term =
  | LConst of constant
  | LApp of string * term list
  | LVar of string  (** immutable logic var *)
  | LDeref of string (** [!r] *)
  | LDerefAtLabel of string * string  (** [(at !x L)] *)
  | TLabeled of why_label * term
  | TIf of term * term * term
  | TLet of string * term * term

type assertion =
  | LTrue | LFalse
  | LAnd of assertion * assertion
  | LOr of assertion * assertion
  | LIff of assertion * assertion
  | LNot of assertion
  | LImpl of assertion * assertion
  | LIf of term * assertion * assertion
  | LLet of string * term * assertion
  | LForall of string * logic_type * trigger list list * assertion (** [forall x : t. a] *)
  | LExists of string * logic_type * trigger list list * assertion (** [exists x : t. a] *)
  | LPred of string * term list
  | LLabeled of why_label * assertion

and trigger =
  | LPatP of assertion
  | LPatT of term

type why_type =
  | Prod_type of string * why_type * why_type (** (x : t1) -> t2 *)
  | Base_type of logic_type
  | Ref_type of why_type
  | Annot_type of
      assertion * why_type *
      string list * string list * assertion * ((string * assertion) list)
      (** [{ P } t reads r writes w raises E { Q | E => R }] *)

type variant = term * string option

type opaque = bool

type assert_kind = [ `ASSERT | `CHECK | `ASSUME ]

type expr_node =
  | Cte of constant
  | Var of string
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Void
  | Deref of string
  | If of expr * expr * expr
  | While of
        expr (** loop condition *)
      * assertion (** invariant *)
      * variant option (** variant *)
      * expr list (** loop body *)
  | Block of expr list
  | Assign of string * expr
  | Let of string * expr * expr
  | Let_ref of string * expr * expr
  | App of expr * expr * why_type option
  | Raise of string * expr option
  | Try of expr * string * string option * expr
  | Fun of (string * why_type) list * assertion * expr * assertion * bool * ((string * assertion) list)
           (** params * pre * body * post * diverges * signals *)
  | Triple of opaque * assertion * expr * assertion * ((string * assertion) list)
  | Assert of assert_kind * assertion * expr
  | BlackBox of why_type
  | Absurd
  | Labeled of why_label * expr

and expr = {
  expr_labels     : string list;
  expr_node       : expr_node;
}

type why_id = {
  why_name : string;
  why_expl : string;
  why_pos  : Position.t
}

type goal_kind = KAxiom | KLemma | KGoal

type why_decl =
  | Param of bool * why_id * why_type  (** parameter in why *)
  | Def of why_id * expr (** global let in why *)
  | Logic of bool * why_id * (string * logic_type) list * logic_type  (** logic decl in why *)
  | Predicate of bool * why_id * (string * logic_type) list * assertion
  | Inductive of bool * why_id * (string * logic_type) list * (string * assertion) list (** inductive definition *)
  | Goal of goal_kind * why_id * assertion  (** Goal *)
  | Function of bool * why_id * (string * logic_type) list * logic_type * term
  | Type of why_id * string list
  | Exception of why_id * logic_type option

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . jc_why_output_ast.mli"
  End:
*)
