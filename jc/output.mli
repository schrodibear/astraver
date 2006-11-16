(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: output.mli,v 1.7 2006-11-16 10:09:36 hubert Exp $ i*)

type constant =
  | Prim_int of string
  | Prim_real of string
  | Prim_bool of bool
;;

type logic_type = 
    { logic_type_name : string;
      logic_type_args : logic_type list;
    }

val fprintf_logic_type : Format.formatter -> logic_type -> unit


type term = 
  | LConst of constant
  | LApp of string * term list
  | LVar of string
  | LVarAtLabel of string * string     (*r x@L *)
;;

val fprintf_term : Format.formatter -> term -> unit

type assertion = 
  | LTrue | LFalse
  | LAnd of assertion * assertion
  | LOr of assertion * assertion
  | LIff of assertion * assertion
  | LNot of assertion
  | LImpl of assertion * assertion
  | LIf of term * assertion * assertion
  | LLet of string * term * assertion
  | LForall of string * logic_type * assertion
      (*r forall x:t.a *)
  | LExists of string * logic_type * assertion
      (*r exists x:t.a *)
  | LPred of string * term list
  | LNamed of string * assertion
;;

val make_or : assertion -> assertion -> assertion
val make_and : assertion -> assertion -> assertion
val make_or_list : assertion list -> assertion
val make_and_list : assertion list -> assertion
val make_impl : assertion -> assertion -> assertion
val make_equiv : assertion -> assertion -> assertion

val fprintf_assertion : Format.formatter -> assertion -> unit

type why_type = 
  | Prod_type of string * why_type * why_type (*r (x:t1)->t2 *)
  | Base_type of logic_type
  | Ref_type of why_type
  | Annot_type of 
      assertion * why_type * 
      string list * string list * assertion * ((string * assertion) list)
	(*r { P } t reads r writes w raises E { Q | E => R } *)
;;

val int_type : why_type
val bool_type : why_type
val unit_type : why_type
val base_type : string -> why_type

type variant = term * string option

type opaque = bool

type expr =
  | Cte of constant
  | Var of string
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Void
  | Deref of string
  | If of expr * expr * expr
  | While of 
      expr (* loop condition *)
      * assertion (* invariant *) 
      * variant option (* variant *) 
      * expr list (* loop body *)
  | Block of expr list
  | Assign of string * expr
  | Let of string * expr * expr
  | Let_ref of string * expr * expr
  | App of expr * expr
  | Raise of string * expr option
  | Try of expr * string * string option * expr
  | Fun of (string * why_type) list * 
      assertion * expr * assertion * ((string * assertion) list)
  | Triple of opaque * 
      assertion * expr * assertion * ((string * assertion) list)
  | Assert of assertion * expr
  | Label of string * expr
  | BlackBox of why_type
  | Absurd 
;;

val make_or_expr : expr -> expr -> expr
val make_and_expr : expr -> expr -> expr


(*

  [make_app id [e1;..;en])] builds
  App(...(App(Var(id),e1),...,en)

*)

val make_app : string -> expr list -> expr
val make_app_e : expr -> expr list -> expr

(*

  [make_label l e] builds

    begin label l; e end

  applying simplification if [e] is already a block

    

*)
val make_label : string -> expr -> expr;;

(*

  [make_while cond inv dec e] builds

  while cond do { invariant inv variant dec } e

  applying simplifications if possible

*)
val make_while : expr -> assertion -> variant option -> expr -> expr;;

val make_pre : assertion -> expr -> expr;;

val append : expr -> expr -> expr

type why_decl =
  | Param of bool * string * why_type  (*r parameter in why *)
  | Def of string * expr               (*r global let in why *)
  | Logic of bool * string * (string * logic_type) list * logic_type  (*r logic decl in why *)
  | Axiom of string * assertion            (*r Axiom *)
  | Predicate of bool * string * (string * logic_type) list * assertion  
  | Function of bool * string * (string * logic_type) list * logic_type * term
  | Type of string * string list
  | Exception of string

val fprintf_why_decl : Format.formatter -> why_decl -> unit;;

val fprintf_why_decls : Format.formatter -> why_decl list -> unit



