(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: clogic.mli,v 1.48 2005-06-16 07:30:33 filliatr Exp $ i*)

(* AST for C annotations *)

type logic_type = 
  | LTvoid
  | LTint
  | LTfloat
  | LTarray of logic_type
  | LTpointer of logic_type
  | LTvar of string

(* parsed terms and predicates *)

type constant = IntConstant of string | FloatConstant of string

type term_binop = Badd | Bsub | Bmul | Bdiv | Bmod
type term_unop = Uminus | Utilde | Ustar | Uamp | Ufloat_of_int | Uint_of_float

type 'ctype quantifiers = ('ctype * string) list
type 'ctype typed_quantifiers = ('ctype * Info.var_info) list

type relation = Lt | Gt | Le | Ge | Eq | Neq

type lexpr = {
  lexpr_node : lexpr_node;
  lexpr_loc : Loc.t
}

and lexpr_node = 
  (* both terms and predicates *)
  | PLvar of Info.var_info
  | PLapp of Info.logic_info * lexpr list
  (* terms *)
  | PLconstant of constant
  | PLunop of term_unop * lexpr
  | PLbinop of lexpr * term_binop * lexpr
  | PLdot of lexpr * string
  | PLarrow of lexpr * string
  | PLarrget of lexpr * lexpr
  | PLold of lexpr
  | PLat of lexpr * string
  | PLbase_addr of lexpr
  | PLblock_length of lexpr
  | PLresult
  | PLnull
  | PLcast of logic_type * lexpr
  | PLrange of lexpr * lexpr option * lexpr option
  (* predicates *)
  | PLfalse
  | PLtrue
  | PLrel of lexpr * relation * lexpr
  | PLand of lexpr * lexpr
  | PLor of lexpr * lexpr
  | PLimplies of lexpr * lexpr
  | PLiff of lexpr * lexpr
  | PLnot of lexpr
  | PLif of lexpr * lexpr * lexpr
  | PLforall of logic_type quantifiers * lexpr
  | PLexists of logic_type quantifiers * lexpr
  | PLvalid of lexpr
  | PLseparated of lexpr * lexpr
  | PLfullseparated of lexpr * lexpr
  | PLvalid_index of lexpr * lexpr
  | PLvalid_range of lexpr * lexpr * lexpr
  | PLfresh of lexpr
  | PLnamed of string * lexpr

(* typed terms *)

type 'ctype term = {
  term_node : 'ctype term_node;
  term_loc : Loc.t;
  term_type : 'ctype
}

and 'ctype term_node =
  | Tconstant of constant
  | Tvar of Info.var_info
  | Tapp of Info.logic_info * 'ctype term list
  | Tunop of term_unop * 'ctype term
  | Tbinop of 'ctype term * term_binop * 'ctype term
  | Tdot of 'ctype term * Info.var_info
  | Tarrow of 'ctype term * Info.var_info
  | Tarrget of 'ctype term * 'ctype term
  | Tif of 'ctype term * 'ctype term * 'ctype term
  | Told of 'ctype term
  | Tat of 'ctype term * string
  | Tbase_addr of 'ctype term
  | Tblock_length of 'ctype term
  | Tresult
  | Tnull
  | Tcast of 'ctype * 'ctype term
  | Trange of 'ctype term * 'ctype term option * 'ctype term option

(* typed predicates *)

type 'ctype predicate = {
  pred_node : 'ctype predicate_node;
  pred_loc : Loc.t;
}

and 'ctype predicate_node = 
  | Pfalse
  | Ptrue
  | Papp of Info.logic_info * 'ctype term list
  | Prel of 'ctype term * relation * 'ctype term
  | Pand of 'ctype predicate * 'ctype predicate
  | Por of 'ctype predicate * 'ctype predicate
  | Pimplies of 'ctype predicate * 'ctype predicate
  | Piff of 'ctype predicate * 'ctype predicate
  | Pnot of 'ctype predicate
  | Pif of 'ctype term * 'ctype predicate * 'ctype predicate
  | Pforall of 'ctype typed_quantifiers * 'ctype predicate
  | Pexists of 'ctype typed_quantifiers * 'ctype predicate
  | Pold of 'ctype predicate
  | Pat of 'ctype predicate * string
  | Pseparated of 'ctype term * 'ctype term  
  | Pfullseparated of 'ctype term * 'ctype term
  | Pvalid of 'ctype term 
  | Pvalid_index of 'ctype term * 'ctype term
  | Pvalid_range of 'ctype term * 'ctype term * 'ctype term
  | Pfresh of 'ctype term 
  | Pnamed of string * 'ctype predicate

type 'term location = 'term

type 'term variant = 'term * string option

type ('term,'pred) spec = { 
  mutable requires : 'pred option;
  mutable assigns : 'term location list option;    
  mutable ensures : 'pred option;
  mutable decreases : 'term variant option
}

type ('term,'pred) loop_annot = {
  invariant : 'pred option;
  loop_assigns : 'term location list option;
  variant : 'term variant option
}

type ('term,'ctype) logic_symbol =
  | Predicate_reads of (Info.var_info * 'ctype) list * 'term location list
  | Predicate_def of (Info.var_info * 'ctype) list * 'ctype predicate 
  | Function of (Info.var_info * 'ctype) list * 'ctype * 'term location list
  | Function_def of (Info.var_info * 'ctype) list * 'ctype * 'term

(*

normalized AST

*)

type 'ctype nterm = {
  nterm_node : 'ctype nterm_node;
  nterm_loc : Loc.t;
  nterm_type : 'ctype
}

and 'ctype nterm_node =
  | NTconstant of constant
  | NTvar of Info.var_info
  | NTapp of Info.logic_info * 'ctype nterm list
  | NTunop of term_unop * 'ctype nterm
  | NTstar of 'ctype nterm
  | NTbinop of 'ctype nterm * term_binop * 'ctype nterm
  | NTarrow of 'ctype nterm * Info.var_info
  | NTif of 'ctype nterm * 'ctype nterm * 'ctype nterm
  | NTold of 'ctype nterm
  | NTat of 'ctype nterm * string
  | NTbase_addr of 'ctype nterm
  | NTblock_length of 'ctype nterm
  | NTresult
  | NTnull
  | NTcast of 'ctype * 'ctype nterm
  | NTrange of 'ctype nterm * 'ctype nterm option * 'ctype nterm option

type 'ctype npredicate = {
  npred_node : 'ctype npredicate_node;
  npred_loc : Loc.t
}

and 'ctype npredicate_node =
  | NPfalse
  | NPtrue
  | NPapp of Info.logic_info * 'ctype nterm list
  | NPrel of 'ctype nterm * relation * 'ctype nterm
  | NPand of 'ctype npredicate * 'ctype npredicate
  | NPor of 'ctype npredicate * 'ctype npredicate
  | NPimplies of 'ctype npredicate * 'ctype npredicate
  | NPiff of 'ctype npredicate * 'ctype npredicate
  | NPnot of 'ctype npredicate
  | NPif of 'ctype nterm * 'ctype npredicate * 'ctype npredicate
  | NPforall of 'ctype typed_quantifiers * 'ctype npredicate
  | NPexists of 'ctype typed_quantifiers * 'ctype npredicate
  | NPold of 'ctype npredicate
  | NPat of 'ctype npredicate * string
  | NPvalid of 'ctype nterm 
  | NPvalid_index of 'ctype nterm * 'ctype nterm
  | NPvalid_range of 'ctype nterm * 'ctype nterm * 'ctype nterm
  | NPfresh of 'ctype nterm 
  | NPnamed of string * 'ctype npredicate

type ('term,'ctype) nlogic_symbol =
  | NPredicate_reads of (Info.var_info * 'ctype) list * 'term location list
  | NPredicate_def of (Info.var_info * 'ctype) list * 'ctype npredicate 
  | NFunction of (Info.var_info * 'ctype) list * 'ctype * 'term location list
  | NFunction_def of (Info.var_info * 'ctype) list * 'ctype * 'term


