(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ptree.mli,v 1.1 2002-07-08 09:02:28 filliatr Exp $ i*)

open Logic
open Types

(*s Parse trees. *)

(*s Logical expressions (for both terms and predicates) *)

type pp_infix = 
  PPand | PPor | PPimplies | 
  PPlt | PPle | PPgt | PPge | PPeq | PPneq |
  PPadd | PPsub | PPmul | PPdiv | PPmod

type pp_prefix = 
  PPneg | PPnot

type lexpr = 
  { pp_loc : Loc.t; pp_desc : pp_desc }

and pp_desc =
  | PPvar of Ident.t
  | PPapp of Ident.t * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of Ident.t * pure_type * lexpr

(*s Parsed types *)

type ptype_v =
  | PVref   of ptype_v
  | PVarray of lexpr * ptype_v   (* size x type *)
  | PVarrow of ptype_v binder list * ptype_c
  | PVpure  of pure_type

and ptype_c =
  { pc_result_name : Ident.t;
    pc_result_type : ptype_v;
    pc_effect : Effect.t;
    pc_pre    : lexpr pre list;
    pc_post   : lexpr post option }

(*s Parsed program. *)

type variable = Ident.t

type label = string

type variant = lexpr * variable

type t = 
  { pdesc : t_desc;
    pre : lexpr pre list;
    post : lexpr post option;
    loc : Loc.t }

and t_desc =
  | Svar of variable
  | Srefget of variable
  | Srefset of variable * t
  | Sarrget of bool * variable * t
  | Sarrset of bool * variable * t * t
  | Sseq of block
  | Swhile of t * lexpr asst option * variant * t
  | Sif of t * t * t
  | Slam of ptype_v binder list * t
  | Sapp of t * arg * ptype_c option
  | Sletref of variable * t * t
  | Sletin of variable * t * t
  | Srec of variable * ptype_v binder list * ptype_v * variant * t
  | Sraise of variable * t option * ptype_v option
  | Sexpression of term

and arg =
  | Sterm of t
  | Srefarg of variable
  | Stype of ptype_v

and block_st =
  | Slabel of label
  | Sassert of lexpr asst
  | Sstatement of t

and block = block_st list

type parsed_program = t

(*s Declarations. *)

type decl = 
  | Program of Ident.t * parsed_program
  | Parameter of Loc.t * Ident.t list * ptype_v
  | External of Loc.t * Ident.t list * ptype_v
  | Exception of Loc.t * Ident.t * pure_type option
  | Logic of Loc.t * Ident.t * logic_type
  | QPvs of string

