(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
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


open Jc_env
open Jc_fenv



type const =
  | JCCnull
  | JCCboolean of bool
  | JCCinteger of string
  | JCCreal of string

type label = string

(***************)
(* parse trees *)
(***************)

type ptype_node = 
  | JCPTnative of native_type
  | JCPTidentifier of string
  | JCPTpointer of string * int * int

and ptype =
    {
      jc_ptype_loc : Loc.position;
      jc_ptype_node : ptype_node;
    }

type pbin_op =
  | Blt | Bgt | Ble | Bge | Beq | Bneq 
  | Badd | Bsub | Bmul | Bdiv | Bmod
  | Bland | Blor | Bimplies | Biff
  

type punary_op =
  | Uplus | Uminus | Unot 
  | Upostfix_inc | Upostfix_dec | Uprefix_inc | Uprefix_dec


type pexpr_node =
  | JCPEconst of const
  | JCPEvar of string
  | JCPEshift of pexpr * pexpr
  | JCPEderef of pexpr * string
  | JCPEapp of pexpr * pexpr list
  | JCPEassign of pexpr * pexpr
  | JCPEassign_op of pexpr * pbin_op * pexpr
  | JCPEbinary of pexpr * pbin_op * pexpr
  | JCPEunary of punary_op * pexpr
  | JCPEinstanceof of pexpr * string
  | JCPEcast of pexpr * string
  | JCPEforall of ptype * string list * pexpr
  | JCPEold of pexpr
  | JCPEoffset_max of pexpr
  | JCPEoffset_min of pexpr
  | JCPEif of pexpr * pexpr * pexpr

and pexpr =
    {
      jc_pexpr_node : pexpr_node;
      jc_pexpr_loc : Loc.position;
    }

     
type pclause =
  | JCPCrequires of pexpr
  | JCPCbehavior of string * pexpr list option * pexpr


type pstatement_node =
  | JCPSskip
  | JCPSblock of pstatement list
  | JCPSexpr of pexpr
  | JCPSassert of pexpr
  | JCPSdecl of ptype * string * pexpr option
  | JCPSif of pexpr * pstatement * pstatement
  | JCPSwhile of pexpr * pexpr * pexpr * pstatement
  | JCPSreturn of pexpr
  | JCPSbreak of label
  | JCPScontinue of label
  | JCPSgoto of label
  | JCPStry of pstatement * (string * string * pstatement) list * pstatement
  | JCPSthrow of string * pexpr
  | JCPSpack of pexpr
  | JCPSunpack of pexpr

and pstatement = 
    {
      jc_pstatement_node : pstatement_node;
      jc_pstatement_loc : Loc.position;
    }


type pdecl_node =
  | JCPDfun of ptype * string * (ptype * string) list * pclause list * pstatement list
  | JCPDtype of string * string option * (ptype * string) list * (string * string * pexpr) list
  | JCPDaxiom of string * pexpr

and pdecl =
    {
      jc_pdecl_node : pdecl_node;
      jc_pdecl_loc : Loc.position;
    }

(*************)
(* typed ast *)
(*************)

type term_node =
  | JCTconst of const
  | JCTvar of var_info
  | JCTshift of term * term
  | JCTderef of term * field_info
  | JCTapp of logic_info * term list
  | JCTold of term
  | JCToffset_max of term
  | JCToffset_min of term
  | JCTinstanceof of term * struct_info
  | JCTcast of term * struct_info
  | JCTif of term * term * term

and term =
    {
      jc_term_node : term_node;
      jc_term_loc : Loc.position;
    }

type assertion_node =
  | JCAtrue
  | JCAfalse
  | JCAand of assertion list
  | JCAimplies of assertion * assertion
  | JCAiff of assertion * assertion
  | JCAnot of assertion
  | JCAapp of logic_info * term list
  | JCAforall of var_info * assertion
  | JCAold of assertion
  | JCAinstanceof of term * struct_info
  | JCAbool_term of term
  | JCAif of term * assertion * assertion

and assertion =
    {
      jc_assertion_node : assertion_node;
      jc_assertion_loc : Loc.position;
    }

type term_or_assertion =
  | JCAssertion of assertion
  | JCTerm of term

type incr_op = Prefix_inc | Prefix_dec | Postfix_inc | Postfix_dec

type expr_node =
  | JCEconst of const
  | JCEvar of var_info
  | JCEshift of expr * expr
  | JCEderef of expr * field_info
  | JCEcall of fun_info * expr list
  | JCEinstanceof of expr * struct_info
  | JCEcast of expr * struct_info
  | JCEassign_local of var_info * expr
  | JCEassign_heap of expr * field_info * expr
  | JCEassign_op_local of var_info * fun_info * expr
  | JCEassign_op_heap of expr * field_info * fun_info * expr
  | JCEincr_local of incr_op * var_info 
  | JCEincr_heap of incr_op * field_info * expr
  | JCEif of expr * expr * expr

and expr =
   {
      jc_expr_node : expr_node;
      jc_expr_loc : Loc.position;
    }

type loop_annot =
    {
      jc_loop_invariant : assertion;
      jc_loop_variant : term;
    }

type statement_node =
  | JCSblock of statement list
  | JCSexpr of expr
  | JCSassert of assertion
  | JCSdecl of var_info * expr option * statement
  | JCSif of expr * statement * statement
  | JCSwhile of expr * loop_annot * statement
  | JCSreturn of expr
  | JCSbreak of label
  | JCScontinue of label
  | JCSgoto of label
  | JCStry of statement * (exception_info * var_info * statement) list * statement
  | JCSthrow of exception_info * expr
  | JCSpack of struct_info * expr
  | JCSunpack of struct_info * expr

and statement = 
    {
      jc_statement_node : statement_node;
      jc_statement_loc : Loc.position;
    }


type location =
  | JCLvar of var_info
  | JCLderef of location * field_info

type behavior =
    { 
      jc_behavior_assigns : location list option ;
      jc_behavior_ensures : assertion;
    }

type fun_spec =
    {
      jc_fun_requires : assertion;
      jc_fun_behavior : (string * behavior) list;
    }



    
(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
