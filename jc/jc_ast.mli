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



type const =
  | JCCnull
  | JCCbool of bool
  | JCCinteger of string
  | JCCreal of string

type label = string

(***************)
(* parse trees *)
(***************)

type ptype = 
  | JCPTnative of native_type
  | JCPTidentifier of string
  | JCPTvalidpointer of string * int * int

type pbin_op =
  [ `Ble | `Bge | `Beq | `Bneq 
  | `Badd | `Bsub
  | `Bland | `Bimplies ]

type pexpr_node =
  | JCPEconst of const
  | JCPEvar of string
  | JCPEshift of pexpr * pexpr
  | JCPEderef of pexpr * string
  | JCPEapp of pexpr * pexpr list
  | JCPEassign of pexpr * pexpr
  | JCPEassign_op of pexpr * pbin_op * pexpr
  | JCPEbinary of pexpr * pbin_op * pexpr
  | JCPEforall of ptype * string * pexpr
  | JCPEold of pexpr

and pexpr =
    {
      jc_pexpr_node : pexpr_node;
      jc_pexpr_loc : Loc.position;
    }

     
type pclause =
  | JCPCrequires of pexpr
  | JCPCbehavior of string * pexpr option * pexpr


type pstatement_node =
  | JCPSskip
  | JCPSblock of pstatement list
  | JCPSexpr of pexpr
  | JCPSassert of pexpr
  | JCPSdecl of ptype * string * pexpr
  | JCPSif of pexpr * pstatement * pstatement
  | JCPSwhile of pexpr * pstatement
  | JCPSreturn of pexpr
  | JCPSbreak of label
  | JCPScontinue of label
  | JCPSgoto of label
  | JCPStry of pstatement * (string * string * pstatement) list * pstatement
  | JCPSthrow of string * pexpr

and pstatement = 
    {
      jc_pstatement_node : pstatement_node;
      jc_pstatement_loc : Loc.position;
    }


type pdecl_node =
  | JCPDfun of ptype * string * (ptype * string) list * pclause list * pstatement list
  | JCPDtype of string * (ptype * string) list

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

and term =
    {
      jc_term_node : term_node;
      jc_term_loc : Loc.position;
    }

type assertion_node =
  | JCAtrue
  | JCAand of assertion list
  | JCAimplies of assertion * assertion
  | JCAapp of logic_info * term list
  | JCAforall of var_info * assertion
  | JCAold of assertion

and assertion =
    {
      jc_assertion_node : assertion_node;
      jc_assertion_loc : Loc.position;
    }

type expr_node =
  | JCEconst of const
  | JCEvar of var_info
  | JCEshift of expr * expr
  | JCEderef of expr * field_info
  | JCEcall of fun_info * expr list
  | JCEassign_local of var_info * expr
  | JCEassign_heap of expr * field_info * expr
  | JCEassign_op_local of var_info * fun_info * expr
  | JCEassign_op_heap of expr * field_info * fun_info * expr

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
  | JCSskip
  | JCSblock of statement list
  | JCSexpr of expr
  | JCSassert of assertion
  | JCSdecl of var_info
  | JCSif of expr * statement * statement
  | JCSwhile of expr * loop_annot * statement
  | JCSreturn of expr
  | JCSbreak of label
  | JCScontinue of label
  | JCSgoto of label
  | JCStry of statement * (exception_info * var_info * statement) list * statement
  | JCSthrow of exception_info * expr

and statement = 
    {
      jc_statement_node : statement_node;
      jc_statement_loc : Loc.position;
    }


type behavior =
    { 
      jc_behavior_assigns : term option;
      jc_behavior_ensures : assertion;
    }

type fun_spec =
    {
      jc_fun_requires : assertion;
      jc_fun_behavior : (string * behavior) list;
    }



