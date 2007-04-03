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
  | JCCvoid
  | JCCnull
  | JCCboolean of bool
  | JCCinteger of string
  | JCCreal of string

type identifier = 
    { jc_identifier_loc : Loc.position;
      jc_identifier_name : string;
    }

type label = string


(***************)
(* parse trees *)
(***************)

type ptype_node = 
  | JCPTnative of native_type
  | JCPTidentifier of string
  | JCPTpointer of string * Num.num * Num.num

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
(*
  | JCPEshift of pexpr * pexpr
*)
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
  | JCPCbehavior of 
      string * identifier option * pexpr option * pexpr list option * pexpr


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
  | JCPStry of pstatement * (identifier * string * pstatement) list * pstatement
  | JCPSthrow of identifier * pexpr option
  | JCPSpack of pexpr
  | JCPSunpack of pexpr

and pstatement = 
    {
      jc_pstatement_node : pstatement_node;
      jc_pstatement_loc : Loc.position;
    }


type pdecl_node =
  | JCPDfun of 
      ptype * string * (ptype * string) list * pclause list * pstatement list
  | JCPDstructtype of string * 
      string option * (ptype * string) list * (string * string * pexpr) list
  | JCPDrectypes of pdecl list
  | JCPDrangetype of string * Num.num * Num.num
  | JCPDlogictype of string 
  | JCPDaxiom of string * pexpr
  | JCPDexception of string * ptype
  (* logic functions and predicates (return type: None if predicate) *)
  | JCPDlogic of ptype option * string * (ptype * string) list * pexpr

and pdecl =
    {
      jc_pdecl_node : pdecl_node;
      jc_pdecl_loc : Loc.position;
    }

(*************)
(* typed ast *)
(*************)

type tterm_node =
  | JCTTconst of const
  | JCTTvar of var_info
  | JCTTshift of tterm * tterm
  | JCTTderef of tterm * field_info
  | JCTTapp of logic_info * tterm list
  | JCTTold of tterm
  | JCTToffset_max of tterm * struct_info
  | JCTToffset_min of tterm * struct_info
  | JCTTinstanceof of tterm * struct_info
  | JCTTcast of tterm * struct_info
  | JCTTif of tterm * tterm * tterm

and tterm =
    {
      jc_tterm_node : tterm_node;
      jc_tterm_loc : Loc.position;
    }

type tlocation_set = 
  | JCTLSvar of var_info
  | JCTLSderef of tlocation_set * field_info
  | JCTLSrange of tlocation_set * tterm * tterm

type tlocation =
  | JCTLvar of var_info
  | JCTLderef of tlocation_set * field_info

type tassertion_node =
  | JCTAtrue
  | JCTAfalse
  | JCTAand of tassertion list
  | JCTAor of tassertion list
  | JCTAimplies of tassertion * tassertion
  | JCTAiff of tassertion * tassertion
  | JCTAnot of tassertion
  | JCTAapp of logic_info * tterm list
  | JCTAforall of var_info * tassertion
  | JCTAold of tassertion
  | JCTAinstanceof of tterm * struct_info
  | JCTAbool_term of tterm
  | JCTAif of tterm * tassertion * tassertion

and tassertion =
    {
      jc_tassertion_node : tassertion_node;
      jc_tassertion_loc : Loc.position;
    }

type tterm_or_tassertion =
  | JCTAssertion of tassertion
  | JCTTerm of tterm

type tincr_op = Prefix_inc | Prefix_dec | Postfix_inc | Postfix_dec

type texpr_node =
  | JCTEconst of const
  | JCTEvar of var_info
  | JCTEshift of texpr * texpr
  | JCTEderef of texpr * field_info
  | JCTEcall of fun_info * texpr list
  | JCTEinstanceof of texpr * struct_info
  | JCTEcast of texpr * struct_info
  | JCTEassign_local of var_info * texpr
  | JCTEassign_heap of texpr * field_info * texpr
  | JCTEassign_op_local of var_info * fun_info * texpr
  | JCTEassign_op_heap of texpr * field_info * fun_info * texpr
  | JCTEincr_local of tincr_op * var_info 
  | JCTEincr_heap of tincr_op * texpr * field_info 
  | JCTEif of texpr * texpr * texpr

and texpr =
    {
      jc_texpr_node : texpr_node;
      jc_texpr_type : jc_type;
      jc_texpr_loc : Loc.position;
    }

type tloop_annot =
    {
      jc_tloop_invariant : tassertion;
      jc_tloop_variant : tterm;
    }

type tstatement_node =
  | JCTSblock of tstatement list
  | JCTSexpr of texpr
  | JCTSassert of tassertion
  | JCTSdecl of var_info * texpr option * tstatement
  | JCTSif of texpr * tstatement * tstatement
  | JCTSwhile of texpr * tloop_annot * tstatement
  | JCTSreturn of texpr
  | JCTSbreak of label
  | JCTScontinue of label
  | JCTSgoto of label
  | JCTStry of 
      tstatement * (exception_info * var_info * tstatement) list * tstatement
  | JCTSthrow of exception_info * texpr option
  | JCTSpack of struct_info * texpr
  | JCTSunpack of struct_info * texpr

and tstatement = 
    {
      jc_tstatement_node : tstatement_node;
      jc_tstatement_loc : Loc.position;
    }


type tbehavior =
    { 
      jc_tbehavior_throws : exception_info option ;
      jc_tbehavior_assumes : tassertion option ;
      jc_tbehavior_assigns : tlocation list option ;
      jc_tbehavior_ensures : tassertion;
    }

type tfun_spec =
    {
      jc_tfun_requires : tassertion;
      jc_tfun_behavior : (string * tbehavior) list;
    }


(******************)
(* normalized ast *)
(******************)

type term_node =
  | JCTconst of const
  | JCTvar of var_info
  | JCTshift of term * term
  | JCTderef of term * field_info
  | JCTapp of logic_info * term list
  | JCTold of term
  | JCToffset_max of term * struct_info
  | JCToffset_min of term * struct_info
  | JCTinstanceof of term * struct_info
  | JCTcast of term * struct_info
  | JCTif of term * term * term

and term =
    {
      jc_term_node : term_node;
      jc_term_loc : Loc.position;
    }

type location_set = 
  | JCLSvar of var_info
  | JCLSderef of location_set * field_info
  | JCLSrange of location_set * term * term

type location =
  | JCLvar of var_info
  | JCLderef of location_set * field_info

type assertion_node =
  | JCAtrue
  | JCAfalse
  | JCAand of assertion list
  | JCAor of assertion list
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

(* application, increment and assignment are statements.
   special assignment with operation disappears.
 *)
type expr_node =
  | JCEconst of const
  | JCEvar of var_info
  | JCEshift of expr * expr
  | JCEderef of expr * field_info
  | JCEinstanceof of expr * struct_info
  | JCEcast of expr * struct_info
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

type incr_op = Stat_inc | Stat_dec

(* application, increment and assignment are statements. 
   expressions (without any of the above) are not statements anymore.
   break, continue, goto are translated with exceptions.
*)
type statement_node =
  | JCScall of var_info option * fun_info * expr list * statement
  | JCSincr_local of incr_op * var_info 
  | JCSincr_heap of incr_op * expr * field_info
  | JCSassign_local of var_info * expr
  | JCSassign_heap of expr * field_info * expr
  | JCSblock of statement list
  | JCSassert of assertion
  | JCSdecl of var_info * expr option * statement
  | JCSif of expr * statement * statement
  | JCSloop of loop_annot * statement
  | JCSreturn of expr
  | JCStry of statement 
      * (exception_info * var_info option * statement) list * statement
  | JCSthrow of exception_info * expr option
  | JCSpack of struct_info * expr
  | JCSunpack of struct_info * expr

and statement = 
    {
      jc_statement_node : statement_node;
      jc_statement_loc : Loc.position;
    }


type behavior =
    { 
      jc_behavior_throws : exception_info option ;
      jc_behavior_assumes : assertion option ;
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
