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

type switch_label =
  | Case of const
  | Default


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
  | BPlt | BPgt | BPle | BPge | BPeq | BPneq 
  | BPadd | BPsub | BPmul | BPdiv | BPmod
  | BPland | BPlor | BPimplies | BPiff
  (* bitwise operators *)
  | BPbw_and | BPbw_or | BPbw_xor | BPshift_left | BPshift_right

type punary_op =
  | UPplus | UPminus | UPnot 
  | UPpostfix_inc | UPpostfix_dec | UPprefix_inc | UPprefix_dec
  (* bitwise operator *)
  | UPbw_not

type offset_kind = Offset_max | Offset_min

type pexpr_node =
  | JCPEconst of const
  | JCPEvar of string
  | JCPEderef of pexpr * string
  | JCPEapp of pexpr * pexpr list
  | JCPEassign of pexpr * pexpr
  | JCPEassign_op of pexpr * pbin_op * pexpr
  | JCPEbinary of pexpr * pbin_op * pexpr
  | JCPEunary of punary_op * pexpr
  | JCPEinstanceof of pexpr * string
  | JCPEcast of pexpr * string
  | JCPEforall of ptype * string list * pexpr
  | JCPEexists of ptype * string list * pexpr
  | JCPEold of pexpr
  | JCPEoffset of offset_kind * pexpr 
  | JCPEif of pexpr * pexpr * pexpr
  | JCPErange of pexpr * pexpr

and pexpr =
    {
      jc_pexpr_node : pexpr_node;
      jc_pexpr_loc : Loc.position;
    }

     
type pclause =
  | JCPCrequires of pexpr
  | JCPCbehavior of 
      string * identifier option * pexpr option * pexpr option 
      * pexpr list option * pexpr


type pstatement_node =
  | JCPSskip
  | JCPSblock of pstatement list
  | JCPSexpr of pexpr
  | JCPSassert of identifier option * pexpr
  | JCPSdecl of ptype * string * pexpr option
  | JCPSif of pexpr * pstatement * pstatement
  | JCPSwhile of pexpr * pexpr * pexpr * pstatement
      (*r condition, invariant, variant, body *)
  | JCPSfor of pexpr list * pexpr * pexpr list * pexpr * pexpr * pstatement
      (*r inits, condition, updates, invariant, variant, body *)
  | JCPSreturn of pexpr
  | JCPSbreak of label
  | JCPScontinue of label
  | JCPSgoto of label
  | JCPSlabel of label * pstatement
  | JCPStry of pstatement * (identifier * string * pstatement) list * pstatement
  | JCPSthrow of identifier * pexpr option
  | JCPSpack of pexpr
  | JCPSunpack of pexpr
  | JCPSswitch of pexpr * (switch_label * pstatement list) list

and pstatement = 
    {
      jc_pstatement_node : pstatement_node;
      jc_pstatement_loc : Loc.position;
    }

type preads_or_pexpr =
  | JCPReads of pexpr list
  | JCPExpr of pexpr

type pdecl_node =
  | JCPDvar of ptype * string * pexpr
  | JCPDfun of ptype * string * (ptype * string) list * pclause list
      * pstatement list option
  | JCPDstructtype of string * 
      string option * (ptype * string) list * (string * string * pexpr) list
  (* use to define recursively a set of types *)
  | JCPDrectypes of pdecl list
  (* use to define recursively a set of functions *)
  | JCPDrecfuns of pdecl list
  | JCPDenumtype of string * Num.num * Num.num
  | JCPDlogictype of string 
  | JCPDaxiom of string * pexpr
  | JCPDexception of string * ptype
  (* logic functions and predicates (return type: None if predicate) *)
  | JCPDlogic of ptype option * string * (ptype * string) list 
      * preads_or_pexpr
  (* global invariant *)
  | JCPDglobinv of string * pexpr

and pdecl =
    {
      jc_pdecl_node : pdecl_node;
      jc_pdecl_loc : Loc.position;
    }

(*************)
(* typed ast *)
(*************)

type bin_op =
  | Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
  | Blt_real | Bgt_real | Ble_real | Bge_real | Beq_real | Bneq_real 
  | Badd_int | Bsub_int | Bmul_int | Bdiv_int | Bmod_int
  | Badd_real | Bsub_real | Bmul_real | Bdiv_real
  | Bland | Blor | Bimplies | Biff
  | Beq_pointer | Bneq_pointer
  (* bitwise operators *)
  | Bbw_and | Bbw_or | Bbw_xor | Bshift_left | Bshift_right
  
type unary_op =
  | Uplus_int | Uminus_int | Uplus_real | Uminus_real | Unot 
  (* bitwise operator *)
  | Ubw_not

type tterm_node =
  | JCTTconst of const
  | JCTTvar of var_info
  | JCTTshift of tterm * tterm
  | JCTTderef of tterm * field_info
  | JCTTbinary of tterm * bin_op * tterm
  | JCTTunary of unary_op * tterm
  | JCTTapp of logic_info * tterm list
  | JCTTold of tterm
  | JCTToffset of offset_kind * tterm * struct_info 
  | JCTTinstanceof of tterm * struct_info
  | JCTTcast of tterm * struct_info
  | JCTTif of tterm * tterm * tterm
  | JCTTrange of tterm * tterm

and tterm =
    {
      jc_tterm_node : tterm_node;
      jc_tterm_type : jc_type;
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
  | JCTArelation of tterm * bin_op * tterm
  | JCTAand of tassertion list
  | JCTAor of tassertion list
  | JCTAimplies of tassertion * tassertion
  | JCTAiff of tassertion * tassertion
  | JCTAnot of tassertion
  | JCTAapp of logic_info * tterm list
  | JCTAforall of var_info * tassertion
  | JCTAexists of var_info * tassertion
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
  | JCTReads of tlocation list

type tincr_op = Prefix_inc | Prefix_dec | Postfix_inc | Postfix_dec

type texpr_node =
  | JCTEconst of const
  | JCTEvar of var_info
  | JCTEshift of texpr * texpr
  | JCTEderef of texpr * field_info
  | JCTEbinary of texpr * bin_op * texpr
  | JCTEunary of unary_op * texpr
  | JCTEcall of fun_info * texpr list
  | JCTEoffset of offset_kind * texpr * struct_info 
  | JCTEinstanceof of texpr * struct_info
  | JCTEcast of texpr * struct_info
  | JCTEassign_local of var_info * texpr
  | JCTEassign_local_op of var_info * bin_op * texpr
  | JCTEassign_heap of texpr * field_info * texpr
  | JCTEassign_heap_op of texpr * field_info * bin_op * texpr
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
  | JCTSassert of string option * tassertion
  | JCTSdecl of var_info * texpr option * tstatement
  | JCTSif of texpr * tstatement * tstatement
  | JCTSwhile of texpr * tloop_annot * tstatement
  | JCTSfor of texpr * texpr list * tloop_annot  * tstatement
      (*r condition, updates, loop annotations, body *)
      (*r inits must be given before using JCTSexpr or JCTSdecl *)
  | JCTSreturn of jc_type * texpr
  | JCTSbreak of label
  | JCTScontinue of label
  | JCTSgoto of label
  | JCTSlabel of label * tstatement
  | JCTStry of 
      tstatement * (exception_info * var_info * tstatement) list * tstatement
  | JCTSthrow of exception_info * texpr option
  | JCTSpack of struct_info * texpr
  | JCTSunpack of struct_info * texpr
  | JCTSswitch of texpr * (switch_label * tstatement list) list

and tstatement = 
    {
      jc_tstatement_node : tstatement_node;
      jc_tstatement_loc : Loc.position;
    }


type tbehavior =
    { 
      jc_tbehavior_throws : exception_info option ;
      jc_tbehavior_assumes : tassertion option ;
(*
      jc_tbehavior_requires : tassertion option ;
*)
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
  | JCTbinary of term * bin_op * term
  | JCTunary of unary_op * term
  | JCTshift of term * term
  | JCTderef of term * field_info
  | JCTapp of logic_info * term list
  | JCTold of term
  | JCToffset of offset_kind * term * struct_info
  | JCTinstanceof of term * struct_info
  | JCTcast of term * struct_info
  | JCTif of term * term * term
  | JCTrange of term * term

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
  | JCArelation of term * bin_op * term
  | JCAand of assertion list
  | JCAor of assertion list
  | JCAimplies of assertion * assertion
  | JCAiff of assertion * assertion
  | JCAnot of assertion
  | JCAapp of logic_info * term list
  | JCAforall of var_info * assertion
  | JCAexists of var_info * assertion
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
  | JCReads of location list

(* application, increment and assignment are statements.
   special assignment with operation disappears.
 *)
type expr_node =
  | JCEconst of const
  | JCEvar of var_info
  | JCEbinary of expr * bin_op * expr
  | JCEunary of unary_op * expr
  | JCEshift of expr * expr
  | JCEderef of expr * field_info
  | JCEinstanceof of expr * struct_info
  | JCEcast of expr * struct_info
  | JCEif of expr * expr * expr
  | JCEoffset of offset_kind * expr * struct_info
(*
  - enlever JCEif et le mettre au niveau des statements comme
      l'appel de fonction : A VOIR
*)

and expr =
   {
      jc_expr_node : expr_node;
      jc_expr_type : jc_type;
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
    (* instructions *)
  | JCScall of var_info option * fun_info * expr list * statement
  | JCSassign_local of var_info * expr
  | JCSassign_heap of expr * field_info * expr
      (* statements *)
  | JCSassert of string option * assertion
  | JCSblock of statement list
  | JCSdecl of var_info * expr option * statement
  | JCSif of expr * statement * statement
  | JCSloop of loop_annot * statement
  | JCSreturn of jc_type * expr
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
(*
      jc_behavior_requires : assertion option ;
*)
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
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
