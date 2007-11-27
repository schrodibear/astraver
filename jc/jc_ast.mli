(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
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

type label_info =
    { label_info_name : string;
      mutable times_used : int;
    }

(***************)
(* parse trees *)
(***************)

type ptype_node = 
  | JCPTnative of native_type
  | JCPTidentifier of string
  | JCPTpointer of string * Num.num option * Num.num option

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
  | BPbw_and | BPbw_or | BPbw_xor 
  | BPshift_left | BPlogical_shift_right | BParith_shift_right

type punary_op =
  | UPplus | UPminus | UPnot 
  | UPpostfix_inc | UPpostfix_dec | UPprefix_inc | UPprefix_dec
  (* bitwise operator *)
  | UPbw_not

type offset_kind = Offset_max | Offset_min

type quantifier = Forall | Exists

type pexpr_node =
  | JCPElabel of string * pexpr
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
  | JCPEquantifier of quantifier * ptype * string list * pexpr
  | JCPEold of pexpr
  | JCPEoffset of offset_kind * pexpr 
  | JCPEif of pexpr * pexpr * pexpr
  | JCPErange of pexpr option * pexpr option
  | JCPEalloc of pexpr * string
  | JCPEfree of pexpr
  | JCPEmutable of pexpr * ptag
  | JCPEtagequality of ptag * ptag

and pexpr =
    {
      jc_pexpr_node : pexpr_node;
      jc_pexpr_loc : Loc.position;
    }

and ptag_node =
  | JCPTtag of identifier
  | JCPTbottom
  | JCPTtypeof of pexpr

and ptag =
    {
      jc_ptag_node : ptag_node;
      jc_ptag_loc : Loc.position;
    }

     
type pclause =
  | JCPCrequires of pexpr
  | JCPCbehavior of Loc.position * string 
      * identifier option 
      * pexpr option 
      * pexpr option 
      * (Loc.position * pexpr list) option 
      * pexpr
      (*r loc, name, throws, assumes,requires,assigns,ensures *)


type pstatement_node =
  | JCPSskip
  | JCPSblock of pstatement list
  | JCPSexpr of pexpr
  | JCPSassert of (* identifier option * *) pexpr
  | JCPSdecl of ptype * string * pexpr option
  | JCPSif of pexpr * pstatement * pstatement
  | JCPSwhile of pexpr * pexpr * pexpr option * pstatement
      (*r condition, invariant, variant, body *)
  | JCPSfor of 
      pexpr list * pexpr * pexpr list * pexpr * pexpr option * pstatement
      (*r inits, condition, updates, invariant, variant, body *)
  | JCPSreturn of pexpr option
  | JCPSbreak of label
  | JCPScontinue of label
  | JCPSgoto of label
  | JCPSlabel of label * pstatement
  | JCPStry of pstatement * (identifier * string * pstatement) list * pstatement
  | JCPSthrow of identifier * pexpr option
  | JCPSpack of pexpr * identifier option
  | JCPSunpack of pexpr * identifier option
  | JCPSswitch of pexpr * (pexpr option list * pstatement list) list

and pstatement = 
    {
      jc_pstatement_node : pstatement_node;
      jc_pstatement_loc : Loc.position;
    }

type preads_or_pexpr =
  | JCPReads of pexpr list
  | JCPExpr of pexpr

type pdecl_node =
  | JCPDvar of ptype * string * pexpr option
  | JCPDfun of ptype * identifier * (ptype * string) list * pclause list
      * pstatement list option
  | JCPDstructtype of string * 
      string option * (bool * ptype * string) list * (string * string * pexpr) list
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
  | Beq_bool | Bneq_bool
  | Bland | Blor | Bimplies | Biff
  | Beq_pointer | Bneq_pointer
  (* bitwise operators *)
  | Bbw_and | Bbw_or | Bbw_xor 
  | Bshift_left | Blogical_shift_right | Barith_shift_right 
  
type unary_op =
  | Uplus_int | Uminus_int | Uplus_real | Uminus_real | Unot 
  (* bitwise operator *)
  | Ubw_not

type term_node =
  | JCTconst of const
  | JCTvar of var_info
  | JCTshift of term * term
  | JCTsub_pointer of term * term
  | JCTderef of term * field_info
  | JCTbinary of term * bin_op * term
  | JCTunary of unary_op * term
  | JCTapp of logic_info * term list
  | JCTold of term
  | JCToffset of offset_kind * term * struct_info 
  | JCTinstanceof of term * struct_info
  | JCTcast of term * struct_info
  | JCTif of term * term * term
  | JCTrange of term option * term option

and term =
    {
      jc_term_node : term_node;
      jc_term_type : jc_type;
      jc_term_loc : Loc.position;
      jc_term_label : string;
    }

type tag =
    {
      jc_tag_node : tag_node;
      jc_tag_loc : Loc.position;
    }

and tag_node =
  | JCTtag of struct_info
  | JCTbottom
  | JCTtypeof of term * struct_info

type tlocation_set = 
  | JCLSvar of var_info
  | JCLSderef of tlocation_set * field_info
  | JCLSrange of tlocation_set * term option * term option

type tlocation =
  | JCLvar of var_info
  | JCLderef of tlocation_set * field_info

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
  | JCAquantifier of quantifier * var_info * assertion
  | JCAold of assertion
  | JCAinstanceof of term * struct_info
  | JCAbool_term of term
  | JCAif of term * assertion * assertion
  | JCAmutable of term * struct_info * tag
  | JCAtagequality of tag * tag * string option
	
and assertion =
    {
     jc_assertion_node : assertion_node;
     jc_assertion_loc : Loc.position;
     jc_assertion_label : string;
   }
      
type term_or_assertion =
  | JCAssertion of assertion
  | JCTerm of term
  | JCReads of tlocation list

type tincr_op = Prefix_inc | Prefix_dec | Postfix_inc | Postfix_dec

type texpr_node =
  | JCTEconst of const
  | JCTEvar of var_info
  | JCTEshift of texpr * texpr
  | JCTEsub_pointer of texpr * texpr
  | JCTEderef of texpr * field_info
  | JCTEbinary of texpr * bin_op * texpr
  | JCTEunary of unary_op * texpr
  | JCTEcall of fun_info * texpr list
  | JCTEoffset of offset_kind * texpr * struct_info 
  | JCTEinstanceof of texpr * struct_info
  | JCTEcast of texpr * struct_info
  | JCTErange_cast of enum_info * texpr
  | JCTEassign_var of var_info * texpr
  | JCTEassign_var_op of var_info * bin_op * texpr
  | JCTEassign_heap of texpr * field_info * texpr
  | JCTEassign_heap_op of texpr * field_info * bin_op * texpr
  | JCTEincr_local of tincr_op * var_info 
  | JCTEincr_heap of tincr_op * texpr * field_info 
  | JCTEif of texpr * texpr * texpr
  | JCTEalloc of texpr * struct_info
  | JCTEfree of texpr

and texpr =
    {
      jc_texpr_node : texpr_node;
      jc_texpr_type : jc_type;
      jc_texpr_label : string;
      jc_texpr_loc : Loc.position;
    }

type loop_annot =
    {
      jc_loop_tag : int;
      mutable jc_loop_invariant : assertion;
      jc_loop_variant : term option;
    }

type tstatement_node =
  | JCTSblock of tstatement list
  | JCTSexpr of texpr
  | JCTSassert of (* string option * *) assertion
  | JCTSdecl of var_info * texpr option * tstatement
  | JCTSif of texpr * tstatement * tstatement
  | JCTSwhile of texpr * loop_annot * tstatement
  | JCTSfor of texpr * texpr list * loop_annot  * tstatement
      (*r condition, updates, loop annotations, body *)
      (*r inits must be given before using JCTSexpr or JCTSdecl *)
  | JCTSreturn_void 
  | JCTSreturn of jc_type * texpr
  | JCTSbreak of label
  | JCTScontinue of label
  | JCTSgoto of label
  | JCTSlabel of label * tstatement
  | JCTStry of tstatement 
      * (exception_info * var_info option * tstatement) list * tstatement
  | JCTSthrow of exception_info * texpr option
  | JCTSpack of struct_info * texpr * struct_info
  | JCTSunpack of struct_info * texpr * struct_info
  | JCTSswitch of texpr * (texpr option list * tstatement list) list

and tstatement = 
    {
      jc_tstatement_node : tstatement_node;
      jc_tstatement_loc : Loc.position;
    }


type behavior =
    { 
      jc_behavior_throws : exception_info option ;
      jc_behavior_assumes : assertion option ;
(*
      jc_behavior_requires : assertion option ;
*)
      jc_behavior_assigns : (Loc.position * tlocation list) option ;
      mutable jc_behavior_ensures : assertion;
    }

type fun_spec =
    {
      mutable jc_fun_requires : assertion;
      mutable jc_fun_behavior : (Loc.position * string * behavior) list;
    }


(******************)
(* normalized ast *)
(******************)


(* application, increment and assignment are statements.
   special assignment with operation disappears.
 *)
type expr_node =
  | JCEconst of const
  | JCEvar of var_info
  | JCEbinary of expr * bin_op * expr
  | JCEunary of unary_op * expr
  | JCEshift of expr * expr
  | JCEsub_pointer of expr * expr
  | JCEderef of expr * field_info
  | JCEinstanceof of expr * struct_info
  | JCEcast of expr * struct_info
  | JCErange_cast of enum_info * expr
  | JCEif of expr * expr * expr
  | JCEoffset of offset_kind * expr * struct_info
  | JCEalloc of expr * struct_info
  | JCEfree of expr
(*
  - enlever JCEif et le mettre au niveau des statements comme
      l'appel de fonction : A VOIR
*)

and expr =
    {
      jc_expr_node : expr_node;
      jc_expr_type : jc_type;
      jc_expr_label : string;
      jc_expr_loc : Loc.position;
    }

(*
type loop_annot =
    {
      jc_loop_invariant : assertion;
      jc_loop_variant : term;
    }
*)

type incr_op = Stat_inc | Stat_dec

(* application, increment and assignment are statements. 
   expressions (without any of the above) are not statements anymore.
   break, continue, goto are translated with exceptions.
*)

type statement_node =
    (* instructions *)
  | JCScall of var_info option * fun_info * expr list * statement
  | JCSassign_var of var_info * expr
  | JCSassign_heap of expr * field_info * expr
    (* statements *)
  | JCSassert of (* string option * *) assertion
  | JCSblock of statement list
  | JCSdecl of var_info * expr option * statement
  | JCSif of expr * statement * statement
  | JCSloop of loop_annot * statement
  | JCSreturn_void 
  | JCSreturn of jc_type * expr
  | JCStry of statement 
      * (exception_info * var_info option * statement) list * statement
  | JCSthrow of exception_info * expr option
  | JCSpack of struct_info * expr * struct_info
  | JCSunpack of struct_info * expr * struct_info

and statement = 
    {
      jc_statement_node : statement_node;
      jc_statement_label : string;
      jc_statement_loc : Loc.position;
    }


(*
type behavior =
    {  
      jc_behavior_throws : exception_info option ;
      jc_behavior_assumes : assertion option ;
(*
      jc_behavior_requires : assertion option ;
*)
      jc_behavior_assigns : tlocation list option ;
      jc_behavior_ensures : assertion;
    }
*)

(*
type fun_spec =
    {
      jc_fun_requires : assertion;
      jc_fun_behavior : (string * behavior) list;
    }
*)


    
(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
