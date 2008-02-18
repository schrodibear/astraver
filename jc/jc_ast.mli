(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
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

(* $Id: jc_ast.mli,v 1.119 2008-02-18 11:06:36 moy Exp $ *)

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

type real_conversion = Integer_to_real | Real_to_integer

type ppattern_node =
  | JCPPstruct of identifier * (identifier * ppattern) list
  | JCPPvar of identifier
  | JCPPor of ppattern * ppattern
  | JCPPas of ppattern * identifier
  | JCPPany
  | JCPPconst of const

and ppattern = {
  jc_ppattern_node: ppattern_node;
  jc_ppattern_loc: Loc.position;
}

type pexpr_node =
  | JCPElabel of string * pexpr
  | JCPEconst of const
  | JCPEvar of string
  | JCPEderef of pexpr * string
  | JCPEapp of string * logic_label list * pexpr list
  | JCPEassign of pexpr * pexpr
  | JCPEassign_op of pexpr * pbin_op * pexpr
  | JCPEbinary of pexpr * pbin_op * pexpr
  | JCPEunary of punary_op * pexpr
  | JCPEinstanceof of pexpr * string
  | JCPEcast of pexpr * string
  | JCPEquantifier of quantifier * ptype * string list * pexpr
  | JCPEold of pexpr
  | JCPEat of pexpr * logic_label
  | JCPEoffset of offset_kind * pexpr 
  | JCPEif of pexpr * pexpr * pexpr
  | JCPElet of string * pexpr * pexpr
  | JCPErange of pexpr option * pexpr option
  | JCPEalloc of pexpr * string
  | JCPEfree of pexpr
  | JCPEmutable of pexpr * ptag
  | JCPEtagequality of ptag * ptag
  | JCPEmatch of pexpr * (ppattern * pexpr) list

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
  | JCPSwhile of string * pexpr * pexpr * pexpr option * pstatement
      (*r label, condition, invariant, variant, body *)
  | JCPSfor of string * pexpr list * pexpr * pexpr list * pexpr 
      * pexpr option * pstatement
      (*r label, inits, condition, updates, invariant, variant, body *)
  | JCPSreturn of pexpr option
  | JCPSbreak of string
  | JCPScontinue of string
  | JCPSgoto of string
  | JCPSlabel of string * pstatement
  | JCPStry of pstatement * (identifier * string * pstatement) list * pstatement
  | JCPSthrow of identifier * pexpr option
  | JCPSpack of pexpr * identifier option
  | JCPSunpack of pexpr * identifier option
  | JCPSswitch of pexpr * (pexpr option list * pstatement list) list
  | JCPSmatch of pexpr * (ppattern * pstatement list) list

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
  | JCPDtag of string * string option * (bool * ptype * string) list
      * (identifier * string * pexpr) list
  | JCPDvarianttype of string * identifier list
(*  (* use to define recursively a set of types *)
  | JCPDrectypes of pdecl list*)
  (* use to define recursively a set of functions *)
  | JCPDrecfuns of pdecl list
  | JCPDenumtype of string * Num.num * Num.num
  | JCPDlogictype of string 
  | JCPDlemma of string * bool * logic_label list * pexpr
      (* 2nd arg is true if it is an axiom *)
  | JCPDexception of string * ptype
  (* logic functions and predicates (return type: None if predicate) *)
  | JCPDlogic of ptype option * string * logic_label list * (ptype * string) list 
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

type pattern_node =
  | JCPstruct of struct_info * (field_info * pattern) list
  | JCPvar of var_info
  | JCPor of pattern * pattern
  | JCPas of pattern * var_info
  | JCPany
  | JCPconst of const

and pattern = {
  jc_pattern_node: pattern_node;
  jc_pattern_loc: Loc.position;
  jc_pattern_type: jc_type;
}

type app = 
    {
      jc_app_fun : logic_info;
      jc_app_args : term list;
      mutable jc_app_region_assoc : (region * region) list;
      jc_app_label_assoc : (logic_label * logic_label) list;
    }

and term_node =
  | JCTconst of const
  | JCTvar of var_info
  | JCTshift of term * term
  | JCTsub_pointer of term * term
  | JCTderef of term * logic_label * field_info
  | JCTbinary of term * bin_op * term
  | JCTunary of unary_op * term
  | JCTapp of app
  | JCTold of term
  | JCTat of term * logic_label
  | JCToffset of offset_kind * term * struct_info 
  | JCTinstanceof of term * logic_label * struct_info
  | JCTcast of term * logic_label * struct_info
  | JCTrange_cast of term * logic_label * enum_info
  | JCTreal_cast of term * logic_label * real_conversion
  | JCTif of term * term * term
  | JCTrange of term option * term option
  | JCTmatch of term * (pattern * term) list

and term =
    {
      jc_term_node : term_node;
      jc_term_type : jc_type;
      jc_term_region : region;
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
  | JCLSderef of tlocation_set * logic_label * field_info * region
  | JCLSrange of tlocation_set * term option * term option

type tlocation =
  | JCLvar of var_info
  | JCLderef of tlocation_set * logic_label * field_info * region
  | JCLat of tlocation * logic_label

type assertion_node =
  | JCAtrue
  | JCAfalse
  | JCArelation of term * bin_op * term
  | JCAand of assertion list
  | JCAor of assertion list
  | JCAimplies of assertion * assertion
  | JCAiff of assertion * assertion
  | JCAnot of assertion
  | JCAapp of app
  | JCAquantifier of quantifier * var_info * assertion
  | JCAold of assertion
  | JCAat of assertion * logic_label
  | JCAinstanceof of term * logic_label * struct_info
  | JCAbool_term of term
  | JCAif of term * assertion * assertion
  | JCAmutable of term * struct_info * tag
  | JCAtagequality of tag * tag * string option
  | JCAmatch of term * (pattern * assertion) list
	
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
  | JCTErange_cast of texpr * enum_info
  | JCTEreal_cast of texpr * real_conversion
  | JCTEassign_var of var_info * texpr
  | JCTEassign_var_op of var_info * bin_op * texpr
  | JCTEassign_heap of texpr * field_info * texpr
  | JCTEassign_heap_op of texpr * field_info * bin_op * texpr
  | JCTEincr_local of tincr_op * var_info 
  | JCTEincr_heap of tincr_op * texpr * field_info 
  | JCTEif of texpr * texpr * texpr
  | JCTElet of var_info * texpr * texpr
  | JCTEalloc of texpr * struct_info
  | JCTEfree of texpr
  | JCTEmatch of texpr * (pattern * texpr) list

and texpr =
    {
      jc_texpr_node : texpr_node;
      jc_texpr_type : jc_type;
      jc_texpr_region : region;
      jc_texpr_label : string;
      jc_texpr_loc : Loc.position;
    }

type loop_annot =
    {
      jc_loop_tag : int;
      mutable jc_loop_invariant : assertion;
      mutable jc_free_loop_invariant : assertion;
      jc_loop_variant : term option;
    }

type tstatement_node =
  | JCTSblock of tstatement list
  | JCTSexpr of texpr
  | JCTSassert of (* string option * *) assertion
  | JCTSdecl of var_info * texpr option * tstatement
  | JCTSif of texpr * tstatement * tstatement
  | JCTSwhile of string * texpr * loop_annot * tstatement
  | JCTSfor of string * texpr * texpr list * loop_annot  * tstatement
      (*r condition, updates, loop annotations, body *)
      (*r inits must be given before using JCTSexpr or JCTSdecl *)
  | JCTSreturn_void 
  | JCTSreturn of jc_type * texpr
  | JCTSbreak of label_info
  | JCTScontinue of label_info
  | JCTSgoto of label_info
  | JCTSlabel of label_info * tstatement
  | JCTStry of tstatement 
      * (exception_info * var_info option * tstatement) list * tstatement
  | JCTSthrow of exception_info * texpr option
  | JCTSpack of struct_info * texpr * struct_info
  | JCTSunpack of struct_info * texpr * struct_info
  | JCTSswitch of texpr * (texpr option list * tstatement list) list
  | JCTSmatch of texpr * (pattern * tstatement list) list

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
      (* free precondition : used to prove the fun correctness, but not checked at call locations *)
      mutable jc_fun_free_requires : assertion; 
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
  | JCErange_cast of expr * enum_info
  | JCEreal_cast of expr * real_conversion
  | JCEif of expr * expr * expr
  | JCEoffset of offset_kind * expr * struct_info
  | JCEalloc of expr * struct_info
  | JCEfree of expr
      (*  | JCEmatch of expr * (pattern * expr) list*)
      (*
	- enlever JCEif et le mettre au niveau des statements comme
	l'appel de fonction : A VOIR
	Remarque : JCEif est toujours dans l'ast mais n'est jamais produit,
	on peut l'enlever ?
      *)
      
and expr =
    {
      jc_expr_node : expr_node;
      jc_expr_type : jc_type;
      jc_expr_region : region;
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

type call = 
    {
      jc_call_fun : fun_info;
      jc_call_args : expr list;
      mutable jc_call_region_assoc : (region * region) list;
    }

type statement_node =
    (* instructions *)
  | JCScall of var_info option * call * statement
  | JCSassign_var of var_info * expr
  | JCSassign_heap of expr * field_info * expr
    (* statements *)
  | JCSassert of (* string option * *) assertion
  | JCSblock of statement list
  | JCSdecl of var_info * expr option * statement
  | JCSif of expr * statement * statement
  | JCSloop of loop_annot * statement
  | JCSreturn_void 
  | JCSreturn of jc_type * expr (*r expected return type *) 
  | JCSlabel of label_info * statement
  | JCStry of statement 
      * (exception_info * var_info option * statement) list * statement
  | JCSthrow of exception_info * expr option
  | JCSpack of struct_info * expr * struct_info
  | JCSunpack of struct_info * expr * struct_info
  | JCSmatch of expr * (pattern * statement) list

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
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
