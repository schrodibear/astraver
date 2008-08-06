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

(* $Id: jc_ast.mli,v 1.142 2008-08-06 22:59:00 moy Exp $ *)

open Jc_env
open Jc_fenv
open Jc_region

class type positioned =
object
  method pos: Loc.position
end

class type typed =
object
  method typ: jc_type
end

class type labeled =
object
  method label: label option
  method set_label: label option -> unit
end

class type marked =
object
  method mark: string
end

class type regioned =
object
  method region: region
  method set_region: region -> unit
end

type const =
  | JCCvoid
  | JCCnull
  | JCCboolean of bool
  | JCCinteger of string
  | JCCreal of string
  | JCCstring of string

class type identifier = 
object
  inherit positioned
  method name: string
end

class type ['a] node_positioned = 
object
  inherit positioned
  method node: 'a
end

(***************)
(* parse trees *)
(***************)

type ptype_node = 
  | JCPTnative of native_type
  | JCPTidentifier of string
  | JCPTpointer of string * ptype list * Num.num option * Num.num option

and ptype = ptype_node node_positioned

type comparison_op = [ `Blt | `Bgt | `Ble | `Bge | `Beq | `Bneq ]
type arithmetic_op = [ `Badd | `Bsub | `Bmul | `Bdiv | `Bmod ]
type logical_op = [ `Bland | `Blor | `Bimplies | `Biff ]
type bitwise_op = 
    [ `Bbw_and | `Bbw_or | `Bbw_xor 
    | `Bshift_left | `Blogical_shift_right | `Barith_shift_right ]

type operational_op = [ comparison_op | arithmetic_op | bitwise_op | `Bconcat | `Bland | `Blor ]
type bin_op = [ operational_op | logical_op ]
      
type pre_unary_op = [ `Uprefix_inc | `Uprefix_dec ]
type post_unary_op = [ `Upostfix_inc | `Upostfix_dec ]
type pm_unary_op = [ pre_unary_op | post_unary_op | `Uplus ]
type unary_op = [ `Uminus | `Unot | `Ubw_not ]

type pexpr_unary_op = [ pm_unary_op | unary_op ]

type native_operator_type = [ `Unit | `Boolean | `Integer | `Real ]
type operator_type = [ native_operator_type | `Pointer | `Logic ]

type pred_bin_op = [comparison_op | logical_op] * operator_type
type expr_unary_op = unary_op * native_operator_type
type term_unary_op = expr_unary_op
type expr_bin_op = operational_op * operator_type
type term_bin_op = bin_op * operator_type
type pred_rel_op = comparison_op * operator_type

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

and ppattern = ppattern_node node_positioned

type 'expr pbehavior = 
    Loc.position * string * identifier option * 'expr option 
    * 'expr option * (Loc.position * 'expr list) option * 'expr
      (*r loc, name, throws, assumes,requires,assigns,ensures *)
 
and pexpr_node =
  | JCPEconst of const
  | JCPElabel of string * pexpr
  | JCPEvar of string
  | JCPEderef of pexpr * string
  | JCPEbinary of pexpr * bin_op * pexpr
  | JCPEunary of pexpr_unary_op * pexpr
  | JCPEapp of string * label list * pexpr list
  | JCPEassign of pexpr * pexpr
  | JCPEassign_op of pexpr * bin_op * pexpr
  | JCPEinstanceof of pexpr * string
  | JCPEcast of pexpr * string
  | JCPEquantifier of quantifier * ptype * string list * pexpr
  | JCPEold of pexpr
  | JCPEat of pexpr * label
  | JCPEoffset of offset_kind * pexpr 
  | JCPEaddress of pexpr 
  | JCPEif of pexpr * pexpr * pexpr
  | JCPElet of ptype option * string * pexpr option * pexpr
  | JCPEdecl of ptype * string * pexpr option
  | JCPErange of pexpr option * pexpr option
  | JCPEalloc of pexpr * string
  | JCPEfree of pexpr
  | JCPEmutable of pexpr * pexpr ptag
  | JCPEeqtype of pexpr ptag * pexpr ptag
  | JCPEsubtype of pexpr ptag * pexpr ptag
  | JCPEmatch of pexpr * (ppattern * pexpr) list
(*  | JCPSskip *) (* -> JCPEconst JCCvoid *)
  | JCPEblock of pexpr list
  | JCPEassert of string list * pexpr
  | JCPEcontract of 
      pexpr option * pexpr option * pexpr pbehavior list * pexpr 
	(* requires, decreases, behaviors, expression *)
  | JCPEwhile of 
      pexpr * (string list * pexpr) list * pexpr option * pexpr
	(*r condition, invariant, variant, body *)
  | JCPEfor of 
      pexpr list * pexpr * pexpr list * pexpr * pexpr option * pexpr
	(*r inits, condition, updates, invariant, variant, body *)
  | JCPEreturn of pexpr
  | JCPEbreak of string
  | JCPEcontinue of string
  | JCPEgoto of string
  | JCPEtry of pexpr * (identifier * string * pexpr) list * pexpr
  | JCPEthrow of identifier * pexpr
  | JCPEpack of pexpr * identifier option
  | JCPEunpack of pexpr * identifier option
  | JCPEswitch of pexpr * (pexpr option list * pexpr) list

and pexpr = pexpr_node node_positioned

and 'a ptag_node =
  | JCPTtag of identifier
  | JCPTbottom
  | JCPTtypeof of 'a

and 'a ptag = 'a ptag_node node_positioned

type 'expr clause =
  | JCCrequires of 'expr
  | JCCbehavior of 'expr pbehavior

type 'expr reads_or_expr =
  | JCreads of 'expr list
  | JCexpr of 'expr

type 'expr decl_node =
  | JCDvar of ptype * string * 'expr option
  | JCDfun of ptype * identifier * (ptype * string) list * 'expr clause list
      * 'expr option
  | JCDtag of
      string (* name of the tag *)
      * string list (* type parameters *)
      * (string * ptype list) option (* parent tag, applied type parameters *)
      * (bool * ptype * string * int option) list (* fields *)
      * (identifier * string * 'expr) list (* invariants *)
  | JCDvariant_type of string * identifier list
  | JCDunion_type of string * identifier list
  | JCDenum_type of string * Num.num * Num.num
  | JCDlogic_type of string 
  | JCDlemma of string * bool * label list * 'expr
      (* 2nd arg is true if it is an axiom *)
  | JCDexception of string * ptype option
  (* logic functions and predicates (return type: None if predicate) *)
  | JCDlogic of ptype option * string * label list * (ptype * string) list 
      * 'expr reads_or_expr
  | JCDlogic_var of ptype * string * 'expr option
  (* global invariant *)
  | JCDglobal_inv of string * 'expr
  (* "pragma" options and policies *)
  | JCDinvariant_policy of Jc_env.inv_sem
  | JCDseparation_policy of Jc_env.separation_sem
  | JCDannotation_policy of Jc_env.annotation_sem
  | JCDabstract_domain of Jc_env.abstract_domain 
  | JCDint_model of Jc_env.int_model

and 'expr decl = 'expr decl_node node_positioned

type pdecl = pexpr decl

class type ['expr_node] c_nexpr =
object
  inherit labeled
  inherit ['expr_node] node_positioned
end

(** Normalized expressions. Not typed yet, but without gotos. *)
type nexpr_node =
  | JCNEconst of const
  | JCNElabel of string * nexpr
  | JCNEvar of string
  | JCNEderef of nexpr * string
  | JCNEbinary of nexpr * bin_op * nexpr
  | JCNEunary of unary_op * nexpr
  | JCNEapp of string * label list * nexpr list
  | JCNEassign of nexpr * nexpr
  | JCNEinstanceof of nexpr * string
  | JCNEcast of nexpr * string
  | JCNEif of nexpr * nexpr * nexpr
  | JCNEoffset of offset_kind * nexpr 
  | JCNEaddress of nexpr 
  | JCNEalloc of nexpr * string
  | JCNEfree of nexpr
  | JCNElet of ptype option * string * nexpr option * nexpr
  | JCNEassert of string list * nexpr
  | JCNEcontract of 
      nexpr option * nexpr option * nexpr pbehavior list * nexpr 
	(* requires, decreases, behaviors, expression *)
  | JCNEblock of nexpr list
  | JCNEloop of (string list * nexpr) list * nexpr option * nexpr
      (*r invariant, variant, body *)
  | JCNEreturn of nexpr option
  | JCNEtry of nexpr * (identifier * string * nexpr) list * nexpr
  | JCNEthrow of identifier * nexpr option
  | JCNEpack of nexpr * identifier option
  | JCNEunpack of nexpr * identifier option
  | JCNEmatch of nexpr * (ppattern * nexpr) list
  (* Assertions only *)
  | JCNEquantifier of quantifier * ptype * string list * nexpr
  | JCNEold of nexpr
  | JCNEat of nexpr * label
  | JCNEmutable of nexpr * nexpr ptag
  | JCNEeqtype of nexpr ptag * nexpr ptag
  | JCNEsubtype of nexpr ptag * nexpr ptag
  (* Locations only *)
  | JCNErange of nexpr option * nexpr option

and nexpr = nexpr_node c_nexpr

     
(*************)
(* typed ast *)
(*************)

class type ['pattern_node] c_pattern =
object
  inherit typed
  inherit ['pattern_node] node_positioned
end

type pattern_node =
  | JCPstruct of struct_info * (field_info * pattern) list
  | JCPvar of var_info
  | JCPor of pattern * pattern
  | JCPas of pattern * var_info
  | JCPany
  | JCPconst of const

and pattern = pattern_node c_pattern

class type ['node] c_term =
object
  inherit typed
  inherit regioned
  inherit marked
  inherit labeled
  inherit ['node] node_positioned
end

type app = 
    {
      jc_app_fun : logic_info;
      jc_app_args : term list;
      mutable jc_app_region_assoc : (region * region) list;
      jc_app_label_assoc : (label * label) list;
    }

and term_node =
  | JCTconst of const
  | JCTvar of var_info
  | JCTshift of term * term
  | JCTderef of term * label * field_info
  | JCTbinary of term * term_bin_op * term
  | JCTunary of term_unary_op * term
  | JCTapp of app
  | JCTold of term
  | JCTat of term * label
  | JCToffset of offset_kind * term * struct_info 
  | JCTaddress of term
  | JCTinstanceof of term * label * struct_info
  | JCTcast of term * label * struct_info
  | JCTbitwise_cast of term * label * struct_info
  | JCTrange_cast of term * enum_info
  | JCTreal_cast of term * real_conversion
  | JCTif of term * term * term
  | JCTrange of term option * term option
  | JCTmatch of term * (pattern * term) list

and term = term_node c_term

type tag = tag_node node_positioned

and tag_node =
  | JCTtag of struct_info
  | JCTbottom
  | JCTtypeof of term * struct_info

class type ['node] c_location =
object
  inherit regioned
  inherit labeled
  inherit ['node] node_positioned
end

type location_set_node = 
  | JCLSvar of var_info
  | JCLSderef of location_set * label * field_info * region
(* TODO ?
  | JCLSshift of location_set * term 
*)
  | JCLSrange of location_set * term option * term option

and location_node =
  | JCLvar of var_info
  | JCLderef of location_set * label * field_info * region
  | JCLat of location * label

and location_set = location_set_node c_location

and location = location_node c_location

class type ['assertion_node] c_assertion =
object
  inherit marked
  inherit labeled
  inherit ['assertion_node] node_positioned
end

type assertion_node =
  | JCAtrue
  | JCAfalse
  | JCArelation of term * pred_rel_op * term
  | JCAand of assertion list
  | JCAor of assertion list
  | JCAimplies of assertion * assertion
  | JCAiff of assertion * assertion
  | JCAnot of assertion
  | JCAapp of app
  | JCAquantifier of quantifier * var_info * assertion
  | JCAold of assertion
  | JCAat of assertion * label
  | JCAinstanceof of term * label * struct_info
  | JCAbool_term of term
  | JCAif of term * assertion * assertion
  | JCAmutable of term * struct_info * tag
  | JCAeqtype of tag * tag * struct_info option
  | JCAsubtype of tag * tag * struct_info option
  | JCAmatch of term * (pattern * assertion) list

and assertion = assertion_node c_assertion

type term_or_assertion =
  | JCAssertion of assertion
  | JCTerm of term
  | JCReads of location list

type loop_annot =
    {
      jc_loop_tag : int;
      mutable jc_loop_invariant : (string list * assertion) list;
      mutable jc_free_loop_invariant : assertion;
      jc_loop_variant : term option;
    }


type behavior =
    { 
      jc_behavior_throws : exception_info option ;
      jc_behavior_assumes : assertion option ;
      jc_behavior_assigns : (Loc.position * location list) option ;
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
(*    typed ast   *)
(******************)

class type ['node] c_expr =
object
  inherit typed
  inherit regioned
  inherit marked
  inherit ['node] node_positioned
  method original_type: jc_type
end

(* application, increment and assignment are statements.
   special assignment with operation disappears.
 *)
type expr_node =
  | JCEconst of const
  | JCEvar of var_info
  | JCEderef of expr * field_info
  | JCEbinary of expr * expr_bin_op * expr
  | JCEunary of expr_unary_op * expr
  | JCEapp of call
  | JCEassign_var of var_info * expr
  | JCEassign_heap of expr * field_info * expr
  | JCEinstanceof of expr * struct_info
  | JCEcast of expr * struct_info
  | JCEbitwise_cast of expr * struct_info
  | JCErange_cast of expr * enum_info
  | JCEreal_cast of expr * real_conversion
  | JCEif of expr * expr * expr
  | JCEoffset of offset_kind * expr * struct_info
  | JCEaddress of expr
  | JCEalloc of expr * struct_info
  | JCEfree of expr
  | JCElet of var_info * expr option * expr
  | JCEassert of string list * assertion
  | JCEcontract of assertion option * term option * var_info * 
      (Loc.position * string * behavior)
 list * expr
  | JCEblock of expr list
  | JCEloop of loop_annot * expr
  | JCEreturn_void 
  | JCEreturn of jc_type * expr (*r expected return type *) 
  | JCEtry of expr 
      * (exception_info * var_info option * expr) list * expr
  | JCEthrow of exception_info * expr option
  | JCEpack of struct_info * expr * struct_info
  | JCEunpack of struct_info * expr * struct_info
  | JCEmatch of expr * (pattern * expr) list
  | JCEshift of expr * expr
      
and expr = expr_node c_expr

and callee = JClogic_fun of logic_info | JCfun of fun_info

and call = 
    {
      jc_call_fun : callee;
      jc_call_args : expr list;
      mutable jc_call_region_assoc : (region * region) list;
      jc_call_label_assoc : (label * label) list;
    }

(*
type loop_annot =
    {
      jc_loop_invariant : assertion;
      jc_loop_variant : term;
    }
*)

(*type incr_op = Stat_inc | Stat_dec*)

(* application, increment and assignment are exprs. 
   expressions (without any of the above) are not exprs anymore.
   break, continue, goto are translated with exceptions.
*)


(*
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
