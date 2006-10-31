

open Jc_env



type const =
  | JCCnull
  | JCCbool of bool
  | JCCinteger of string
  | JCCreal of string

type bin_op =
  [ `Ble | `Bge | `Bland | `Bimplies ]

type label = string

(***************)
(* parse trees *)
(***************)


type pexpr_node =
  | JCPEconst of const
  | JCPEvar of string
  | JCPEshift of pexpr * pexpr
  | JCPEderef of pexpr * string
  | JCPEapp of string * pexpr list
  | JCPEassign of pexpr * pexpr
  | JCPEbinary of pexpr * bin_op * pexpr
  | JCPEforall of jc_type * string * pexpr

and pexpr =
    {
      jc_pexpr_node : pexpr_node;
      jc_pexpr_loc : Loc.position;
    }

type pclause_node =
  | JCPCensures of string * pexpr

and pclause =
    {
      jc_pclause_node : pclause_node;
      jc_pclause_loc : Loc.position;
    }

type pstatement_node =
  | JCPSskip
  | JCPSblock of pstatement list
  | JCPSexpr of pexpr
  | JCPSassert of pexpr
  | JCPSdecl of jc_type * string * pexpr
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
  | JCPDfun of jc_type * string * (jc_type * string) list * pclause list * pstatement list

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
  | JCEassign of expr * expr
  | JCEbinary of expr * bin_op * expr

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


type fun_spec =
    {
      jc_fun_requires : assertion;
      jc_fun_ensures : (string * assertion) list;
    }



