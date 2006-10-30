

open Jc_env

type const =
  | JCCnull
  | JCCbool of bool
  | JCCinteger of string
  | JCCreal of string

type term =
  | JCTconst of const
  | JCTshift of term * term
  | JCTderef of term * field_info
  | JCTapp of logic_info * term list

type assertion =
  | JCAapp of logic_info * term list

type expr =
  | JCEconst of const
  | JCEshift of expr * expr
  | JCEderef of expr * field_info
  | JCEcall of fun_info * expr list
  | JCSassign of expr * expr

type loop_annot =
    {
      jc_loop_invariant : assertion;
      jc_loop_variant : term;
    }

type label = string

type statement =
  | JCSskip
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


type decl =
  | JCDfun of fun_info * var_info list * statement
