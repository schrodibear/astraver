

open Jc_env

type const =
  | JCCnull
  | JCCbool of bool
  | JCCinteger of string
  | JCCreal of string

type term =
  | JCTconst of const
  | JCTapp of logic_symbol * term list

type assertion =
  | JCAapp of logic_symbol * term list

type expr =
  | JCEconst of const
  | JCEcall of function_symbol * expr list
  | JCSassign of expr * expr
  | JCEderef of expr * field_symbol

type loop_annot =
    {
      jc_loop_invariant : assertion;
      jc_loop_variant : term;
    }

type statement =
  | JCSexpr of expr
  | JCSassert of assertion
  | JCSif of expr * statement * statement
  | JCSwhile of expr * loop_annot * statement
