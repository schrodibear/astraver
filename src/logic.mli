
(*i $Id: logic.mli,v 1.3 2001-08-19 02:44:48 filliatr Exp $ i*)

(*s Logic. *)

type constant =
  | ConstInt of int
  | ConstBool of bool
  | ConstUnit
  | ConstFloat of float

type term =
  | Tvar of Ident.t
  | Tconst of constant
  | Tapp of Ident.t * term list

type predicate =
  | Pterm of term
  | Pimplies of predicate * predicate
  | Pif of predicate * predicate * predicate
  | Pand of predicate * predicate
  | Por of predicate * predicate
  | Pnot of predicate

  
