
(*i $Id: logic.mli,v 1.1 2001-08-15 21:08:52 filliatr Exp $ i*)

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
  | Pvar of Ident.t
  | Papp of Ident.t * term list
  | Pimplies of predicate * predicate
  | Pand of predicate * predicate
  | Por of predicate * predicate
  | Pnot of predicate

  
