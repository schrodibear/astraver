
(*i $Id: logic.mli,v 1.4 2001-08-21 20:57:01 filliatr Exp $ i*)

(*s Logic. *)

type constant =
  | ConstInt of int
  | ConstBool of bool
  | ConstUnit
  | ConstFloat of float

type term =
  | Tvar of Ident.t
  | Tbound of Ident.bound
  | Tconst of constant
  | Tapp of Ident.t * term list

(*s Pure types. *)

type pure_type =
  | PTint
  | PTbool
  | PTfloat
  | PTunit
  | PTarray of term * pure_type
  | PTexternal of Ident.t

type predicate =
  | Pterm of term
  | Pimplies of predicate * predicate
  | Pif of predicate * predicate * predicate
  | Pand of predicate * predicate
  | Por of predicate * predicate
  | Pnot of predicate
  | Forall of Ident.t * Ident.bound * pure_type * predicate

  


