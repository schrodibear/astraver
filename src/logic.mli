
(*i $Id: logic.mli,v 1.5 2002-02-04 16:42:21 filliatr Exp $ i*)

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
  | Pvar of Ident.t
  | Papp of Ident.t * term list
  | Ptrue
  | Pfalse
  | Pimplies of predicate * predicate
  | Pif of term * predicate * predicate
  | Pand of predicate * predicate
  | Por of predicate * predicate
  | Pnot of predicate
  | Forall of Ident.t * Ident.bound * pure_type * predicate

  


