
(*i $Id: logic.mli,v 1.8 2002-07-05 16:14:09 filliatr Exp $ i*)

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

type substitution = term Ident.map
type var_substitution = Ident.t Ident.map

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
  | Forall of Ident.t * Ident.t * pure_type * predicate

type logic_type =
  | Predicate of pure_type list
  | Function of pure_type list * pure_type
