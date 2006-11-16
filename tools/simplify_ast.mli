
type atom = 
  | Defpred
  | Bg_push
  | True
  | Implies
  | Iff
  | Forall
  | Mpat
  | Pats
  | And
  | Or
  | Eq
  | Neq
  | Distinct
  | Lblpos
  | Lblneg
  | Ident of string

type sexp =
  | Satom of atom
  | Slist of sexp list

type t = sexp list
