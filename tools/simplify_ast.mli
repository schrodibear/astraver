
type atom = 
  | DEFPRED
  | BG_PUSH
  | AT_TRUE
  | TRUE
  | FALSE
  | IMPLIES
  | IFF
  | FORALL
  | MPAT
  | PATS
  | AND
  | OR
  | NOT
  | EQ
  | NEQ
  | DISTINCT
  | LBLPOS
  | LBLNEG
  | INTEGER of string
  | IDENT of string

type sexp =
  | Satom of atom
  | Slist of sexp list

type t = sexp list
