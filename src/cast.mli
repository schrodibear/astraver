
(* C abstract syntax trees *)

open Logic
open Ptree

type constant_expression = unit

type annot = string

type declarator =
  | CDvar of Ident.t
  | CDarr of Ident.t * constant_expression
  | CDfun of Ident.t * (pure_type * Ident.t) list * annot option

type decl = 
  | Ctypedecl of Loc.t * declarator * pure_type

type file = decl list
