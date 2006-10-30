
open Jc_env
open Jc_ast
open Output

let const c =
  match c with
    | JCCnull -> assert false
    | JCCreal s -> Prim_real s
    | JCCinteger s -> Prim_int s
    | JCCbool b -> Prim_bool b

let rec expr e =
  match e with
    | JCEconst JCCnull -> Var "null"
    | JCEconst c -> Cte(const c)
    | JCEderef(e,f) -> make_app "select" [expr e;Var f.jc_field_symbol_name]
    | JCSassign (_, _) -> assert false
    | JCEcall (_, _) -> assert false

let statement s = 
  match s with
    | JCSexpr e -> expr e
    | JCSwhile (_, _, _) -> assert false
    | JCSif (_, _, _) -> assert false
    | JCSassert _ -> assert false
