
open Jc_env
open Jc_ast
open Output

let const c =
  match c with
    | JCCnull -> assert false
    | JCCreal s -> Prim_real s
    | JCCinteger s -> Prim_int s
    | JCCbool b -> Prim_bool b

let rec term t =
  match t with
    | JCTconst JCCnull -> LVar "null"
    | JCTconst c -> LConst(const c)
    | JCTshift(t1,t2) -> LApp("shift",[term t1; term t2])
    | JCTderef(t,f) -> LApp("select",[term t; LVar f.jc_field_info_name])
    | JCTapp(f,l) -> assert false

let rec assertion a =
  match a with
    | JCAapp(f,l) -> assert false

let rec expr e =
  match e with
    | JCEconst JCCnull -> Var "null"
    | JCEconst c -> Cte(const c)
    | JCEshift(e1,e2) -> make_app "shift" [expr e1; expr e2]
    | JCEderef(e,f) -> make_app "select" [expr e; Var f.jc_field_info_name]
    | JCSassign (_, _) -> assert false
    | JCEcall (_, _) -> assert false

let statement s = 
  match s with
    | JCSskip -> Void
    | JCSexpr e -> expr e
    | JCSif (_, _, _) -> assert false
    | JCSwhile (_, _, _) -> assert false
    | JCSassert _ -> assert false
    | JCSdecl _ -> assert false
    | JCSreturn e -> assert false
    | JCSbreak l -> assert false
    | JCScontinue l -> assert false
    | JCSgoto l -> assert false
    | JCSthrow (_, _) -> assert false
    | JCStry (_, _, _) -> assert false

let decl d =
  match d with
    | JCDfun(f,args,e) -> assert false
