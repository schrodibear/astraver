
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
  match t.jc_term_node with
    | JCTconst JCCnull -> LVar "null"
    | JCTconst c -> LConst(const c)
    | JCTshift(t1,t2) -> LApp("shift",[term t1; term t2])
    | JCTderef(t,f) -> LApp("select",[term t; LVar f.jc_field_info_name])
    | JCTapp(f,l) -> assert false

let rec assertion a =
  match a with
    | JCAapp(f,l) -> assert false

let expr_op op =
  match op with
    | `Bge -> "ge_int_"
    | `Ble -> "le_int_"

let rec expr e =
  match e.jc_expr_node with
    | JCEconst JCCnull -> Var "null"
    | JCEconst c -> Cte(const c)
    | JCEvar v -> Var v.jc_var_info_name
    | JCEshift(e1,e2) -> make_app "shift" [expr e1; expr e2]
    | JCEderef(e,f) -> make_app "select" [expr e; Var f.jc_field_info_name]
    | JCEassign (_, _) -> assert false
    | JCEbinary(e1,op,e2) -> 
	make_app (expr_op op) [expr e1; expr e2]
    | JCEcall (_, _) -> assert false

let rec statement s = 
  match s.jc_statement_node with
    | JCSskip -> Void
    | JCSblock l -> statement_list l
    | JCSexpr e -> expr e
    | JCSif (e, s1, s2) -> 
	If(expr e, statement s1, statement s2)
    | JCSwhile (_, _, _) -> assert false
    | JCSassert _ -> assert false
    | JCSdecl _ -> assert false
    | JCSreturn e -> 
	expr e
    | JCSbreak l -> assert false
    | JCScontinue l -> assert false
    | JCSgoto l -> assert false
    | JCSthrow (_, _) -> assert false
    | JCStry (_, _, _) -> assert false

and statement_list l =
  match l with
    | [] -> Void
    | [i] -> statement i
    | i::r -> assert false

let tr_type t =
  match t with
    | JCTlogic s -> Base_type([],s)
    | JCTvalidpointer (_, _, _) -> assert false
    | JCTpointer _ -> assert false

let parameter v =
  (v.jc_var_info_name,tr_type v.jc_var_info_type)

let tr_fun f e acc = 
  let d = 
    Def(f.jc_fun_info_name,
	Fun(List.map parameter f.jc_fun_info_parameters,
	    LTrue,statement_list e,LTrue,[]))
  in d::acc

  
