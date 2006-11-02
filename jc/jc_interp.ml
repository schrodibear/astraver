
open Jc_env
open Jc_ast
open Output

let const c =
  match c with
    | JCCnull -> assert false
    | JCCreal s -> Prim_real s
    | JCCinteger s -> Prim_int s
    | JCCbool b -> Prim_bool b


let tr_base_type t =
  match t with
    | JCTlogic "integer" -> ([],"int")
    | JCTlogic s -> ([],s)
    | JCTvalidpointer (_, _, _) -> assert false
    | JCTpointer _ -> assert false

let tr_type t =
  match t with
    | JCTlogic s -> Base_type(tr_base_type t)
    | JCTvalidpointer (_, _, _) -> assert false
    | JCTpointer _ -> assert false

let lvar label v =
  match label with 
    | None -> LVar v 
    | Some l -> LVarAtLabel(v,l)

let rec term label oldlabel t =
  let ft = term label oldlabel in
  match t.jc_term_node with
    | JCTconst JCCnull -> LVar "null"
    | JCTvar v -> lvar label v.jc_var_info_final_name
    | JCTconst c -> LConst(const c)
    | JCTshift(t1,t2) -> LApp("shift",[ft t1; ft t2])
    | JCTderef(t,f) -> LApp("select",[ft t; lvar label f.jc_field_info_name])
    | JCTapp(f,l) -> assert false
    | JCTold(t) -> term (Some oldlabel) oldlabel t

let rec assertion label oldlabel a =
  let fa = assertion label oldlabel 
  and ft = term label oldlabel
  in
  match a.jc_assertion_node with
    | JCAtrue -> LTrue
    | JCAand l -> make_and_list (List.map fa l)
    | JCAimplies(a1,a2) -> make_impl (fa a1) (fa a2)
    | JCAapp(f,l) -> LPred(f.jc_logic_info_name,List.map ft l)
    | JCAforall(v,p) -> 
	LForall(v.jc_var_info_final_name,
		tr_base_type v.jc_var_info_type,
		fa p)
    | JCAold a -> assertion (Some oldlabel) oldlabel a

let rec expr e =
  match e.jc_expr_node with
    | JCEconst JCCnull -> Var "null"
    | JCEconst c -> Cte(const c)
    | JCEvar v -> Var v.jc_var_info_final_name
    | JCEshift(e1,e2) -> make_app "shift" [expr e1; expr e2]
    | JCEderef(e,f) -> make_app "select" [expr e; Var f.jc_field_info_name]
    | JCEassign (_, _) -> assert false
    | JCEassign_op (e1, op, e2) -> assert false
    | JCEcall(f,l) -> 
	make_app f.jc_fun_info_name (List.map expr l)

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

let parameter v =
  (v.jc_var_info_final_name,tr_type v.jc_var_info_type)

let tr_fun f spec body acc = 
  let requires = assertion None "" spec.jc_fun_requires in
  let global_ensures =
    List.fold_right
      (fun (id,e) acc -> make_and (assertion None "" e.jc_behavior_ensures) acc)
      spec.jc_fun_behavior LTrue
  in
  let why_param = 
    let annot_type =
      Annot_type(requires,tr_type f.jc_fun_info_return_type,
		 [],[], global_ensures,[])
    in
    let fun_type =
      List.fold_right
	(fun v acc ->
	   Prod_type(v.jc_var_info_final_name,tr_type v.jc_var_info_type,acc))
	f.jc_fun_info_parameters
	annot_type
    in
    Param(false,f.jc_fun_info_name,fun_type)
  in
  let params = List.map parameter f.jc_fun_info_parameters in
  let acc =
    List.fold_right
      (fun (id,b) acc ->
	 let d =
	   Def(f.jc_fun_info_name ^ "_ensures_" ^ id,
	       Fun(params,
		   requires,statement_list body,
		   assertion None "" b.jc_behavior_ensures,[]))
	 in d::acc)
      spec.jc_fun_behavior acc
  in why_param::acc

  
