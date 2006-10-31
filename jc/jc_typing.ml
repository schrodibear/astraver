
open Jc_env
open Jc_ast

let functions_table = Hashtbl.create 97

let logic_bin_op op =
  match op with
    | `Bge -> assert false
    | `Ble -> assert false
    | `Bland -> assert false
    | `Bimplies -> assert false

let rec term env e =
  let te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in JCTvar vi
	    with Not_found -> assert false
	  end
      | JCPEbinary (e1, op, e2) -> 
	  JCTapp(logic_bin_op op,[term env e1 ; term env e2])
      | JCPEassign (_, _) -> assert false
      | JCPEapp (_, _) -> assert false
      | JCPEderef (_, _) -> assert false
      | JCPEshift (_, _) -> assert false
      | JCPEconst _ -> assert false
      | JCPEforall _ -> failwith "not allowed in this context"

  in { jc_term_node = te;
       jc_term_loc = e.jc_pexpr_loc }

  
let rel_ge =
  { jc_logic_info_name = "ge_int";
    jc_logic_info_result_type = None }
    
let rel_le =
  { jc_logic_info_name = "le_int";
    jc_logic_info_result_type = None }
    
let tr_rel_op op =
  match op with
    | `Bge -> rel_ge
    | `Ble -> rel_le
    | _ -> assert false

let make_and a1 a2 =
  match (a1.jc_assertion_node,a2.jc_assertion_node) with
    | (JCAtrue,a2) -> a2
    | (a1,JCAtrue) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCAand l1 , JCAand l2) -> JCAand(l1@l2)
    | (JCAand l1 , _ ) -> JCAand(l1@[a2])
    | (_ , JCAand l2) -> JCAand(a1::l2)
    | _ -> JCAand [a1;a2]

let rec assertion env e =
  let te =
    match e.jc_pexpr_node with
      | JCPEvar id -> assert false
      | JCPEbinary (e1, `Bland, e2) -> 
	  make_and (assertion env e1) (assertion env e2)
      | JCPEbinary (e1, `Bimplies, e2) -> 
	  JCAimplies(assertion env e1,assertion env e2)
      | JCPEbinary (e1, op, e2) -> 
	  JCAapp(tr_rel_op op,[term env e1 ; term env e2])
      | JCPEassign (_, _) -> assert false
      | JCPEapp (_, _) -> assert false
      | JCPEderef (_, _) -> assert false
      | JCPEshift (_, _) -> assert false
      | JCPEconst _ -> assert false
      | JCPEforall(ty,id,e) -> 
	  let vi = {
	    jc_var_info_name = id;
	    jc_var_info_final_name = id;
	    jc_var_info_type = ty;
	  }
	  in JCAforall(vi,assertion ((id,vi)::env) e)

  in { jc_assertion_node = te;
       jc_assertion_loc = e.jc_pexpr_loc }

let rec expr env e =
  let te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in JCEvar vi
	    with Not_found -> assert false
	  end
      | JCPEbinary (e1, op, e2) -> 
	  JCEbinary(expr env e1, op, expr env e2)
      | JCPEassign (_, _) -> assert false
      | JCPEapp (_, _) -> assert false
      | JCPEderef (_, _) -> assert false
      | JCPEshift (_, _) -> assert false
      | JCPEconst _ -> assert false
      | JCPEforall _ -> failwith "not allowed in this context"

  in { jc_expr_node = te;
       jc_expr_loc = e.jc_pexpr_loc }

  

let rec statement env s =
  let ts =
    match s.jc_pstatement_node with
      | JCPSskip -> JCSskip
      | JCPSthrow (_, _) -> assert false
      | JCPStry (_, _, _) -> assert false
      | JCPSgoto _ -> assert false
      | JCPScontinue _ -> assert false
      | JCPSbreak _ -> assert false
      | JCPSreturn e -> JCSreturn(expr env e)
      | JCPSwhile (_, _) -> assert false
      | JCPSif (e, s1, s2) -> 
	  JCSif(expr env e,statement env s1,statement env s2)
      | JCPSdecl (_, _, _) -> assert false
      | JCPSassert _ -> assert false
      | JCPSexpr e -> JCSexpr (expr env e)
      | JCPSblock l -> JCSblock (List.map (statement env) l)


  in { jc_statement_node = ts;
       jc_statement_loc = s.jc_pstatement_loc }

let clause env c acc =
  match c.jc_pclause_node with
    | JCPCensures(id,e) ->
	{ acc with 
	    jc_fun_ensures = (id,assertion env e)::acc.jc_fun_ensures }
	  

  
let param (t,id) =
  let vi = {
    jc_var_info_name = id;
    jc_var_info_final_name = id;
    jc_var_info_type = t;
  }
  in (id,vi)

let assertion_true =
  { jc_assertion_node = JCAtrue;
    jc_assertion_loc = Loc.dummy_position }

let decl d =
  match d.jc_pdecl_node with
    | JCPDfun(ty,id,pl,specs,body) -> 
	let param_env = List.map param pl in
	let fi = { 
	  jc_fun_info_name = id;
	  jc_fun_info_parameters = List.map snd param_env;
	  jc_fun_info_return_type = ty;
	}
	in
	let param_env_result =
	  ("\\result",{
	     jc_var_info_name = "\\result";
	     jc_var_info_final_name = "result";
	     jc_var_info_type = ty;
	  })::param_env
	in
	let s = List.fold_right 
		  (clause param_env_result) specs 
		  { jc_fun_requires = assertion_true;
		    jc_fun_ensures = [] }
	in
	let b = List.map (statement param_env) body in
	Hashtbl.add functions_table id (fi,s,b)
	  


