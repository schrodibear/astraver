
open Jc_env
open Jc_ast

let functions_table = Hashtbl.create 97

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

let param (t,id) =
  let vi = {
    jc_var_info_name = id;
    jc_var_info_type = t;
  }
  in (id,vi)

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
	let b = List.map (statement param_env) body in
	Hashtbl.add functions_table id (fi,b)
	  


