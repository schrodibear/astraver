
open Jc_env
open Jc_ast

let unit_type = JCTlogic "unit"
let integer_type = JCTlogic "int"
let boolean_type = JCTlogic "bool"

let functions_table = Hashtbl.create 97

let structs_table = Hashtbl.create 97

exception Typing_error of Loc.position * string

let typing_error l f = 
  Format.ksprintf (fun s -> raise (Typing_error(l, s))) f


let find_field ty f =
  {
	 jc_field_info_name = f;
	    jc_field_info_type = unit_type
	  }


(* terms *)

let make_term_op name ty =
  { jc_logic_info_name = name;
    jc_logic_info_result_type = Some ty;
  }

let eq_int_bool = make_term_op "eq_int_bool" boolean_type
let neq_int_bool = make_term_op "neq_int" boolean_type
let add_int = make_term_op "add_int" integer_type
let sub_int = make_term_op "sub_int" integer_type

let logic_bin_op op =
  match op with
    | `Bge -> assert false (* TODO *)
    | `Ble -> assert false (* TODO *)
    | `Beq -> eq_int_bool
    | `Bneq -> neq_int_bool
    | `Badd -> add_int
    | `Bsub -> sub_int
    | `Bland -> assert false (* TODO *)
    | `Bimplies -> assert false

let rec term env e =
  let te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in JCTvar vi
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id

	  end
      | JCPEbinary (e1, op, e2) -> 
	  JCTapp(logic_bin_op op,[term env e1 ; term env e2])
      | JCPEapp (_, _) -> assert false
      | JCPEderef (e, f) -> 
	  let t = term env e in
	  let fi = find_field unit_type f in
	  JCTderef(t,fi)	  
      | JCPEshift (_, _) -> assert false
      | JCPEconst c -> JCTconst c
      | JCPEold e -> JCTold(term env e)
	  (* non-pure expressions *)
      | JCPEassign_op _ 
      | JCPEassign _ -> failwith "assignment not allowed as logic term"
	  (* propositional (non-boolean) expressions *)
      | JCPEforall _ -> failwith "quantification not allowed as logic term"

  in { jc_term_node = te;
       jc_term_loc = e.jc_pexpr_loc }

  
let make_rel name =
  { jc_logic_info_name = name;
    jc_logic_info_result_type = None }

let ge_int = make_rel "ge_int"
let le_int = make_rel "le_int"
let eq_int = make_rel "eq_int"
let neq_int = make_rel "neq_int"
    
let tr_rel_op op =
  match op with
    | `Bge -> ge_int
    | `Ble -> le_int
    | `Beq -> eq_int
    | `Bneq -> neq_int
	(* non propositional operators *)
    | `Badd -> assert false
    | `Bsub -> assert false
	(* already recognized as connectives *)
    | `Bland -> assert false 
    | `Bimplies -> assert false

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
      | JCPEold e -> JCAold(assertion env e)
	  (* non-pure expressions *)
      | JCPEassign_op _ 
      | JCPEassign _ -> failwith "assignment not allowed as logic term"


  in { jc_assertion_node = te;
       jc_assertion_loc = e.jc_pexpr_loc }

(* expressions *)

let make_bin_op name ty =
 { jc_fun_info_name = name;
   jc_fun_info_parameters = [];
   jc_fun_info_return_type = ty }
 
let ge_int = make_bin_op "ge_int_" boolean_type
let le_int = make_bin_op "le_int_" boolean_type 
let eq_int = make_bin_op "eq_int_" integer_type
let neq_int = make_bin_op "neq_int_" integer_type
let add_int = make_bin_op "add_int_" integer_type
let sub_int = make_bin_op "sub_int_" integer_type
    
let tr_bin_op op =
  match op with
    | `Bge -> ge_int
    | `Ble -> le_int
    | `Beq -> eq_int
    | `Bneq -> neq_int
    | `Badd -> add_int
    | `Bsub -> sub_int
    | `Bland -> assert false (* TODO *)
	(* not allowed as expression op *)
    | `Bimplies -> assert false

let rec expr env e =
  let te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in JCEvar vi
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
      | JCPEbinary (e1, op, e2) -> 
	  JCEcall(tr_bin_op op, [expr env e1 ; expr env e2])
      | JCPEassign (_, _) -> assert false
      | JCPEassign_op (e1, op, e2) -> 
	  JCEassign_op(expr env e1, tr_bin_op op, expr env e2)
      | JCPEapp (_, _) -> assert false
      | JCPEderef (e, f) -> 
	  let fi = find_field unit_type f in
	  JCEderef(expr env e,fi)
      | JCPEshift (_, _) -> assert false
      | JCPEconst _ -> assert false
	  (* logic expressions, not allowed as program expressions *)
      | JCPEforall _ 
      | JCPEold _ -> failwith "not allowed in this context"

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
  match c with
    | JCPCrequires(e) ->
	{ acc with 
	    jc_fun_requires = assertion env e }
    | JCPCbehavior(id,assigns,ensures) ->
	let assigns =
	  match assigns with
	    | None -> None
	    | Some a -> Some(term env a)
	in
	let b = {
	  jc_behavior_assigns = assigns;
	  jc_behavior_ensures = assertion env ensures }
	in
	{ acc with jc_fun_behavior = (id,b)::acc.jc_fun_behavior }
	  

  
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
		    jc_fun_behavior = [] }
	in
	let b = List.map (statement param_env) body in
	Hashtbl.add functions_table id (fi,s,b)
    | JCPDtype(id,fields) ->
	Hashtbl.add structs_table id fields



