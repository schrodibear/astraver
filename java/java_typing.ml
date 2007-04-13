
open Java_env
open Java_ast
open Java_tast
open Format
open Java_pervasives

let methods_table = Hashtbl.create 97

exception Typing_error of Loc.position * string

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter

let imported_packages = ref [ "java.lang" ]

let axioms_table = Hashtbl.create 17

let type_type ty =
  match ty with
    | Base_type t -> JTYbase t
    | Type_name _ -> assert false (* TODO *)
    | Array_type_expr _ -> assert false (* TODO *)

let string_of_base_type t =
  match t with
(*
    | Tunit -> "unit"
*)
    | Tinteger -> "integer"
    | Treal -> "real"
    | Tboolean -> "boolean"
    | Tdouble -> "double"
    | Tlong -> "long"
    | Tfloat -> "float"
    | Tint -> "int"
    | Tchar -> "char"
    | Tbyte -> "byte"
    | Tshort -> "short"


let print_type fmt t =
  match t with
    | JTYbase t -> fprintf fmt "%s" (string_of_base_type t)
    | _ -> assert false (* TODO *)


(* variables *)

let var_tag_counter = ref 0

let var ty id =
  incr var_tag_counter;
  let vi = {
    java_var_info_tag = !var_tag_counter;
    java_var_info_name = id;
    java_var_info_final_name = id;
    java_var_info_type = ty;
    java_var_info_assigned = false;
  }
  in vi

(* methods *)

let method_tag_counter = ref 0

let method_info id ty pars =
  incr method_tag_counter;
  {
    method_info_tag = !method_tag_counter;
    method_info_name = id;
    method_info_trans_name = id;
    method_info_return_type = ty;
    method_info_parameters = pars;
    method_info_is_static = false
  }
    

let rec var_type_and_id ty id =
  match id with
    | Simple_id (loc,n) -> ty,n
    | Array_id id -> 
	let ty,n = var_type_and_id ty id in
	JTYarray(ty),n

let logic_bin_op ty op =
  match ty,op with
    | Tinteger,Badd -> add_int
    | Tinteger,Bmul -> mul_int
    | Tinteger,Beq -> eq_int
    | Tinteger,Bge -> ge_int
    | _,Ble -> le_int 
    | _,Blt -> lt_int
    | _,Bgt -> gt_int
    | _,Bne -> ne_int 
    | _,(Basr|Blsr|Blsl) -> assert false (* TODO *)
    | _,(Bbwxor|Bbwor|Bbwand) -> assert false (* TODO *)
    | _,(Bimpl|Bor|Band) -> assert false (* TODO *)
    | _,(Bmod|Bdiv|Bsub) -> assert false (* TODO *)
    | _ -> assert false (* TODO *)

let lit l =
  match l with
    | Integer s -> integer_type,l
    | Char s -> assert false (* TODO *)
    | String s -> assert false (* TODO *)
    | Bool b -> boolean_type,l
    | Float s -> real_type,l
    | Null -> assert false (* TODO *)

let is_numeric t =
  match t with
    | JTYbase t -> 
	begin
	  match t with
	    | Tinteger | Tshort | Tbyte | Tint | Tlong -> true
	    | Treal | Tdouble | Tfloat -> true
	    | Tchar -> assert false (* TODO *)
	    | Tboolean -> false
	end
    | _ -> false

let is_boolean t =
  match t with
    | JTYbase Tboolean -> true
    | _ -> false

let lub_numeric_types t1 t2 =
  match t1,t2 with
    | JTYbase t1,JTYbase t2 -> 
	begin
	  match t1,t2 with
	    | (Treal | Tdouble | Tfloat),_ 
	    | _, (Treal | Tdouble | Tfloat) -> Treal
	    | _ -> Tinteger

	end
    | _ -> assert false

(*
let term_coerce t1 t2 e =
  let e_int =
    match t1 with
      | JCTrange ri ->
	  let (_,to_int,_,_) = 
	    Hashtbl.find range_types_table ri.jc_range_info_name 
	  in
	  { jc_tterm_node = JCTTapp(to_int,[e]) ;
	    jc_tterm_loc = e.jc_tterm_loc }  
      | _ -> e
  in
  match t2 with
    | Tinteger -> e_int
    | Treal -> 
	{ jc_tterm_node = JCTTapp(real_of_integer,[e_int]) ;
	  jc_tterm_loc = e.jc_tterm_loc }  
    | _ -> assert false
*)

(*
let subbasetype t1 t2 =
  match t1,t2 with
    | (Tint|Tshort), Tinteger -> true
    | _,Tinteger -> assert false (* TODO *)
    | Tint,Tint -> true
    | _,_ -> assert false (* TODO *)

let subtype t1 t2 =
  match t1,t2 with
    | JTYbase t1, JTYbase t2 -> subbasetype t1 t2
    | _ -> assert false (* TODO *)
*)

let compatible_base_types t1 t2 = true

let compatible_types t1 t2 =
  match t1,t2 with
    | JTYbase t1, JTYbase t2 -> compatible_base_types t1 t2
    | _ -> assert false (* TODO *)

let make_logic_bin_op loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble | Beq | Bne ->
	assert false (* TODO *)
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand|Bimpl|Bor|Band|Biff ->
	assert false (* TODO *)
    | Bsub | Badd | Bmod | Bdiv | Bmul ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  (JTYbase t,
	   JTbin(e1,t,op,e2))
	else typing_error loc "numeric types expected for +,-,*, / and %%"


let rec term env e =
  let ty,tt =
    match e.java_pexpr_node with
    | JPElit l -> 
	let ty,l = lit l in ty,(JTlit l)
    | JPEvar(loc, id) -> 
	begin
	  try
	    let vi = List.assoc id env
	    in vi.java_var_info_type,JTvar vi
	  with Not_found -> 
	    typing_error e.java_pexpr_loc "unbound identifier %s" id
	end
    | JPEresult -> 
	begin
	  try
	    let vi = List.assoc "\\result" env
	    in vi.java_var_info_type,JTvar vi
	  with Not_found -> 
	    typing_error e.java_pexpr_loc "\\result undefined in this context"
	end
    | JPEthis -> assert false (* TODO *)
    | JPEbin (e1, op, e2) -> 
	let ty1,te1 = term env e1
	and ty2,te2 = term env e2
	in make_logic_bin_op e.java_pexpr_loc op ty1 te1 ty2 te2
    | JPEquantifier (q, ty, idl, e)-> 
	typing_error e.java_pexpr_loc
	  "quantified formulas not allowed in term position"
    | JPEold _-> assert false (* TODO *)
    | JPEinstanceof (_, _)-> assert false (* TODO *)
    | JPEcast (_, _)-> assert false (* TODO *)
    | JPEarray_access (_, _)-> assert false (* TODO *)
    | JPEnew_array _-> assert false (* TODO *)
    | JPEnew (_, _)-> assert false (* TODO *)
    | JPEsuper_call (_, _)-> assert false (* TODO *)
    | JPEcall (_, _, _)-> assert false (* TODO *)
    | JPEfield_access _-> assert false (* TODO *)
    | JPEif (_, _, _)-> assert false (* TODO *)
    | JPEassign_array (_, _, _, _)-> assert false (* TODO *)
    | JPEassign_field (_, _, _)-> assert false (* TODO *)
    | JPEassign_name (_, _, _)-> assert false (* TODO *)
    | JPEincr (_, _)-> assert false (* TODO *)
    | JPEun (_, _)-> assert false (* TODO *)

  in ty,{ java_term_node = tt; java_term_loc = e.java_pexpr_loc }


let make_predicate_bin_op loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble | Beq | Bne ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JAbin(e1,t,op,e2)
	else typing_error loc "numeric types expected for >,<,>=,<=,== and !="
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand|Bimpl|Bor|Band|Biff ->
	assert false (* TODO *)
    | Bsub | Badd | Bmod | Bdiv | Bmul ->
	typing_error loc "operator +,-,*, / and %% is not a predicate"

let connective a1 op a2 =
  match op with
    | Band -> JAand(a1,a2)
    | Bor -> JAor(a1,a2)
    | Bimpl -> JAimpl(a1,a2)
    | _ -> assert false

let rec assertion env e =
  let ta =
  match e.java_pexpr_node with
    | JPElit (Bool true) -> JAtrue
    | JPElit (Bool false) -> JAfalse
    | JPElit _ -> 
	typing_error e.java_pexpr_loc 
	  "this literal is not a boolean expression"
    | JPEbin(e1, ((Band | Bor | Bimpl) as op) , e2) ->
	let te1 = assertion env e1
	and te2 = assertion env e2
	in connective te1 op te2
    | JPEbin(e1, op, e2) -> 
	let ty1,te1 = term env e1
	and ty2,te2 = term env e2
	in make_predicate_bin_op e.java_pexpr_loc op ty1 te1 ty2 te2
    | JPEquantifier (q, ty, idl, e)-> 
	let tty = type_type ty in
	let a = make_quantified_formula e.java_pexpr_loc q tty idl env e in
	a.java_assertion_node
    | JPEold _-> assert false (* TODO *)
    | JPEinstanceof (_, _)-> assert false (* TODO *)
    | JPEcast (_, _)-> assert false (* TODO *)
    | JPEarray_access (_, _)-> assert false (* TODO *)
    | JPEnew_array _-> assert false (* TODO *)
    | JPEnew (_, _)-> assert false (* TODO *)
    | JPEsuper_call (_, _)-> assert false (* TODO *)
    | JPEcall (_, _, _)-> assert false (* TODO *)
    | JPEfield_access _-> assert false (* TODO *)
    | JPEif (_, _, _)-> assert false (* TODO *)
    | JPEassign_array (_, _, _, _)-> assert false (* TODO *)
    | JPEassign_field (_, _, _)-> assert false (* TODO *)
    | JPEassign_name (_, _, _)-> assert false (* TODO *)
    | JPEvar _-> assert false (* TODO *)
    | JPEincr (_, _)-> assert false (* TODO *)
    | JPEun (_, _)-> assert false (* TODO *)
    | JPEresult -> assert false (* TODO *)
    | JPEthis -> assert false (* TODO *)

  in { java_assertion_node = ta;
       java_assertion_loc = e.java_pexpr_loc }

and make_quantified_formula loc q ty idl env e : assertion =
  match idl with
    | [] -> assertion env e
    | id::r ->
	let tyv, n = var_type_and_id ty id in
	let vi = var tyv n in
	let f = make_quantified_formula loc q ty r ((n,vi)::env) e in
	{ java_assertion_loc = loc ; 
	  java_assertion_node = JAquantifier(q,vi,f) }


(* expressions *)

let make_bin_op loc op t1 e1 t2 e2 =
    match op with
    | Bgt | Blt | Bge | Ble | Beq | Bne ->
	if is_numeric t1 && is_numeric t2 then
	  let _t = lub_numeric_types t1 t2 in
	  Tboolean,
	  JEbin((*coerce t1 t*) e1, op, (*coerce t2 t*) e2)
	else
	  typing_error loc "numeric types expected"
    | Badd | Bsub | Bmul | Bdiv | Bmod ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  t,
	  JEbin((*coerce t1 t*) e1, op, (* coerce t2 t*) e2)
	else
	  typing_error loc "numeric types expected for +, -, *, / and %%"
    | Band | Bor -> 
	if is_boolean t1 && is_boolean t2 then
	  Tboolean,JEbin(e1,op,e2)
	else
	  typing_error loc "booleans expected"
	(* not allowed as expression op *)
    |Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand -> assert false (* TODO *)
    | Bimpl | Biff -> assert false

let rec expr env e =
  let ty,te = 
    match e.java_pexpr_node with
      | JPElit l -> let t,l = lit l in t,(JElit l)
      | JPEvar (loc,id) -> 
	  begin
	    try
	      let vi = List.assoc id env
	      in vi.java_var_info_type,JEvar vi
	    with Not_found -> 
	      typing_error loc "unbound identifier %s" id
	  end	  
      | JPEthis -> assert false (* TODO *)
      | JPEinstanceof (_, _)-> assert false (* TODO *)
      | JPEcast (_, _)-> assert false (* TODO *)
      | JPEarray_access (_, _)-> assert false (* TODO *)
      | JPEnew_array _-> assert false (* TODO *)
      | JPEnew (_, _)-> assert false (* TODO *)
      | JPEsuper_call (_, _)-> assert false (* TODO *)
      | JPEcall (_, _, _)-> assert false (* TODO *)
      | JPEfield_access _-> assert false (* TODO *)
      | JPEif (_, _, _)-> assert false (* TODO *)
      | JPEassign_array (_, _, _, _)-> assert false (* TODO *)
      | JPEassign_field (_, _, _)-> assert false (* TODO *)
      | JPEassign_name (n, op, e)-> 
	  begin
	    let tye,te = expr env e in
	    match n with
	      | [(loc,id)] ->
		  begin
		    try
		      let vi = List.assoc id env in 
		      if compatible_types tye vi.java_var_info_type
		      then 
			if op = Beq then
			  vi.java_var_info_type,JEassign_local_var(vi,te)
			else assert false (* TODO *)
		      else
			typing_error loc "type %a expected, got %a" 
			  print_type vi.java_var_info_type print_type tye
		    with Not_found -> 
		      typing_error loc "unbound identifier %s" id
		  end
	      | (loc,id)::r ->
		  (* let _tyr,_tr = expr env r in *)
		  assert false (* TODO *)
	      | [] -> assert false
	  end
      | JPEincr (op, e)-> 
	  let t,te = expr env e in 
	  begin
	    match te.java_expr_node with
	      | JEvar v ->
		  t,JEincr_local_var(op,v)
	      | _ -> assert false (* TODO *)
	  end	  
      | JPEun (_, _)-> assert false (* TODO *)
      | JPEbin (e1, op, e2) -> 
	  let ty1,te1 = expr env e1
	  and ty2,te2 = expr env e2
	  in 
	  let t,e = make_bin_op e.java_pexpr_loc op ty1 te1 ty2 te2 in
	  JTYbase t,e
	       (* only in terms *)
      | JPEquantifier (_, _, _, _)
      | JPEold _
      | JPEresult -> 
	  typing_error e.java_pexpr_loc "not allowed in expressions"

  in
  ty,
  { java_expr_loc = e.java_pexpr_loc;
    java_expr_type = ty;
    java_expr_node = te;
  }


			   
let type_initializer env ty i =
  match ty,i with
    | JTYbase t, Simple_initializer e ->
	let tye,te = expr env e in	
	if compatible_types ty tye then JIexpr te
	else
	  typing_error e.java_pexpr_loc "type %a expected, got %a"
	    print_type ty print_type tye
    | _ -> assert false (* TODO *)

(* statements *)

(*
let rec type_variable_id ty id =
  match id with
    | Simple_id (loc,id) -> (ty,id)
    | Array_id v ->
	let t,i = type_variable_id ty v in
	JTYarray t,i
*)

let rec statement env s =
  let s' =
    match s.java_pstatement_node with
      | JPSskip -> JSskip
      | JPSif (e, s1, s2) ->
	  let ty,te = expr env e in
	  let ts1 = statement env s1 in
	  let ts2 = statement env s2 in
	  if is_boolean ty then	    
	    JSif(te,ts1,ts2)
	  else
	    typing_error e.java_pexpr_loc "boolean expected"
      | JPSloop_annot (inv, dec) -> assert false
      | JPSannot (_, _)-> assert false (* TODO *)
      | JPSassert _-> assert false (* TODO *)
      | JPSsynchronized (_, _)-> assert false (* TODO *)
      | JPSblock l -> (block env l).java_statement_node
      | JPSswitch (_, _)-> assert false (* TODO *)
      | JPStry (_, _, _)-> assert false (* TODO *)
      | JPSfor_decl (_, _, _, _)-> assert false (* TODO *)
      | JPSfor (_, _, _, _)-> assert false (* TODO *)
      | JPSdo (_, _)-> assert false (* TODO *)
      | JPSwhile (_, _)-> assert false (* TODO *)
      | JPSlabel (_, _)-> assert false (* TODO *)
      | JPScontinue _-> assert false (* TODO *)
      | JPSbreak _-> assert false (* TODO *)
      | JPSreturn None -> assert false (* TODO *)
      | JPSreturn (Some e) -> 
	  begin
	    try
	      let t,te = expr env e in 
	      let vi = List.assoc "\\result" env in
	      if compatible_types t vi.java_var_info_type then
		JSreturn te
	      else
		begin
		  try
		    JSreturn ((* restrict t vi.jc_var_info_type*) te)
		  with
		      Invalid_argument _ ->
			typing_error s.java_pstatement_loc "type '%a' expected"
			  print_type vi.java_var_info_type
		end
	    with
		Not_found ->
		  typing_error e.java_pexpr_loc "no result expected"
	  end
      | JPSthrow _-> assert false (* TODO *)
      | JPSvar_decl _-> assert false (* TODO *)
      | JPSexpr e -> 
	  let t,te = expr env e in JSexpr te
	  
  in 
  { java_statement_loc = s.java_pstatement_loc ;
    java_statement_node = s' }


and statements env b =
  match b with
    | [] -> []
    | s :: rem ->
	match s.java_pstatement_node with
	  | JPSskip -> statements env rem
	  | JPSvar_decl vd -> 
	      let ty = type_type vd.variable_type in
	      let l =
		List.map
		  (fun vd ->
		     let ty',id = var_type_and_id ty vd.variable_id in
		     match vd.variable_initializer with
		       | None -> (id,ty',None)
		       | Some e -> 
			   let i = type_initializer env ty' e in
			   (id,ty',Some i))
		  vd.variable_decls
	      in
	      let env,decls =
		List.fold_right
		  (fun (id,ty,i) (env,decls)->
		     let vi = var ty id in		     
		     (id,vi)::env,(vi,i)::decls)
		  l (env,[])
	      in
	      let r = block env rem in
	      let s =
		List.fold_right
		  (fun (vi,i) acc -> 
		     { java_statement_loc = s.java_pstatement_loc ;
		       java_statement_node =
			 JSvar_decl(vi,i,acc); })
		  decls r in
	      [s]
	  | JPSloop_annot(inv,dec) ->
	      let inv = assertion env inv in
	      let tdec,dec = term env dec in
	      begin
		match rem with
		  | { java_pstatement_node = JPSwhile(e,s) ;
		      java_pstatement_loc = loc } :: rem -> 
		      let te,e = expr env e in
		      let s = statement env s in
		      { java_statement_node = JSwhile(e,inv,dec,s);
			java_statement_loc = loc } :: statements env rem
		  | _ -> assert false (* TODO *)
	      end      
	  | _ ->
	      let s' = statement env s in
	      s' :: statements env rem

and block env b =
  match statements env b with
    | [] -> { java_statement_loc = Loc.dummy_position ; 
	      java_statement_node = JSskip }
    | [s] -> s
    | (s::_) as l -> 
	{ java_statement_loc = s.java_statement_loc ; 
	  java_statement_node = JSblock l }

(* methods *)

let rec type_param p =
  match p with
    | Simple_parameter(ty,(loc,id)) -> 
	let vi = var (type_type ty) id in id,vi
    | Array_parameter id -> assert false

let rec method_header retty mdecl =
  match mdecl with
    | Simple_method_declarator(id,l) -> 
	id,(Option_misc.map type_type retty), List.map type_param l
    | Array_method_declarator d -> 
	let id,t,l = method_header retty d in
	match t with
	  | Some t -> id,Some (JTYarray t),l
	  | None -> typing_error (fst id) "invalid type void array"

let behavior env env_result (id,b) = 
  let env_ensures = 
    match b.java_pbehavior_throws with
      | None -> env_result
      | Some(c,id) -> assert false (* TODO *)
  in
  (id,
   Option_misc.map (assertion env) b.java_pbehavior_assumes,
   Option_misc.map (fun _ -> assert false (* TODO *)) b.java_pbehavior_assigns,
   assertion env_ensures b.java_pbehavior_ensures)
	

let rec class_fields l acc =
  match l with
    | [] -> acc
    | JPFmethod _ :: rem -> assert false
    | JPFmethod_spec(req,behs) :: JPFmethod(head,body) :: rem ->
	let id, ret_ty, params = 
	  method_header head.method_return_type head.method_declarator 
	in
	let mi = method_info (snd id) ret_ty (List.map snd params) in
	let req = Option_misc.map (assertion params) req in
	let env_result =
	  match ret_ty with
	    | None -> params
	    | Some t ->
		let vi = var t "\\result" in ("\\result",vi)::params
	in
	let behs = List.map (behavior params env_result) behs in
	let body = Option_misc.map (statements env_result) body in
	Hashtbl.add methods_table mi.method_info_tag (mi,req,behs,body);
	class_fields rem (mi :: acc)
   | JPFmethod_spec(req,behs) :: JPFconstructor(head,eci,body) :: rem ->
	assert false
(*let id, ret_ty, params = 
	  method_header head.method_return_type head.method_declarator 
	in
	let mi = method_info (snd id) ret_ty (List.map snd params) in
	let req = Option_misc.map (assertion params) req in
	let behs = List.map (behavior params ret_ty) behs in
	let body = Option_misc.map (statements params) body in
	Hashtbl.add constructors_table mi.method_info_tag (mi,req,behs,body);
	class_fields rem (mi :: acc) *)
    | JPFmethod_spec _ :: _ ->
	typing_error (assert false) "out of place method specification"
    | JPFinvariant _ :: rem ->  assert false (* TODO *)
    | JPFannot _ :: _ -> assert false (* not possible after 2nd parsing *)
    | JPFstatic_initializer _ ::rem -> assert false (* TODO *)
    | JPFvariable vd :: rem -> 
	(*
	vd.variable_modifiers : modifiers ;
	vd.variable_type : type_expr ;
	vd.variable_decls : variable_declarator list }
*)assert false (* TODO *)
    | JPFconstructor _ :: rem -> assert false (* TODO *)


let type_decl d = 
    match d with
    | JPTclass c -> 
	(*
	  class_modifiers : modifiers;
	  class_name : identifier;
	  class_extends : qualified_ident option;
	  class_implements : qualified_ident list;
	  class_fields : field_declaration list
	*)
	let _tf = class_fields c.class_fields [] in
	()
    | JPTinterface i -> assert false (* TODO *)
    | JPTannot(loc,s) -> assert false
    | JPTaxiom(id,e) -> 
	let te = assertion [] e in
	Hashtbl.add axioms_table id te
    | JPTlogic_type_decl _
    | JPTlogic_reads _ 
    | JPTlogic_def _ -> assert false (* TODO *)


let compilation_unit cu =
  assert (cu.cu_package = []); (* TODO *)
  assert (cu.cu_imports = []); (* TODO *)
  List.iter type_decl cu.cu_type_decls


(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
