
open Java_ast
open Java_tast
open Format
open Java_pervasives

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
    | _,(Bge|Ble|Blt|Bgt|Bne) -> assert false (* TODO *)
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

let make_logic_bin_op loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble | Beq | Bne ->
	assert false (* TODO *)
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand|Bimpl|Bor|Band ->
	assert false (* TODO *)
    | Bsub | Badd | Bmod | Bdiv | Bmul ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  (JTYbase t,
	   JTapp(logic_bin_op t op,[e1; e2]))
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
    | Instanceof (_, _)-> assert false (* TODO *)
    | Cast (_, _)-> assert false (* TODO *)
    | Array_access (_, _)-> assert false (* TODO *)
    | Array_creation _-> assert false (* TODO *)
    | Class_instance_creation (_, _)-> assert false (* TODO *)
    | Super_method_call (_, _)-> assert false (* TODO *)
    | Method_call (_, _, _)-> assert false (* TODO *)
    | JPEfield_access _-> assert false (* TODO *)
    | JPEif (_, _, _)-> assert false (* TODO *)
    | JPEassign_array (_, _, _, _)-> assert false (* TODO *)
    | JPEassign_field (_, _, _)-> assert false (* TODO *)
    | Assign_name (_, _, _)-> assert false (* TODO *)
    | JPEincr (_, _)-> assert false (* TODO *)
    | JPEun (_, _)-> assert false (* TODO *)

  in ty,{ java_term_node = tt; java_term_loc = e.java_pexpr_loc }


let make_predicate_bin_op loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble | Beq | Bne ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JAapp(logic_bin_op t op,[e1; e2])
	else typing_error loc "numeric types expected for >,<,>=,<=,== and !="
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand|Bimpl|Bor|Band ->
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
    | Instanceof (_, _)-> assert false (* TODO *)
    | Cast (_, _)-> assert false (* TODO *)
    | Array_access (_, _)-> assert false (* TODO *)
    | Array_creation _-> assert false (* TODO *)
    | Class_instance_creation (_, _)-> assert false (* TODO *)
    | Super_method_call (_, _)-> assert false (* TODO *)
    | Method_call (_, _, _)-> assert false (* TODO *)
    | JPEfield_access _-> assert false (* TODO *)
    | JPEif (_, _, _)-> assert false (* TODO *)
    | JPEassign_array (_, _, _, _)-> assert false (* TODO *)
    | JPEassign_field (_, _, _)-> assert false (* TODO *)
    | Assign_name (_, _, _)-> assert false (* TODO *)
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

let rec expr env e =
  let ty,te = 
    match e.java_pexpr_node with
      | JPElit l -> let t,l = lit l in t,(JElit l)
      | JPEvar _ -> assert false (* TODO *)
      | JPEthis -> assert false (* TODO *)
      | Instanceof (_, _)
      | Cast (_, _)
      | Array_access (_, _)
      | Array_creation _
      | Class_instance_creation (_, _)
      | Super_method_call (_, _)
      | Method_call (_, _, _)
      | JPEfield_access _
      | JPEif (_, _, _)
      | JPEassign_array (_, _, _, _)
      | JPEassign_field (_, _, _)
      | Assign_name (_, _, _)
      | JPEincr (_, _)
      | JPEun (_, _)
      | JPEbin (_, _, _) -> assert false (* TODO *)
	  (* only in terms *)
      | JPEquantifier (_, _, _, _)
      | JPEold _
      | JPEresult -> 
	  typing_error e.java_pexpr_loc "not allowed in expressions"

  in
  { java_expr_loc = e.java_pexpr_loc;
    java_expr_type = ty;
    java_expr_node = te;
  }

(* statements *)

let rec statements env b =
  match b with
    | [] -> []
    | s :: rem ->
	match s.java_pstatement_node with
	  | JPSskip -> statements env rem
	  | JPSif (e, s1, s2) ->
	      let te = expr env e in
	      let ts1 = statements env [s1] in
	      let ts2 = statements env [s2] in
	      JSif(te,ts1,ts2)
	  | JPSloop_annot (_, _)
	  | JPSannot (_, _)
	  | JPSassert _
	  | JPSsynchronized (_, _)
	  | JPSblock _
	  | JPSswitch (_, _)
	  | JPStry (_, _, _)
	  | JPSfor_decl (_, _, _, _)
	  | JPSfor (_, _, _, _)
	  | JPSdo (_, _)
	  | JPSwhile (_, _)
	  | JPSlabel (_, _)
	  | JPScontinue _
	  | JPSbreak _
	  | JPSreturn _
	  | JPSthrow _
	  | JPSvar_decl _
	  | JPSexpr _ -> assert false (* TODO *)

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

let rec class_fields l acc =
  match l with
    | [] -> acc
    | JPFmethod _ :: rem -> assert false
    | JPFmethod_spec(req,behs) :: JPFmethod(head,body) :: rem ->
	let id, ret_ty, params = 
	  method_header head.method_return_type head.method_declarator 
	in
	let req = Option_misc.map (assertion params) req in
	let params_result = 
	  match ret_ty with
	    | None -> params
	    | Some t ->
		let vi = var t "\\result" in ("\\result",vi)::params
	in
	let behs = List.map
	  (fun (id,(assumes,assigns,ensures)) ->
	     (id,Option_misc.map (assertion params) assumes,
	      Option_misc.map (fun _ -> assert false (* TODO *)) assigns,
	      assertion params_result ensures))
	  behs
	in
	let body = Option_misc.map (statements params) body in
	class_fields rem ((id,params,ret_ty,req,behs,body) :: acc)
    | JPFmethod_spec _ :: _ ->
	typing_error (assert false) "out of place method specification"
    | JPFinvariant _ :: rem ->  assert false (* TODO *)
    | JPFannot _ :: _ -> assert false (* not possible after 2nd parsing *)
    | JPFstatic_initializer _ ::rem
    | JPFvariable _ :: rem
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
