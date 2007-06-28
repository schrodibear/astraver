
open Java_env
open Java_ast
open Java_tast
open Format
open Java_pervasives

exception Typing_error of Loc.position * string

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter


(******************************

Typing level 0: extract types (logic, Java classes, Java interfaces)

**********************************)

let class_table = Hashtbl.create 17 

let new_class_info id =
  let ci =
    { class_info_name = id ;
      class_info_fields = [];
      class_info_methods = [];
    }
  in
  Hashtbl.add class_table id ci;
  ci

let get_type_decl d = 
    match d with
    | JPTclass c -> 
	(*
	  class_modifiers : modifiers;
	  class_name : identifier;
	  class_extends : qualified_ident option;
	  class_implements : qualified_ident list;
	  class_fields : field_declaration list
	*)
	let _ci = new_class_info (snd c.class_name) in ()
    | JPTinterface i -> assert false (* TODO *)
    | JPTannot(loc,s) -> assert false
    | JPTaxiom((loc,id),e) -> ()
    | JPTlogic_type_decl _ -> assert false (* TODO *)
    | JPTlogic_reads _ -> assert false (* TODO *)
    | JPTlogic_def((loc,id),ret_type,params,body) -> ()	

let get_types cu =
  assert (cu.cu_package = []); (* TODO *)
  assert (cu.cu_imports = []); (* TODO *)
  List.iter get_type_decl cu.cu_type_decls


(******************************

Typing level 1: extract prototypes 
  (logic functions profiles, Field types of Java classes and interfaces, profiles of methods and constructors)

**********************************)

let search_for_class id =
  try
    Hashtbl.find class_table id 
  with
      Not_found -> assert false

let rec type_type ty =
  match ty with
    | Base_type t -> JTYbase t
    | Type_name qid -> 
	begin
	  match qid with
	    | [(loc,id)] ->
		let ci = search_for_class id in
		JTYclass(false,ci)
	    | _ -> assert false (* TODO *)
	end
    | Array_type_expr t -> 
	let ty = type_type t in
	JTYarray ty

let rec var_type_and_id ty id =
  match id with
    | Simple_id id -> ty,id
    | Array_id id -> 
	let ty,id = var_type_and_id ty id in
	JTYarray(ty),id


(* variables *)

let var_tag_counter = ref 0

let new_var ty id =
  incr var_tag_counter;
  let vi = {
    java_var_info_tag = !var_tag_counter;
    java_var_info_name = id;
    java_var_info_final_name = id;
    java_var_info_type = ty;
    java_var_info_assigned = false;
  }
  in vi


(* fields *)

let fields_table = Hashtbl.create 97

let field_tag_counter = ref 0

let new_field ~is_static ~is_final ci ty id =
  incr field_tag_counter;
  let fi = {
    java_field_info_tag = !field_tag_counter;
    java_field_info_name = id;
    java_field_info_type = ty;
    java_field_info_class = ci;
    java_field_info_is_static = is_static;
    java_field_info_is_final = is_final;
  }
  in fi

(* methods *)

let methods_env = Hashtbl.create 97

let method_tag_counter = ref 0

let new_method_info ~is_static id ty pars =
  incr method_tag_counter;
  {
    method_info_tag = !method_tag_counter;
    method_info_name = id;
    method_info_trans_name = id;
    method_info_has_this = None;
    method_info_parameters = pars;
    method_info_return_type = ty;
    method_info_calls = [];
    method_info_is_static = is_static;
  }

let type_param p =
  let rec get_type p =
    match p with
      | Simple_parameter(ty,(loc,id)) -> (type_type ty, id)
      | Array_parameter x -> 
	  let (t,i) = get_type x in
	  (JTYarray t,i)
  in
  let (t,i) = get_type p in new_var t i

let rec method_header retty mdecl =
  match mdecl with
    | Simple_method_declarator(id,l) -> 
	id,(Option_misc.map type_type retty), List.map type_param l
    | Array_method_declarator d -> 
	let id,t,l = method_header retty d in
	match t with
	  | Some t -> id,Some (JTYarray t),l
	  | None -> typing_error (fst id) "invalid type void array"

let get_field_prototypes ci acc d =
  match d with
    | JPFvariable vd -> 
	(*
	vd.variable_modifiers : modifiers ;
	vd.variable_type : type_expr ;
	vd.variable_decls : variable_declarator list }
	*)
	let ty = type_type vd.variable_type in
	let is_static = List.mem `STATIC vd.variable_modifiers in
	let is_final = List.mem `FINAL vd.variable_modifiers in
	List.fold_left
	  (fun acc vd -> 
	     let ty',(loc,id) = var_type_and_id ty vd.variable_id in
	     let fi = new_field ~is_static ~is_final ci ty' id in	     
	     Hashtbl.add fields_table fi.java_field_info_tag 
	       (fi,vd.variable_initializer,None);
	     fi::acc
	  ) acc vd.variable_decls
    | _ -> acc

let rec get_method_prototypes ci acc env l =
  match l with
    | [] -> acc
    | JPFmethod _ :: rem -> assert false
    | JPFmethod_spec(req,behs) :: JPFmethod(head,body) :: rem ->
	let id, ret_ty, params = 
	  method_header head.method_return_type head.method_declarator 
	in
	let is_static = List.mem `STATIC head.method_modifiers in
	let mi = new_method_info ~is_static (snd id) ret_ty params in
	Hashtbl.add methods_env mi.method_info_tag (mi,req,behs,body)
	  (* { mt_method_info = mi;
	    mt_requires = req;
	    mt_behaviors = behs;
	    mt_body = body } *);
	get_method_prototypes ci (mi::acc) env rem 
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
	    class_methods env rem *)
    | JPFmethod_spec _ :: _ ->
	typing_error (assert false) "out of place method specification"
    | JPFinvariant(id,e) :: rem ->
(*
	let local_env =
(*
	  if List.mem `STATIC head.method_modifiers then [] else
*)
	    let vi = var (JTYclass(true,ci)) "this" in 
	    ("this",vi)::env
	in
	let p = assertion local_env e in
	Hashtbl.add invariants_table id p;
*)
	get_method_prototypes ci acc env rem 
    | JPFannot _ :: _ -> assert false (* not possible after 2nd parsing *)
    | JPFstatic_initializer _ ::rem -> assert false (* TODO *)
    | JPFvariable vd :: rem -> 
	get_method_prototypes ci acc env rem 
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
	let ci = search_for_class (snd c.class_name) in	  
	let fields = List.fold_left (get_field_prototypes ci) [] c.class_fields in
	ci.class_info_fields <- fields;
	let methods = get_method_prototypes ci [] [] c.class_fields in
	ci.class_info_methods <- methods;
    | JPTinterface i -> assert false (* TODO *)
    | JPTannot(loc,s) -> assert false
    | JPTaxiom((loc,id),e) -> ()
    | JPTlogic_type_decl _ -> assert false (* TODO *)
    | JPTlogic_reads _ -> assert false (* TODO *)
    | JPTlogic_def((loc,id),ret_type,params,body) -> ()
	


let get_prototypes cu =
  assert (cu.cu_package = []); (* TODO *)
  assert (cu.cu_imports = []); (* TODO *)
  List.iter type_decl cu.cu_type_decls


(*******************************

Typing level 2: extract bodies
  (logic functions definitions, axioms,
   field initializers, method and constructors bodies)

**********************************)

let imported_packages = ref [ "java.lang" ]

let static_fields = Hashtbl.create 17

let invariants_table = Hashtbl.create 17

let axioms_table = Hashtbl.create 17




let string_of_base_type t =
  match t with
    | Tnull -> "(nulltype)"
    | Tunit -> "unit"
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


let rec print_type fmt t =
  match t with
    | JTYbase t -> fprintf fmt "%s" (string_of_base_type t)
    | JTYarray t -> fprintf fmt "%a[]" print_type t
    | JTYclass(_,c) -> fprintf fmt "%s" c.class_info_name




(* methods *)

type method_table_info =
    { mt_method_info : Java_env.method_info;
      mt_requires : Java_tast.assertion option;
      mt_behaviors : (Java_ast.identifier * 
			Java_tast.assertion option * 
			Java_tast.term list option * 
			Java_tast.assertion) list ;
      mt_body : Java_tast.block option;
    }

  

(* logic funs *)

type logic_body =
  | JAssertion of assertion
  | JTerm of term
(*
  | JReads of location list
*)

let logics_table = Hashtbl.create 97
let logics_env = Hashtbl.create 97

let logic_tag_counter = ref 0

let logic_info id ty pars =
  incr logic_tag_counter;
  { java_logic_info_tag = !logic_tag_counter;
    java_logic_info_name = id;
    java_logic_info_parameters = pars;
    java_logic_info_result_type = ty;
    java_logic_info_calls = [];
  }
    


let lit l =
  match l with
    | Integer s -> integer_type,l
    | Char s -> assert false (* TODO *)
    | String s -> assert false (* TODO *)
    | Bool b -> boolean_type,l
    | Float s -> real_type,l
    | Null -> null_type,l

let int_type t =
  match t with
    | JTYbase t -> 
	begin
	  match t with
	    | Tchar | Tshort | Tbyte | Tint -> t
	    | Tlong | Tdouble | Tfloat | Treal | Tinteger
	    | Tboolean | Tnull | Tunit -> raise Not_found
	end
    | _ -> raise Not_found

let is_numeric t =
  match t with
    | JTYbase t -> 
	begin
	  match t with
	    | Tinteger | Tshort | Tbyte | Tint | Tlong -> true
	    | Treal | Tdouble | Tfloat -> true
	    | Tchar -> assert false (* TODO *)
	    | Tboolean | Tnull | Tunit -> false
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


let is_object t =
  match t with
    | JTYbase t -> t=Tnull
    | _ -> true

let lub_object_types t1 t2 = Tnull
  
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

let subbasetype t1 t2 =
  match t1,t2 with
    | (Tint|Tshort|Tchar|Tbyte|Tlong|Tinteger), Tinteger -> true
    | (Tfloat|Tdouble|Treal), Treal -> true
    | (Tshort|Tchar|Tbyte|Tint), Tint -> true
    | (Tshort|Tbyte), Tshort -> true
    | Tchar, Tchar -> true
    | _ -> false

(*
let subtype t1 t2 =
  match t1,t2 with
    | JTYbase t1, JTYbase t2 -> subbasetype t1 t2
    | _ -> assert false (* TODO *)
*)

let compatible_base_types t1 t2 = true

let rec compatible_types t1 t2 =
  match t1,t2 with
    | JTYbase t1, JTYbase t2 -> compatible_base_types t1 t2
    | JTYarray t1, JTYarray t2 -> compatible_types t1 t2
    | JTYclass(_,c1), JTYclass(_,c2) -> assert false
    | JTYclass (_, c), JTYbase Tnull 
    | JTYbase Tnull, JTYclass (_, c) -> assert false
    | JTYarray t1, JTYbase Tnull 
    | JTYbase Tnull, JTYarray t1 -> assert false
    | JTYclass _, JTYarray _ -> assert false
    | JTYclass _, JTYbase _ -> assert false
    | JTYarray _, JTYclass _ -> assert false
    | JTYarray _, JTYbase _ -> assert false
    | JTYbase _, JTYarray _ -> false
    | JTYbase _, JTYclass _ -> assert false


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


let get_this loc env =
  try 
    List.assoc "this" env 
  with Not_found -> 
    typing_error loc "this undefined in this context"

let term_var loc vi =
  { java_term_node = JTvar vi; 
    java_term_type = vi.java_var_info_type;
    java_term_loc = loc }

let lookup_field ci id =
  let rec list_assoc_field_name id l =
    match l with
      | [] -> raise Not_found
      | fi::r ->
	  if fi.java_field_info_name = id then fi
	  else list_assoc_field_name id r
  in
  list_assoc_field_name id ci.class_info_fields


type classified_name =
  | TermName of term
  | ClassName of java_class_info

let rec classify_name env name =
  match name with
    | [] -> assert false
    | [(loc,id)] ->
	begin
	  (* look for a local var of that name *)
	  try
	    let vi = List.assoc id env in
	    TermName { 
	      java_term_node = JTvar vi; 
	      java_term_type = vi.java_var_info_type;
	      java_term_loc = loc 
	    }
	  with Not_found -> 
	    (* look for a field of that name in class this *)
	    try
	      let this = List.assoc "this" env in	    
	      match this.java_var_info_type with
		| JTYclass(_,ci) ->
		    begin
		      try 
			let fi = lookup_field ci id in
			let facc =
			  if fi.java_field_info_is_static then
			    JTstatic_field_access(ci,fi)
			  else
			    JTfield_access(term_var loc this,fi)
			in
			TermName {
			  java_term_node = facc;
			  java_term_type = fi.java_field_info_type;
			  java_term_loc = loc
			}
		      with Not_found ->
			typing_error loc "unknown identifier %s" id
		    end
		| _ -> assert false (* impossible *)
	    with Not_found ->
	      (* look for a class of that name *)
	      try 
		let ci = search_for_class id in ClassName ci
	      with Not_found ->
		assert false (* TODO *)
	end		
    | (loc,id)::n ->
	match classify_name env n with
	  | TermName t -> 
	      begin
		match t.java_term_type with
		  | JTYclass(_,c) ->
		      begin
			try
			  let fi = lookup_field c id in
			  TermName { 
			    java_term_loc = loc;
			    java_term_type = fi.java_field_info_type ;
			    java_term_node = JTfield_access(t,fi)
			  }
			with Not_found ->
			  typing_error loc 
			    "no such field in this class"
		      end
		  | JTYarray _ -> 
		      if id="length" then
			TermName {
			  java_term_loc = loc;
			  java_term_type = integer_type;
			  java_term_node = JTarray_length(t)
			}
		      else
			typing_error loc 
			  "no such field in array type"
		  | JTYbase _ ->
		      typing_error t.java_term_loc 
			"not a class type" 
	      end
	  | ClassName ci ->
	      	try
		  let fi = lookup_field ci id in
		  if fi.java_field_info_is_static then
		    TermName { 
		      java_term_loc = loc;
		      java_term_type = fi.java_field_info_type ;
		      java_term_node = JTstatic_field_access(ci,fi)
		    }
		  else
		    typing_error loc 
		      "field %s is not static" id

		with Not_found ->
		  typing_error loc 
		    "no such field in class %s" ci.class_info_name
		
  
let rec term env e =
  let ty,tt =
    match e.java_pexpr_node with
      | JPElit l -> 
	  let ty,l = lit l in ty,(JTlit l)
      | JPEname n ->
	  begin
	    match classify_name env n with
	      | TermName t ->
		  t.java_term_type, t.java_term_node
	      | ClassName _ ->
		  typing_error e.java_pexpr_loc
		    "term expected, got a class"
	  end

      | JPEresult -> 
	  begin
	    try
	      let vi = List.assoc "\\result" env in
	      vi.java_var_info_type,JTvar vi
	    with Not_found -> 
	      typing_error e.java_pexpr_loc "\\result undefined in this context"
	  end
      | JPEthis -> 
	  let vi = get_this e.java_pexpr_loc env in
	  vi.java_var_info_type, JTvar vi
      | JPEbin (e1, op, e2) -> 
	  let te1 = term env e1 and te2 = term env e2 in 
	  make_logic_bin_op e.java_pexpr_loc op 
	    te1.java_term_type te1 te2.java_term_type te2
      | JPEquantifier (q, ty, idl, e)-> 
	  typing_error e.java_pexpr_loc
	    "quantified formulas not allowed in term position"
      | JPEold e1 -> 
	  let te1 = term env e1 in te1.java_term_type,JTold te1	
      | JPEinstanceof (_, _)-> assert false (* TODO *)
      | JPEcast (_, _)-> assert false (* TODO *)
      | JPEarray_access (e1, e2)-> 
	  let te1 = term env e1 and te2 = term env e2 in 
	  begin
	    match te1.java_term_type with
	      | JTYarray t ->
		  if is_numeric te2.java_term_type then
		    t, JTarray_access(te1,te2)
		  else
		    typing_error e2.java_pexpr_loc
		      "integer expected"	
	      | _ ->
		  typing_error e1.java_pexpr_loc
		    "not an array"	
	  end
      | JPEnew_array _-> assert false (* TODO *)
      | JPEnew (_, _)-> assert false (* TODO *)
      | JPEsuper_call (_, _)-> assert false (* TODO *)
      | JPEcall (e1, (loc,id), args)-> 
	  begin
	    match e1 with
	      | None -> 
		  begin 
		    try 
		      let fi = Hashtbl.find logics_env id in
		      let args = List.map (term env) args in		      
		      (* TODO: check arg types *)
		      match fi.java_logic_info_result_type with
			| None ->
			    typing_error loc 
			      "logic symbol `%s' is a predicate" id
			| Some t -> t,JTapp(fi,args)
		    with Not_found ->
		      typing_error loc "logic function `%s' not found" id
		  end		
	      | Some e -> 
		  typing_error e.java_pexpr_loc "method calls not allowed in annotations"
	  end
      | JPEfield_access fa -> 
	  begin
	    match fa with
	      | Primary_access (e1, f) -> 
		  let te1 = term env e1 in
		  begin
		    match te1.java_term_type with
		      | JTYclass(_,ci) ->
			  begin
			    try
			      let fi = lookup_field ci (snd f) in
			      fi.java_field_info_type,JTfield_access(te1,fi)
			    with
				Not_found ->
				  typing_error e1.java_pexpr_loc
				    "not such field"
			  end
		      | _ ->
			  typing_error e1.java_pexpr_loc
			    "not a class"
		  end
		    
	      | Super_access _ -> assert false (* TODO *)
	  end	
      | JPEif (_, _, _)-> assert false (* TODO *)
      | JPEassign_array (_, _, _, _)-> assert false (* TODO *)
      | JPEassign_field (_, _, _)-> assert false (* TODO *)
      | JPEassign_name (_, _, _)-> assert false (* TODO *)
      | JPEincr (_, _)-> assert false (* TODO *)
      | JPEun (_, _)-> assert false (* TODO *)

  in { java_term_node = tt; 
       java_term_type = ty;
       java_term_loc = e.java_pexpr_loc }


let make_predicate_bin_op loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JAbin(e1,t,op,e2)
	else typing_error loc "numeric types expected for >,<,>= and <="
    | Beq | Bne ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JAbin(e1,t,op,e2)
	else 
	  if is_object t1 && is_object t2 then
	    let t = lub_object_types t1 t2 in
	    JAbin(e1,t,op,e2)
	  else 
	    typing_error loc "numeric or object types expected for == and !="
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand|Bimpl|Bor|Band|Biff ->
	assert false (* TODO *)
    | Bsub | Badd | Bmod | Bdiv | Bmul ->
	typing_error loc "operator +,-,*, / and %% is not a predicate"

let connective a1 op a2 =
  match op with
    | Band -> JAand(a1,a2)
    | Bor -> JAor(a1,a2)
    | Bimpl -> JAimpl(a1,a2)
    | Biff -> JAiff(a1,a2)
    | _ -> assert false

let rec assertion env e =
  let ta =
  match e.java_pexpr_node with
    | JPElit (Bool true) -> JAtrue
    | JPElit (Bool false) -> JAfalse
    | JPElit _ -> 
	typing_error e.java_pexpr_loc 
	  "this literal is not a boolean expression"
    | JPEbin(e1, ((Band | Bor | Bimpl | Biff) as op) , e2) ->
	let te1 = assertion env e1
	and te2 = assertion env e2
	in connective te1 op te2
    | JPEbin(e1, op, e2) -> 
	let te1 = term env e1 and te2 = term env e2 in 
	make_predicate_bin_op e.java_pexpr_loc op 
	  te1.java_term_type te1 te2.java_term_type te2
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
    | JPEcall (None, (loc,id), args)-> 
	begin
	  try
	    let fi = Hashtbl.find logics_env id in
	    let tl =
	      try
		List.map2
		  (fun vi e ->
		     let ty = vi.java_var_info_type in
		     let te = term env e in
		     if compatible_types te.java_term_type ty then te
		     else
		       typing_error e.java_pexpr_loc 
			 "type %a expected" 
			 print_type ty) 
		  fi.java_logic_info_parameters args
	      with  Invalid_argument _ ->
		typing_error e.java_pexpr_loc 
		  "wrong number of arguments for %s" id
	    in
	    JAapp(fi, tl)
		 
	  with
	      Not_found ->
		typing_error e.java_pexpr_loc 
		  "unknown predicate `%s'" id
	end
    | JPEcall (Some _, _, _)-> 
	typing_error e.java_pexpr_loc 
	  "method calls not allowed in assertion"	
    | JPEfield_access _-> assert false (* TODO *)
    | JPEif (_, _, _)-> assert false (* TODO *)
    | JPEassign_array (_, _, _, _)-> assert false (* TODO *)
    | JPEassign_field (_, _, _)-> assert false (* TODO *)
    | JPEassign_name (_, _, _)-> assert false (* TODO *)
    | JPEname _-> assert false (* TODO *)
    | JPEincr (_, _)-> assert false (* TODO *)
    | JPEun (_, _)-> assert false (* TODO *)
    | JPEresult -> 
	begin
	  try
	    let vi = List.assoc "\\result" env in
	    match vi.java_var_info_type with
	      | JTYbase Tboolean ->
		  JAbool_expr {
		    java_term_node = JTvar vi;
		    java_term_type = vi.java_var_info_type;
		    java_term_loc = e.java_pexpr_loc
		  }
	      | _ ->
		  typing_error e.java_pexpr_loc "\\result is not boolean"

	  with Not_found -> 
	    typing_error e.java_pexpr_loc "\\result undefined in this context"
	end

    | JPEthis -> 
	typing_error e.java_pexpr_loc 
	  "'this' is not a boolean expression"

  in { java_assertion_node = ta;
       java_assertion_loc = e.java_pexpr_loc }

and make_quantified_formula loc q ty idl env e : assertion =
  match idl with
    | [] -> assertion env e
    | id::r ->
	let tyv, (loc,n) = var_type_and_id ty id in
	let vi = new_var tyv n in
	let f = make_quantified_formula loc q ty r ((n,vi)::env) e 
	in
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

let expr_var loc vi =
  { java_expr_node = JEvar vi; 
    java_expr_type = vi.java_var_info_type;
    java_expr_loc = loc }

let rec expr_of_term t =
  let n =
    match t.java_term_node with
      | JTvar vi -> JEvar vi
      | JTold _ -> assert false (* TODO *)
      | JTfield_access(t, fi) -> 
	  JEfield_access(expr_of_term t,fi)
      | JTstatic_field_access(ci, fi) -> 
	  JEstatic_field_access(ci,fi)
      | JTarray_length(t) -> 
	  JEarray_length(expr_of_term t)
      | JTarray_access(t1,t2) -> 
	  JEarray_access(expr_of_term t1, expr_of_term t2)
      | JTapp (_, _) -> assert false (* TODO *)
      | JTbin (_, _, _, _) -> assert false (* TODO *)
      | JTlit _ -> assert false (* TODO *)
  in
  { java_expr_loc = t.java_term_loc;
    java_expr_type = t.java_term_type;
    java_expr_node = n ;
  }

let lookup_method ci id arg_types = assert false (* TODO *)

let rec expr env e =
  let ty,te = 
    match e.java_pexpr_node with
      | JPElit l -> let t,l = lit l in t,(JElit l)
      | JPEname n -> 
	  begin
	    match classify_name env n with
	      | TermName t ->
		  let e = expr_of_term t in
		  e.java_expr_type, e.java_expr_node
	      | ClassName _ ->
		  typing_error e.java_pexpr_loc
		    "expression expected, got a class"
	  end
      | JPEthis -> 
	  let vi = get_this e.java_pexpr_loc env in
	  vi.java_var_info_type, JEvar vi
      | JPEinstanceof (_, _)-> assert false (* TODO *)
      | JPEcast (_, _)-> assert false (* TODO *)
      | JPEarray_access (e1, e2)-> 
	  let te1 = expr env e1 and te2 = expr env e2 in 
	  begin
	    match te1.java_expr_type with
	      | JTYarray t ->
		  if is_numeric te2.java_expr_type then
		    t, JEarray_access(te1,te2)
		  else
		    typing_error e2.java_pexpr_loc
		      "integer expected"	
	      | _ ->
		  typing_error e1.java_pexpr_loc
		    "not an array"	
	  end
      | JPEnew_array _-> assert false (* TODO *)
      | JPEnew (_, _)-> assert false (* TODO *)
      | JPEsuper_call (_, _)-> assert false (* TODO *)
      | JPEcall (e1, id, args)-> 
	  let args = List.map (expr env) args in
	  let arg_types = List.map (fun e -> e.java_expr_type) args in
	  begin
	    match e1 with
	      | None -> 
		  let vi = get_this e.java_pexpr_loc env in
		  begin match vi.java_var_info_type with
		    | JTYclass(_,ci) ->
			let mi = lookup_method ci id arg_types in
			begin
			  match mi.method_info_return_type with
			    | None -> unit_type,JEcall(None,mi,args)
			    | Some t -> t,JEcall(None,mi,args)
			end
		    | _ -> assert false
		  end		
	      | Some e -> assert false (* TODO *)
	  end
      | JPEfield_access _-> assert false (* TODO *)
      | JPEif (_, _, _)-> assert false (* TODO *)
      | JPEassign_array (e1, e2, op, e3)-> 
	  let te1 = expr env e1 
	  and te2 = expr env e2 
	  and te3 = expr env e3 
	  in 
	  begin
	    match te1.java_expr_type with
	      | JTYarray t ->
		  if is_numeric te2.java_expr_type then
		    if compatible_types t te3.java_expr_type then
		      t, JEassign_array_op(te1,te2,op,te3)
		    else
		    typing_error e3.java_pexpr_loc
		      "type `%a' expected" print_type t	
		  else
		    typing_error e2.java_pexpr_loc
		      "integer expected"	
	      | _ ->
		  typing_error e1.java_pexpr_loc
		    "not an array"	
	  end
	  
      | JPEassign_field (_, _, _)-> assert false (* TODO *)
      | JPEassign_name (n, op, e1)-> 
	  begin
	    let te = expr env e1 in
	    match classify_name env n with
	      | TermName t ->
		  begin
		    match t.java_term_node with
		      | JTvar vi ->
			  if compatible_types te.java_expr_type vi.java_var_info_type
			  then 
			    if op = Beq then
			      (vi.java_var_info_type,
			       JEassign_local_var(vi,te))
			    else 
			      (vi.java_var_info_type,
			       JEassign_local_var_op(vi,op,te))
			  else
			    typing_error e.java_pexpr_loc "type %a expected, got %a" 
			      print_type vi.java_var_info_type 
			      print_type te.java_expr_type
		      | JTfield_access(t,fi) ->
			  if compatible_types te.java_expr_type 
			    fi.java_field_info_type
			  then 
			    if op = Beq then
			      (fi.java_field_info_type,
			       JEassign_field(expr_of_term t,fi,te))
			    else 
			      (fi.java_field_info_type,
			       JEassign_field_op(expr_of_term t,fi,op,te))
			  else
			    typing_error e.java_pexpr_loc "type %a expected, got %a" 
			      print_type fi.java_field_info_type 
			      print_type te.java_expr_type
		      | _ -> assert false (* TODO *)
		  end
	      | ClassName _ ->
		  typing_error e.java_pexpr_loc
		    "lvalue expected, got a class"
	  end
(*	    
	    match n with
	      | [] -> assert false
	      | [(loc,id)] ->
		  begin
		    try
		      match List.assoc id env with
			| Local_variable_entry vi -> 
			    if compatible_types te.java_expr_type vi.java_var_info_type
			    then 
			      if op = Beq then
				(vi.java_var_info_type,
				 JEassign_local_var(vi,te))
			      else 
				(vi.java_var_info_type,
			         JEassign_local_var_op(vi,op,te))
			    else
			      typing_error loc "type %a expected, got %a" 
				print_type vi.java_var_info_type 
				print_type te.java_expr_type
			| Instance_variable_entry fi ->
			    let this = get_this_expr loc env in
			    if compatible_types te.java_expr_type 
			      fi.java_field_info_type
			    then 
			      if op = Beq then
				fi.java_field_info_type,
				JEassign_field(this,fi,te)
			      else 
				fi.java_field_info_type,
				JEassign_field_op(this,fi,op,te)			    else
			      typing_error loc "type %a expected, got %a" 
				print_type fi.java_field_info_type 
				print_type te.java_expr_type
			    
		    with Not_found -> 
		      typing_error loc "unbound identifier %s" id
		  end
	      | (loc,id)::r ->
		  begin
		    match classify_name env r with
		      | TermName t ->
			  begin
			    match t.java_term_type with
			      | JTYclass(_,c) ->
				  begin
				    try
				      let fi = 
					list_assoc_field_name id 
					  c.class_info_fields
				      in
				      fi.java_field_info_type,
				      JEassign_field(expr_of_term t,fi,te)
				    with Not_found ->
				      typing_error loc 
					"no such field in this class"
				  end
			      | JTYarray _ -> 
				  assert false (* TODO: .length *)
			      | JTYbase _ ->
				  typing_error t.java_term_loc 
				    "not a class type" 
			  end
		  end
	  end
*)
      | JPEincr (op, e)-> 
	  let te = expr env e in 
	  begin
	    match te.java_expr_node with
	      | JEvar v ->
		  te.java_expr_type,JEincr_local_var(op,v)
	      | _ -> assert false (* TODO *)
	  end	  
      | JPEun (_, _)-> assert false (* TODO *)
      | JPEbin (e1, op, e2) -> 
	  let te1 = expr env e1 and te2 = expr env e2 in 
	  let t,e = make_bin_op e.java_pexpr_loc op 
		      te1.java_expr_type te1 te2.java_expr_type te2 in
	  JTYbase t,e
	       (* only in terms *)
      | JPEquantifier (_, _, _, _)
      | JPEold _
      | JPEresult -> 
	  typing_error e.java_pexpr_loc "not allowed in expressions"

  in { java_expr_loc = e.java_pexpr_loc;
	java_expr_type = ty;
	java_expr_node = te; }


			   
let type_initializer env ty i =
  match ty,i with
    | JTYbase t, Simple_initializer e ->
	let te = expr env e in	
	if compatible_types ty te.java_expr_type then JIexpr te
	else
	  typing_error e.java_pexpr_loc "type %a expected, got %a"
	    print_type ty print_type te.java_expr_type
    | _ -> assert false (* TODO *)

(* statements *)

let variable_declaration env vd =
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
  List.fold_right
      (fun ((loc,id),ty,i) (env,decls)->
	 let vi = new_var ty id in		     
	 (id,vi)::env,(vi,i)::decls)
      l (env,[])

let rec statement env s =
  let s' =
    match s.java_pstatement_node with
      | JPSskip -> JSskip
      | JPSif (e, s1, s2) ->
	  let te = expr env e in
	  let ts1 = statement env s1 in
	  let ts2 = statement env s2 in
	  if is_boolean te.java_expr_type then	    
	    JSif(te,ts1,ts2)
	  else
	    typing_error e.java_pexpr_loc "boolean expected"
      | JPSloop_annot (inv, dec) -> assert false
      | JPSannot (_, _)-> assert false (* TODO *)
      | JPSghost_local_decls d -> assert false (* TODO *)
      | JPSghost_statement e
      | JPSexpr e -> 
	  let te = expr env e in JSexpr te
      | JPSassert(id,a) ->
	  let ta = assertion env a in
	  JSassert(Option_misc.map snd id,ta)
      | JPSsynchronized (_, _)-> assert false (* TODO *)
      | JPSblock l -> (block env l).java_statement_node
      | JPSswitch (e, l)-> 
	  let te = expr env e in
	  (* JSL, p289: switch expr must be char, byte, short or int *)
	  begin
	    try 
	      let t = int_type te.java_expr_type in
	      JSswitch(te,List.map (switch_case env t) l)
	    with Not_found ->
	      typing_error e.java_pexpr_loc "char, byte, short or int expected"
	  end
      | JPStry (_, _, _)-> assert false (* TODO *)
      | JPSfor_decl (_, _, _, _)-> assert false (* TODO *)
      | JPSfor (_, _, _, _)-> assert false (* TODO *)
      | JPSdo (_, _)-> assert false (* TODO *)
      | JPSwhile (_, _)-> assert false (* TODO *)
      | JPSlabel (_, _)-> assert false (* TODO *)
      | JPScontinue _-> assert false (* TODO *)
      | JPSbreak l -> JSbreak (Option_misc.map snd l)
      | JPSreturn None -> assert false (* TODO *)
      | JPSreturn (Some e) -> 
	  begin
	    try
	      let te = expr env e in 
	      let vi = List.assoc "\\result" env in
	      if compatible_types te.java_expr_type vi.java_var_info_type then
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
	  
  in 
  { java_statement_loc = s.java_pstatement_loc ;
    java_statement_node = s' }


and statements env b =
  match b with
    | [] -> []
    | s :: rem ->
	match s.java_pstatement_node with
	  | JPSskip -> statements env rem
	  | JPSghost_local_decls vd 
	  | JPSvar_decl vd -> 
	      let env,decls = variable_declaration env vd in
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
	      begin
		match rem with
		  | { java_pstatement_node = JPSwhile(e,s) ;
		      java_pstatement_loc = loc } :: rem -> 
		      let inv = assertion env inv in
		      let dec = term env dec in
		      let e = expr env e in
		      let s = statement env s in
		      { java_statement_node = JSwhile(e,inv,dec,s);
			java_statement_loc = loc } :: statements env rem
		  | { java_pstatement_node = JPSfor_decl(vd,e,sl,s) ;
		      java_pstatement_loc = loc } :: rem -> 
		      let env,decls = variable_declaration env vd in
		      let inv = assertion env inv in
		      let dec = term env dec in
		      let e = expr env e in
		      let sl = List.map (expr env) sl in
		      let s = statement env s in
		      { java_statement_node = JSfor_decl(decls,e,inv,dec,sl,s);
			java_statement_loc = loc } :: statements env rem		  | _ -> assert false
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

and switch_case env t (labels,b) =
  (List.map (switch_label env t) labels, statements env b)

and switch_label env t = function
  | Default -> Default
  | Case e ->
      let te = expr env e in
      match te.java_expr_type with
	| JTYbase t' when subbasetype t' t -> Case te 
	| _ ->
	     typing_error e.java_pexpr_loc "type `%s' expected"
		(string_of_base_type t)

(* methods *)

(*
let type_param p =
  let rec get_type p =
    match p with
      | Simple_parameter(ty,(loc,id)) -> (type_type ty, id)
      | Array_parameter x -> 
	  let (t,i) = get_type x in
	  (JTYarray t,i)
  in
  let (t,i) = get_type p in new_var t i

let rec method_header retty mdecl =
  match mdecl with
    | Simple_method_declarator(id,l) -> 
	id,(Option_misc.map type_type retty), List.map type_param l
    | Array_method_declarator d -> 
	let id,t,l = method_header retty d in
	match t with
	  | Some t -> id,Some (JTYarray t),l
	  | None -> typing_error (fst id) "invalid type void array"
*)

let assigns env a = 
  term env a 
  

let behavior env env_result (id,b) = 
  let env_ensures = 
    match b.java_pbehavior_throws with
      | None -> env_result
      | Some(c,id) -> assert false (* TODO *)
  in
  (id,
   Option_misc.map (assertion env) b.java_pbehavior_assumes,
   Option_misc.map (List.map (assigns env)) b.java_pbehavior_assigns,
   assertion env_ensures b.java_pbehavior_ensures)
	

let methods_table = Hashtbl.create 97


let type_method_spec_and_body ci mi =
  let (_,req,behs,body) = 
    try
      Hashtbl.find methods_env mi.method_info_tag 
    with Not_found -> assert false
  in
  let local_env =
    if mi.method_info_is_static then [] else
      let vi = new_var (JTYclass(true,ci)) "this" in
      mi.method_info_has_this <- Some vi;
      [("this",vi)]
  in
  let local_env = 
    List.fold_left
      (fun acc vi -> 
	 (vi.java_var_info_name,vi)::acc)
      local_env mi.method_info_parameters
  in
  let req = Option_misc.map (assertion local_env) req in
  let env_result =
    match mi.method_info_return_type with
      | None -> local_env
      | Some t ->
	  let vi = new_var t "\\result" in 
	  ("\\result",vi)::local_env
  in
  let behs = List.map (behavior local_env env_result) behs in
  let body = Option_misc.map (statements env_result) body in
  Hashtbl.add methods_table mi.method_info_tag 
    { mt_method_info = mi;
      mt_requires = req;
      mt_behaviors = behs;
      mt_body = body } 


(*
  match l with
    | [] -> ()
    | JPFmethod _ :: rem -> assert false
    | JPFmethod_spec(req,behs) :: JPFmethod(head,body) :: rem ->
	let id, ret_ty, params = 
	  method_header head.method_return_type head.method_declarator 
	in
	let mi = new_method_info (snd id) ret_ty params in
	let local_env =
	  if List.mem `STATIC head.method_modifiers then [] else
	    let vi = var (JTYclass(true,ci)) "this" in
	    mi.method_info_has_this <- Some vi;
	    ("this",vi)::env
	in
	let local_env = 
	  List.fold_left
	    (fun acc vi -> 
	       (vi.java_var_info_name,vi)::acc)
	    local_env params
	in
	let req = Option_misc.map (assertion local_env) req in
	let env_result =
	  match ret_ty with
	    | None -> local_env
	    | Some t ->
		let vi = var t "\\result" in 
		("\\result",vi)::local_env
	in
	let behs = List.map (behavior local_env env_result) behs in
	let body = Option_misc.map (statements env_result) body in
	Hashtbl.add methods_table mi.method_info_tag 
	  { mt_method_info = mi;
	    mt_requires = req;
	    mt_behaviors = behs;
	    mt_body = body };
	class_methods ci env rem 
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
	    class_methods env rem *)
    | JPFmethod_spec _ :: _ ->
	typing_error (assert false) "out of place method specification"
    | JPFinvariant(id,e) :: rem ->
	let local_env =
(*
	  if List.mem `STATIC head.method_modifiers then [] else
*)
	    let vi = var (JTYclass(true,ci)) "this" in 
	    ("this",vi)::env
	in
	let p = assertion local_env e in
	Hashtbl.add invariants_table id p;
	class_methods ci env rem 
    | JPFannot _ :: _ -> assert false (* not possible after 2nd parsing *)
    | JPFstatic_initializer _ ::rem -> assert false (* TODO *)
    | JPFvariable vd :: rem -> 
	class_methods ci env rem 
    | JPFconstructor _ :: rem -> assert false (* TODO *)
*)

let type_field_initializer fi =
  let (_,init,_) = 
    try
      Hashtbl.find fields_table fi.java_field_info_tag 
    with Not_found -> assert false
  in
  let tinit = 
    Option_misc.map (type_initializer [] fi.java_field_info_type) init 
  in
  Hashtbl.replace fields_table fi.java_field_info_tag (fi,init,tinit)
  
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
	let ci = search_for_class (snd c.class_name) in	  
	List.iter type_field_initializer ci.class_info_fields;
	List.iter (type_method_spec_and_body ci) ci.class_info_methods
    | JPTinterface i -> assert false (* TODO *)
    | JPTannot(loc,s) -> assert false
    | JPTaxiom((loc,id),e) -> 
	let te = assertion [] e in
	Hashtbl.add axioms_table id te
    | JPTlogic_type_decl _ -> assert false (* TODO *)
    | JPTlogic_reads _ -> assert false (* TODO *)
    | JPTlogic_def((loc,id),ret_type,params,body) -> 
	let pl = List.map type_param params in
	let env = 
	  List.fold_left
	    (fun acc vi -> 
	       (vi.java_var_info_name,vi)::acc)
	    [] pl
	in
	begin match ret_type with
	  | None ->
	      let fi = logic_info id None pl in
	      let a = assertion env body in
	      Hashtbl.add logics_env id fi;
	      Hashtbl.add logics_table fi.java_logic_info_tag (fi,JAssertion a)
	  | Some _ -> assert false (* TODO *)
	end
	


let get_bodies cu =
  assert (cu.cu_package = []); (* TODO *)
  assert (cu.cu_imports = []); (* TODO *)
  List.iter type_decl cu.cu_type_decls


(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
