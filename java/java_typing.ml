
open Java_env
open Java_ast
open Java_tast
open Format
open Java_pervasives

(************************

Pretty-printing of types

*************************)

let rec print_qualified_ident fmt id =
  match id with
    | [] -> assert false
    | [(_,id)] -> fprintf fmt "%s" id
    | (_,id)::r ->
	print_qualified_ident fmt r;
	fprintf fmt ".%s" id
	
let print_type_name fmt t =
  match t with
    | TypeClass ci -> fprintf fmt "class %s" ci.class_info_name
    | TypeInterface ii -> fprintf fmt "interface %s" ii.interface_info_name


let string_of_base_type t =
  match t with
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
    | JTYnull -> fprintf fmt "(nulltype)"
    | JTYarray t -> fprintf fmt "%a[]" print_type t
    | JTYclass(_,c) -> fprintf fmt "%s" c.class_info_name
    | JTYinterface ii -> fprintf fmt "%s" ii.interface_info_name

(***********************

Typing error handling

************************)

exception Typing_error of Loc.position * string

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter

let integer_expected l = 
  typing_error l "integer type expected"

let class_or_interface_expected l =
  typing_error l "class or interface expected" 


(**********************

Name classification 
(JLS 2nd ed., pp. 93-104)

***********************)

type classified_name =
  | TermName of term
  | TypeName of java_type_info
  | PackageName of package_info


let rec list_assoc_field_name id l =
  match l with
    | [] -> raise Not_found
    | fi::r ->
	if fi.java_field_info_name = id then fi
	else list_assoc_field_name id r

let rec lookup_interface_field ii id =
  try
    list_assoc_field_name id ii.interface_info_fields
  with
      Not_found ->
	match ii.interface_info_extends with
	  | [] -> raise Not_found
	  | [ii] -> lookup_interface_field ii id
	  | _ -> assert false (* TODO *)

let rec lookup_class_field ci id =
  try
    list_assoc_field_name id ci.class_info_fields
  with
      Not_found ->
	(* TODO: lookup implemented interfaces *)
	match ci.class_info_extends with
	  | None -> raise Not_found
	  | Some ci -> lookup_class_field ci id

let lookup_field ti id =
  match ti with
    | TypeClass ci -> lookup_class_field ci id
    | TypeInterface ii -> lookup_interface_field ii id

(* corresponds to JLS 2nd ed., par. 6.5.2, pp. 96--97 *)
let rec classify_name 
    (package_env : (string * package_info) list)
    (type_env : (string * java_type_info) list)
    (current_type : java_type_info option)
    (local_env : (string * java_var_info) list)
    (name : qualified_ident) =
  match name with
    | [] -> assert false
    | [(loc,id)] ->
	(* case of a simple name (JLS p 96) *)
	begin
	  (* look for a local var of that name *)
	  try
	    let vi = List.assoc id local_env in
	    TermName { 
	      java_term_node = JTvar vi; 
	      java_term_type = vi.java_var_info_type;
	      java_term_loc = loc 
	    }
	  with Not_found -> 
	    (* look for a field of that name in current class *)
	    try
	      match current_type with
		| None -> raise Not_found
		| Some ti ->
		    let fi = lookup_field ti id in
		    let facc =
		      if fi.java_field_info_is_static then
			JTstatic_field_access(ti,fi)
		      else
			let vi = 
			  try
			    List.assoc "this" local_env 
			  with Not_found -> assert false
			in
			let this =
			  { java_term_node = JTvar vi; 
			    java_term_type = vi.java_var_info_type;
			    java_term_loc = loc }
			in		
			JTfield_access(this,fi)
		    in
		    TermName {
		      java_term_node = facc;
		      java_term_type = fi.java_field_info_type;
		      java_term_loc = loc
		    }
	    with Not_found ->
	      try
		(* TODO: look for a local class of member type of that name *)
		raise Not_found
	      with
		  Not_found ->
		    try 
		      (* look for a type of that name 
			 in the current compilation unit, or
			 in another compilation unit of the current package *)
		      let ti = List.assoc id type_env in
		      TypeName ti 
		    with Not_found ->
		      
		      (* look for a type of that name 
			 declared by a type-import-on-demand declaration 
			 (fail if two of them are visible) *)
		      try
			let pi = List.assoc id package_env in
			PackageName pi 
		      with Not_found ->
			  (* otherwise look for a package of that name *)
			  (* TODO *)
			  typing_error loc "unknown identifier %s" id
	end		
	  
    | (loc,id)::n ->
	(* case of a qualified name (JLS p 97) *)
	match classify_name package_env type_env current_type local_env n with
	  | PackageName pi -> 
	      (* TODO *)
	      assert false
	  | TypeName ci ->
	      begin
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
		  (* TODO: look for a method of that name ? *)
		  (* TODO: look for a member type of that name *)
		  typing_error loc 
		    "no such field in %a" print_type_name ci
	      end
	  | TermName t -> 
	      begin
		match t.java_term_type with
		  | JTYclass(_,c) ->
		      begin
			try
			  let fi = lookup_class_field c id in
			  TermName { 
			    java_term_loc = loc;
			    java_term_type = fi.java_field_info_type ;
			    java_term_node = JTfield_access(t,fi)
			  }
			with Not_found ->
			  typing_error loc 
			    "no such field in class %s" c.class_info_name
		      end
		  | JTYinterface ii ->
		      assert false (* TODO *)
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
		  | JTYnull | JTYbase _ ->
		      class_or_interface_expected t.java_term_loc 
	      end

(******************************

Typing level 0: extract types (logic, Java classes, Java interfaces)

**********************************)

(* [package_table] maps each internal package id to package_info *)
let package_table = 
  (Hashtbl.create 17 : (int,package_info) Hashtbl.t)

(* [package_contents] maps each internal package id to its contents *)
type package_member =
  | Subpackage of package_info
  | Type of java_type_info

let package_contents = 
  (Hashtbl.create 17 : (int,package_member list) Hashtbl.t)

(* [package_env] maps each visible package name to its internal id 

   initially should contain "java" mapped to 0, then package_contents
   maps 0 to the 1-element list [Subpackage pi] where pi is the
   package_info for "lang" whose id is 1,
   
*) 

(*
let package_env = ref ([] : (string * int) list)
*)

let type_table = Hashtbl.create 17

(*
let search_package_info qid =
  let rec get_table qid =
    match qid with
      | [] -> assert false
      | [_] -> package_table
      | _::r -> get_table 
  in 
*)  

(* adds an interface named [id] in package [p] *)
let new_interface_info (p:package_info) (id:string) =
  let ii =
    { interface_info_name = id ;
      interface_info_fields = [];
      interface_info_methods = [];
      interface_info_extends = [];
    }
  in
  eprintf "adding interface %s in package '%s'@." id p.package_info_name;
  let l =
    try
      Hashtbl.find package_contents p.package_info_tag 
    with
	Not_found -> []
  in
  Hashtbl.replace package_contents p.package_info_tag 
    (Type (TypeInterface ii) :: l);
  ii

let new_class_info (p:package_info) (id:string) =
  let ci =
    { class_info_name = id ;
      class_info_fields = [];
      class_info_methods = [];
      class_info_constructors = [];
      class_info_extends = None;
      class_info_is_exception = false;
      class_info_implements = [];
    }
  in
  eprintf "adding class %s in package %s@." id p.package_info_name;
  let l =
    try
      Hashtbl.find package_contents p.package_info_tag 
    with
	Not_found -> []
  in
  Hashtbl.replace package_contents p.package_info_tag 
    (Type (TypeClass ci) :: l);
  ci

let get_type_decl package d acc = 
    match d with
    | JPTclass c -> 
	(*
	  class_modifiers : modifiers;
	  class_name : identifier;
	  class_extends : qualified_ident option;
	  class_implements : qualified_ident list;
	  class_fields : field_declaration list
	*)
	let (_,id) = c.class_name in
	let ci = new_class_info package id in 
	(id,TypeClass ci)::acc
    | JPTinterface i -> 
	let (_,id) = i.interface_name in
	let ii = new_interface_info package id in 
	(id,TypeInterface ii)::acc
    | JPTannot(loc,s) -> assert false
    | JPTaxiom((loc,id),e) -> acc
    | JPTlogic_type_decl _ -> assert false (* TODO *)
    | JPTlogic_reads((loc,id),ret_type,params,reads) -> acc 
    | JPTlogic_def((loc,id),ret_type,params,body) -> acc


let package_counter = ref 0

let get_import imp =
    match imp with
      | Import_package qid ->
	  eprintf "importing package %a@." print_qualified_ident qid;
	  begin
(*
	    try
	      ignore (search_package qid)
	    with
		Not_found ->
		  incr package_counter;
		  let pi =
		    { package_entry_tag = !package_counter;
		      package_entry_name = snd (List.hd qid);
		    }
		  in
		  Hashtbl.add package_table !package_counter pi
*)
	    assert false
	  end
      | Import_class_or_interface qid ->
	  eprintf "importing %a@." print_qualified_ident qid;
	  assert false
(*
	  let ast = Java_syntax.file f in
	  Java_typing.get_types ast;
	  Java_typing.get_prototypes ast
*)
	  

let anonymous_package =
  { package_info_tag = 0;
    package_info_name = "";
    package_info_directory = ".";
  }
	
let get_types cu =
  let pi = 
    match cu.cu_package with
      | [] -> anonymous_package
      | qid ->
	  match classify_name [] [] None [] qid with
	    | PackageName pi -> pi
	    | _ -> assert false
  in
  (*
  List.iter get_import cu.cu_imports;
  *)
  [], List.fold_right (get_type_decl pi) cu.cu_type_decls []



(******************************

Typing level 1: extract prototypes 
  (logic functions profiles, Field types of Java classes and interfaces, profiles of methods and constructors)

**********************************)

(*
let search_for_type (loc,id) =
  try
    Hashtbl.find type_table id 
  with
      Not_found -> 
	eprintf "class or interface %s not yet known@." id;
	(* looking in current directory (correct ????) TODO *)
	(* looking in imported packages *)
	raise Not_found
*)

(* importing java.lang and the 'Throwable' class *)
  
(* 
let javalang_qid = [(Loc.dummy_position,"lang"); (Loc.dummy_position,"java")]

let () = 
  get_import (Import_package javalang_qid);
  (* importing the 'Throwable' class *)
  get_import (Import_class_or_interface 
		((Loc.dummy_position,"Throwable")::javalang_qid));
  let the_throwable_class = search_for_type "Throwable" in
  the_throwable_class.class_info_is_exception <- true
*)

(* typing types *)

let rec type_type package_env type_env ty =
  match ty with
    | Base_type t -> JTYbase t
    | Type_name qid -> 
	begin
	  match classify_name package_env type_env None [] qid with
	    | TypeName ti ->
		begin
		  match ti with
		    | TypeClass ci -> JTYclass(false,ci)
		    | TypeInterface ii -> JTYinterface(ii)
		end
	    | _ -> assert false (* TODO *)
	end
    | Array_type_expr t -> 
	let ty = type_type package_env type_env t in
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

let field_prototypes_table = Hashtbl.create 97

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

let new_model_field ii ty id =
(*
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
*)
assert false (* TODO *)

(* methods *)

let methods_env = Hashtbl.create 97

let method_tag_counter = ref 0

let new_method_info ~is_static id ty pars =
  incr method_tag_counter;
  let result = 
      Option_misc.map (fun t -> new_var t "\\result") ty
  in
  {
    method_info_tag = !method_tag_counter;
    method_info_name = id;
    method_info_trans_name = id;
    method_info_has_this = None;
    method_info_parameters = pars;
    method_info_result = result;
    method_info_calls = [];
    method_info_is_static = is_static;
  }

let constructors_env = Hashtbl.create 97

let constr_tag_counter = ref 0

let new_constructor_info ci id pars =
  incr constr_tag_counter;
  {
    constr_info_tag = !constr_tag_counter;
    constr_info_class = ci;
    constr_info_trans_name = ci.class_info_name;
    constr_info_this = None;
    constr_info_result = None;
    constr_info_parameters = pars;
    constr_info_calls = [];
  }

let type_param package_env type_env p =
  let rec get_type p =
    match p with
      | Simple_parameter(ty,(loc,id)) -> 
	  (type_type package_env type_env ty, id)
      | Array_parameter x -> 
	  let (t,i) = get_type x in
	  (JTYarray t,i)
  in
  let (t,i) = get_type p in new_var t i

let rec method_header package_env type_env retty mdecl =
  match mdecl with
    | Simple_method_declarator(id,l) -> 
	eprintf "get prototype for method %s@." (snd id);
	id,(Option_misc.map (type_type package_env type_env) retty), 
	List.map (type_param package_env type_env) l
    | Array_method_declarator d -> 
	let id,t,l = 
	  method_header package_env type_env retty d 
	in
	match t with
	  | Some t -> id,Some (JTYarray t),l
	  | None -> typing_error (fst id) "invalid type void array"


let get_field_prototypes package_env type_env ci acc d =
  match d with
    | JPFvariable vd -> 
	(*
	vd.variable_modifiers : modifiers ;
	vd.variable_type : type_expr ;
	vd.variable_decls : variable_declarator list }
	*)
	let ty = type_type package_env type_env vd.variable_type in
	let is_static = List.mem Static vd.variable_modifiers in
	let is_final = List.mem Final vd.variable_modifiers in
	List.fold_left
	  (fun acc vd -> 
	     let ty',(loc,id) = var_type_and_id ty vd.variable_id in
	     let fi = new_field ~is_static ~is_final ci ty' id in	     
	     Hashtbl.add field_prototypes_table fi.java_field_info_tag 
	       (fi,vd.variable_initializer);
	     fi::acc
	  ) acc vd.variable_decls
    | _ -> acc

let get_interface_field_prototypes package_env type_env ii acc d =
  match d with
    | JPFmodel_variable vd -> 
	(*
	vd.variable_modifiers : modifiers ;
	vd.variable_type : type_expr ;
	vd.variable_decls : variable_declarator list }
	*)
	let ty = type_type package_env type_env vd.variable_type in
	List.fold_left
	  (fun acc vd -> 
	     let ty',(loc,id) = var_type_and_id ty vd.variable_id in
	     let fi = new_model_field ii ty' id in	     
(*
	     Hashtbl.add model_field_prototypes_table fi.java_field_info_tag 
	       (fi,vd.variable_initializer);
*)
	     fi::acc
	  ) acc vd.variable_decls
    | _ -> acc

let rec get_method_prototypes package_env type_env current_type (mis,cis) env l =
  match l with
    | [] -> (mis,cis)
    | JPFmethod(head,body) :: rem -> 
	let id, ret_ty, params = 
	  method_header package_env type_env 
	    head.method_return_type head.method_declarator 
	in
	let is_static = List.mem Static head.method_modifiers in
	let mi = new_method_info ~is_static (snd id) ret_ty params in
	Hashtbl.add methods_env mi.method_info_tag (mi,None,[],body);
	get_method_prototypes package_env type_env 
	  current_type (mi::mis,cis) env rem 
    | JPFmethod_spec(req,behs) :: JPFmethod(head,body) :: rem ->
	let id, ret_ty, params = 
	  method_header package_env type_env 
	    head.method_return_type head.method_declarator 
	in
	let is_static = List.mem Static head.method_modifiers in
	let mi = new_method_info ~is_static (snd id) ret_ty params in
	Hashtbl.add methods_env mi.method_info_tag (mi,req,behs,body);
	get_method_prototypes package_env type_env 
	  current_type (mi::mis,cis) env rem 
   | JPFmethod_spec(req,behs) :: JPFconstructor(head,eci,body) :: rem ->
       begin
	 match current_type with
	   | None -> assert false
	   | Some cur ->
	       let id = head.constr_name in
	       let params = 
		 List.map (type_param package_env type_env) 
		   head.constr_parameters 
	       in
	       let ci = new_constructor_info cur (snd id) params in
	       Hashtbl.add constructors_env ci.constr_info_tag 
		 (ci,req,behs,eci,body);
	       get_method_prototypes package_env type_env 
		 current_type (mis,ci::cis) env rem 
       end
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
	get_method_prototypes package_env type_env
	  current_type (mis,cis) env rem 
    | JPFannot _ :: _ -> assert false (* not possible after 2nd parsing *)
    | JPFstatic_initializer _ ::rem -> assert false (* TODO *)
    | (JPFmodel_variable _ | JPFvariable _) :: rem -> 
	get_method_prototypes package_env type_env 
	  current_type (mis,cis) env rem 
    | JPFconstructor _ :: rem -> assert false (* TODO *)


let type_decl package_env type_env d = 
    match d with
    | JPTclass c -> 
	(*
	  class_modifiers : modifiers;
	  class_name : identifier;
	  class_extends : qualified_ident option;
	  class_implements : qualified_ident list;
	  class_fields : field_declaration list
	*)
	begin
	  try
	    match List.assoc (snd c.class_name) type_env with	  
	    | TypeInterface _ -> assert false
	    | TypeClass ci ->
		(* extends *)
		ci.class_info_extends <-
		  Option_misc.map 
		  (fun id -> 
		     match classify_name package_env type_env None [] id with
		       | TypeName (TypeClass super) -> 
			   ci.class_info_is_exception <-
			     super.class_info_is_exception;
			   super
		       | _ ->
			   typing_error (fst (List.hd id)) "class type expected") 
		  c.class_extends;
		(* fields *)
		let fields = List.fold_left (get_field_prototypes package_env type_env ci) [] c.class_fields in
		ci.class_info_fields <- fields;
		let methods,constructors = 
		  get_method_prototypes package_env type_env (Some ci) ([],[]) [] c.class_fields 
		in
		ci.class_info_methods <- methods;
		ci.class_info_constructors <- constructors;
	  with Not_found -> assert false
	end
    | JPTinterface i -> 
	begin
	  try
	    match List.assoc (snd i.interface_name) type_env with
	      | TypeClass _ -> assert false
	      | TypeInterface ii ->
		  (* extends *)
		  ii.interface_info_extends <-
		    List.map 
		    (fun id -> 
		       match classify_name package_env type_env None [] id with
			 | TypeName (TypeInterface super) -> 
			     super
			 | _ ->
			     typing_error (fst (List.hd id)) "interface type expected") 
		    i.interface_extends;
		  (* fields *)
		  let fields = 
		    List.fold_left (get_interface_field_prototypes package_env type_env ii) [] i.interface_members
		  in
		  ii.interface_info_fields <- fields;
		  let methods,constructors = 
		    get_method_prototypes  package_env type_env None ([],[]) [] i.interface_members
		  in
		  ii.interface_info_methods <- methods
	  with Not_found -> assert false
	end
    | JPTannot(loc,s) -> assert false
    | JPTaxiom((loc,id),e) -> ()
    | JPTlogic_type_decl _ -> assert false (* TODO *)
    | JPTlogic_reads _ -> ()
    | JPTlogic_def((loc,id),ret_type,params,body) -> ()
	


let get_prototypes package_env type_env cu =
  List.iter (type_decl package_env type_env) cu.cu_type_decls


(*******************************

Typing level 2: extract bodies
  (logic functions definitions, axioms,
   field initializers, method and constructors bodies)

**********************************)

let imported_packages = ref [ "java.lang" ]


let fields_table = Hashtbl.create 17

let invariants_table = Hashtbl.create 17

let axioms_table = Hashtbl.create 17







(* logic funs *)

type logic_body =
  | JAssertion of assertion
  | JTerm of term
  | JReads of term list

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
	    | Tboolean | Tunit -> raise Not_found
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
	    | Tboolean | Tunit -> false
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
    | JTYbase t -> false
    | _ -> true

let lub_object_types t1 t2 = JTYnull
  
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
    | JTYbase _, _ | _, JTYbase _ -> false
    | _, JTYnull | JTYnull,  _ -> true
    | JTYarray t1, JTYarray t2 -> compatible_types t1 t2
    | JTYclass(_,c1), JTYclass(_,c2) -> 
	if c1 == c2 then true else
	  assert false
    | JTYinterface i1, JTYinterface i2 -> 
	if i1 == i2 then true else
	  assert false
    | JTYclass _, JTYarray _ -> assert false
    | JTYarray _, JTYclass _ -> assert false
    | _ -> assert false

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


	
  
let rec term package_env type_env current_type env e =
  let termt = term package_env type_env current_type env in
  let ty,tt =
    match e.java_pexpr_node with
      | JPElit l -> 
	  let ty,l = lit l in ty,(JTlit l)
      | JPEname n ->
	  begin
	    match classify_name package_env type_env current_type env n with
	      | TermName t ->
		  t.java_term_type, t.java_term_node
	      | TypeName _ ->
		  typing_error e.java_pexpr_loc
		    "term expected, got a class or interface"
	      | PackageName _ ->
		  typing_error e.java_pexpr_loc
		    "term expected, got a package name"
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
	  let te1 = termt e1 and te2 = termt e2 in 
	  make_logic_bin_op e.java_pexpr_loc op 
	    te1.java_term_type te1 te2.java_term_type te2
      | JPEquantifier (q, ty, idl, e)-> 
	  typing_error e.java_pexpr_loc
	    "quantified formulas not allowed in term position"
      | JPEold e1 -> 
	  let te1 = termt e1 in te1.java_term_type,JTold te1	
      | JPEinstanceof (_, _)-> assert false (* TODO *)
      | JPEcast (t, e1)-> 
	  let te1 = termt e1 in
	  let ty = type_type package_env type_env t in
	  (* TODO: check if cast allowed *)
	  ty,JTcast(ty,te1)
      | JPEarray_access (e1, e2)-> 
	  let te1 = termt e1 and te2 = termt e2 in 
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
      | JPEarray_range (e1, e2, e3)->
	  let te1 = termt e1 and te2 = termt e2 and te3 = termt e3 in 
	  begin
	    match te1.java_term_type with
	      | JTYarray t ->
		  if is_numeric te2.java_term_type then 
		    if is_numeric te3.java_term_type then
		      t, JTarray_range(te1,te2, te3)
		    else
		      integer_expected e3.java_pexpr_loc
		  else
		    integer_expected e2.java_pexpr_loc
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
		      let args = List.map termt args in		      
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
		  let te1 = termt e1 in
		  begin
		    match te1.java_term_type with
		      | JTYclass(_,ci) ->
			  begin
			    try
			      let fi = lookup_field (TypeClass ci) (snd f) in
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
	    JAbin_obj(e1,op,e2)
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

let rec assertion package_env type_env current_type env e =
  let termt = term package_env type_env current_type env in
  let assertiont = assertion package_env type_env current_type env in
  let ta =
  match e.java_pexpr_node with
    | JPElit (Bool true) -> JAtrue
    | JPElit (Bool false) -> JAfalse
    | JPElit _ -> 
	typing_error e.java_pexpr_loc 
	  "this literal is not a boolean expression"
    | JPEun(Unot, e2) ->
	let te2 = assertiont e2 in JAnot(te2)
    | JPEun (_, _)-> assert false (* TODO *)
    | JPEbin(e1, ((Band | Bor | Bimpl | Biff) as op) , e2) ->
	let te1 = assertiont e1
	and te2 = assertiont e2
	in connective te1 op te2
    | JPEbin(e1, op, e2) -> 
	let te1 = termt e1 and te2 = termt e2 in 
	make_predicate_bin_op e.java_pexpr_loc op 
	  te1.java_term_type te1 te2.java_term_type te2
    | JPEquantifier (q, ty, idl, e)-> 
	let tty = type_type package_env type_env ty in
	let a = make_quantified_formula 
	  e.java_pexpr_loc q tty idl package_env type_env current_type env e 
	in
	a.java_assertion_node
    | JPEold _-> assert false (* TODO *)
    | JPEinstanceof (_, _)-> assert false (* TODO *)
    | JPEcast (_, _)-> assert false (* TODO *)
    | JPEarray_access (_, _)-> assert false (* TODO *)
    | JPEarray_range (_, _,_)-> assert false (* TODO *)
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
		     let te = termt e in
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

and make_quantified_formula loc q ty idl package_env type_env current_type env e : assertion =
  match idl with
    | [] -> assertion package_env type_env current_type env e
    | id::r ->
	let tyv, (loc,n) = var_type_and_id ty id in
	let vi = new_var tyv n in
	let f = 
	  make_quantified_formula loc q ty r package_env type_env current_type ((n,vi)::env) e 
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

let make_unary_op loc op t1 e1 =
  match op with
    | Unot -> assert false
    | Ucompl-> assert false
    | Uminus-> 
	if is_numeric t1 then
	  let t = lub_numeric_types t1 t1 in
	  t,JEun(op, e1)
	else
	  typing_error loc "numeric types expected for -"
      | Uplus -> assert false
(*
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
	*)

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
      | JTarray_range _  -> assert false (* TODO *)
      | JTapp (_, _) -> assert false (* TODO *)
      | JTbin (_, _, _, _) -> assert false (* TODO *)
      | JTlit _ -> assert false (* TODO *)
      | JTcast(ty,t) -> JEcast(ty,expr_of_term t)
  in
  { java_expr_loc = t.java_term_loc;
    java_expr_type = t.java_term_type;
    java_expr_node = n ;
  }

(*
  JLS 15.12.2: Compile-Time Step 2: Determine Method signature

  ti is the class or interface to search
  
*)

let is_accessible_and_applicable mi id arg_types =
  if mi.method_info_name = id then 
      (* !!!!!!! TODO !!!! 
	 check args types
      *)
      true
  else 
    false
	
let lookup_method ti (loc,id) arg_types = 
  let rec collect_methods_from_interface acc ii =
    let acc = 
      List.fold_left
	(fun acc mi -> 
	   if is_accessible_and_applicable mi id arg_types then 
	     mi::acc 
	   else acc)
	acc ii.interface_info_methods 
    in
    List.fold_left
      collect_methods_from_interface acc ii.interface_info_extends
  in
  let rec collect_methods_from_class acc ci =
    let acc = 
      List.fold_left
	(fun acc mi -> 
	   if is_accessible_and_applicable mi id arg_types then 
	     mi::acc 
	   else acc)
	acc ci.class_info_methods 
    in
    let acc =
      match ci.class_info_extends with
	| None -> acc 
	| Some ci -> collect_methods_from_class acc ci
    in
    List.fold_left
      collect_methods_from_interface acc ci.class_info_implements
  in
  let meths = 
    match ti with
      | TypeClass ci -> collect_methods_from_class [] ci 
      | TypeInterface ii -> collect_methods_from_interface [] ii 
  in
  match meths with
    | [] -> raise Not_found
    | [mi] -> mi
    | _ -> 
	typing_error loc "overloading/overriding not yet supported"

let lookup_constructor ci arg_types = 
  (* !!!!!!!!! TODO !!!!!!! *)
  ()

let rec expr package_env type_env current_type env e =
  let exprt = expr package_env type_env current_type env in
  let ty,te = 
    match e.java_pexpr_node with
      | JPElit l -> let t,l = lit l in t,(JElit l)
      | JPEname n -> 
	  begin
	    match classify_name package_env type_env current_type env n with
	      | TermName t ->
		  let e = expr_of_term t in
		  e.java_expr_type, e.java_expr_node
	      | TypeName _ ->
		  typing_error e.java_pexpr_loc
		    "expression expected, got a class or interface"
	      | PackageName _ ->
		  typing_error e.java_pexpr_loc
		    "expression expected, got a package name"
	  end
      | JPEthis -> 
	  let vi = get_this e.java_pexpr_loc env in
	  vi.java_var_info_type, JEvar vi
      | JPEinstanceof (_, _)-> assert false (* TODO *)
      | JPEcast (t, e1)-> 
	  let te1 = exprt e1 in
	  let ty = type_type package_env type_env t in
	  (* TODO: check if cast is allowed *)
	  ty,JEcast(ty,te1)
      | JPEarray_access (e1, e2)-> 
	  let te1 = exprt e1 and te2 = exprt e2 in 
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
      | JPEnew_array(t,dims) ->
	  let ty = type_type package_env type_env t in 
	  let l =
	    List.map (fun e ->
			let te = exprt e in
			if is_numeric te.java_expr_type then te
			else 
			  typing_error e.java_pexpr_loc
			    "integer expected")	
	      dims
	  in
	  JTYarray ty, JEnew_array(ty,l)
      | JPEnew (n, args) -> 
	  let args = List.map exprt args in
	  let arg_types = List.map (fun e -> e.java_expr_type) args in
	  begin
	    match classify_name package_env type_env current_type env n with
	      | TypeName (TypeClass ci) ->
		  let _constr = lookup_constructor ci arg_types in
		  JTYclass(true,ci),JEnew_object(ci,args)
	      | _ ->
		  typing_error (fst (List.hd n))
		    "class type expected"	
	  end	  
      | JPEsuper_call (_, _)-> assert false (* TODO *)
      | JPEcall (e1, id, args)-> 
	  let args = List.map exprt args in
	  let arg_types = List.map (fun e -> e.java_expr_type) args in
	  begin
	    let ci,te1 =
	      match e1 with
		| None -> 
		    begin
		      match current_type with
			| None -> assert false
			| Some ci -> ci,None
		    end
		| Some e ->
		    let te = expr package_env type_env current_type env e in
		    begin
		      match te.java_expr_type with
			| JTYclass(_,ci) -> (TypeClass ci),Some te
			| JTYinterface(ii) -> (TypeInterface ii),Some te
			| _ -> typing_error e.java_pexpr_loc 
			    "not a class or interface type"
		    end
	    in
	    let mi = lookup_method ci id arg_types in
	    let ty = 
	      match mi.method_info_result with
		| None -> unit_type
		| Some vi -> vi.java_var_info_type
	    in
	    if mi.method_info_is_static then
	      ty,JEstatic_call(mi,args)
	    else
	      let te2 =
		match te1 with
		  | Some e -> e
		  | None ->
		      let vi = get_this e.java_pexpr_loc env in
		      {
			java_expr_node = JEvar vi;
			java_expr_type = vi.java_var_info_type;
			java_expr_loc = e.java_pexpr_loc;
		      }
	      in
	      ty,JEcall(te2,mi,args)
	  end
      | JPEfield_access _-> assert false (* TODO *)
      | JPEif (_, _, _)-> assert false (* TODO *)
      | JPEassign_array (e1, e2, op, e3)-> 
	  let te1 = exprt e1 
	  and te2 = exprt e2 
	  and te3 = exprt e3 
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
	    let te = exprt e1 in
	    match classify_name package_env type_env current_type env n with
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
	      | TypeName _ ->
		  typing_error e.java_pexpr_loc
		    "lvalue expected, got a class or interface"
	      | PackageName _ ->
		  typing_error e.java_pexpr_loc
		    "lvalue expected, got a package name"
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
	  let te = exprt e in 
	  begin
	    match te.java_expr_node with
	      | JEvar v ->
		  te.java_expr_type,JEincr_local_var(op,v)
	      | _ -> assert false (* TODO *)
	  end	  
      | JPEun (op, e1)-> 
	  let te1 = exprt e1 in 
	  let t,e = make_unary_op e.java_pexpr_loc op 
		      te1.java_expr_type te1 in
	  JTYbase t,e

      | JPEbin (e1, op, e2) -> 
	  let te1 = exprt e1 and te2 = exprt e2 in 
	  let t,e = make_bin_op e.java_pexpr_loc op 
		      te1.java_expr_type te1 te2.java_expr_type te2 in
	  JTYbase t,e
	       (* only in terms *)
      | JPEarray_range _ 
      | JPEquantifier (_, _, _, _)
      | JPEold _
      | JPEresult -> 
	  typing_error e.java_pexpr_loc "not allowed in expressions"

  in { java_expr_loc = e.java_pexpr_loc;
	java_expr_type = ty;
	java_expr_node = te; }


let rec initializer_loc i =
  match i with
    | Simple_initializer e -> e.java_pexpr_loc
    | Array_initializer (x::_) -> initializer_loc x
    | Array_initializer [] -> assert false (* TODO *)
			   
let type_initializer package_env type_env current_type env ty i =
  match ty,i with
    | _, Simple_initializer e ->
	let te = expr package_env type_env current_type env e in	
	if compatible_types ty te.java_expr_type then JIexpr te
	else
	  typing_error e.java_pexpr_loc "type %a expected, got %a"
	    print_type ty print_type te.java_expr_type
    | JTYarray t, Array_initializer l -> 
	assert false (* TODO *)
    | _, Array_initializer l -> 
	typing_error (initializer_loc i) "wrong type for initializer"


(* statements *)

let variable_declaration package_env type_env current_type env vd =
  let ty = type_type package_env type_env vd.variable_type in
  let l =
    List.map
      (fun vd ->
	 let ty',id = var_type_and_id ty vd.variable_id in
	 match vd.variable_initializer with
	   | None -> (id,ty',None)
	   | Some e -> 
	       let i = 
		 type_initializer package_env type_env
		   current_type env ty' e 
	       in
	       (id,ty',Some i))
      vd.variable_decls
  in
  List.fold_right
      (fun ((loc,id),ty,i) (env,decls)->
	 let vi = new_var ty id in		     
	 (id,vi)::env,(vi,i)::decls)
      l (env,[])

let rec statement package_env type_env current_type env s =
  let assertiont = assertion package_env type_env current_type env in
  let exprt = expr package_env type_env current_type env in
  let statementt = statement package_env type_env current_type env in
  let s' =
    match s.java_pstatement_node with
      | JPSskip -> JSskip
      | JPSif (e, s1, s2) ->
	  let te = exprt e in
	  let ts1 = statementt s1 in
	  let ts2 = statementt s2 in
	  if is_boolean te.java_expr_type then	    
	    JSif(te,ts1,ts2)
	  else
	    typing_error e.java_pexpr_loc "boolean expected"
      | JPSloop_annot (inv, dec) -> assert false
      | JPSannot (_, _)-> assert false (* TODO *)
      | JPSghost_local_decls d -> assert false (* TODO *)
      | JPSghost_statement e
      | JPSexpr e -> 
	  let te = exprt e in JSexpr te
      | JPSassert(id,a) ->
	  let ta = assertiont a in
	  JSassert(Option_misc.map snd id,ta)
      | JPSsynchronized (_, _)-> assert false (* TODO *)
      | JPSblock l -> (block package_env type_env current_type env l).java_statement_node
      | JPSswitch (e, l)-> 
	  let te = exprt e in
	  (* JSL, p289: switch expr must be char, byte, short or int *)
	  begin
	    try 
	      let t = int_type te.java_expr_type in
	      JSswitch(te,List.map (switch_case package_env type_env current_type env t) l)
	    with Not_found ->
	      typing_error e.java_pexpr_loc "char, byte, short or int expected"
	  end
      | JPStry (s, catches, finally)-> 
	  let ts = statements package_env type_env current_type env s in
	  let tl =
	    List.map
	      (fun (p,s) ->
		 let vi = type_param package_env type_env p in
		 let e = (vi.java_var_info_name,vi)::env in
		 (vi,statements package_env type_env current_type e s))
	      catches
	  in
	  JStry(ts, tl, 
		Option_misc.map (statements package_env type_env current_type env) finally)
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
	      let te = exprt e in 
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
      | JPSthrow e -> 
	  let te = exprt e in
	  JSthrow te
      | JPSvar_decl _-> assert false (* TODO *)
	  
  in 
  { java_statement_loc = s.java_pstatement_loc ;
    java_statement_node = s' }


and statements package_env type_env current_type env b =
  match b with
    | [] -> []
    | s :: rem ->
	match s.java_pstatement_node with
	  | JPSskip -> statements package_env type_env current_type env rem
	  | JPSghost_local_decls vd 
	  | JPSvar_decl vd -> 
	      let env,decls = 
		variable_declaration package_env type_env 
		  current_type env vd 
	      in
	      let r = block package_env type_env current_type env rem in
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
		      let inv = assertion package_env type_env current_type env inv in
		      let dec = term package_env type_env current_type env dec in
		      let e = expr package_env type_env current_type env e in
		      let s = statement package_env type_env current_type env s in
		      { java_statement_node = JSwhile(e,inv,dec,s);
			java_statement_loc = loc } :: 
			statements package_env type_env current_type env rem
		  | { java_pstatement_node = JPSfor_decl(vd,e,sl,s) ;
		      java_pstatement_loc = loc } :: rem -> 
		      let env,decls = 
			variable_declaration package_env type_env current_type env vd 
		      in
		      let inv = assertion package_env type_env current_type env inv in
		      let dec = term package_env type_env current_type env dec in
		      let e = expr package_env type_env current_type env e in
		      let sl = List.map (expr package_env type_env current_type env) sl in
		      let s = statement package_env type_env current_type env s in
		      { java_statement_node = JSfor_decl(decls,e,inv,dec,sl,s);
			java_statement_loc = loc } :: 
			statements package_env type_env current_type env rem	
		  | _ -> assert false
	      end      
	  | _ ->
	      let s' = statement package_env type_env current_type env s in
	      s' :: statements package_env type_env current_type env rem

and block package_env type_env current_type env b =
  match statements package_env type_env current_type env b with
    | [] -> { java_statement_loc = Loc.dummy_position ; 
	      java_statement_node = JSskip }
    | [s] -> s
    | (s::_) as l -> 
	{ java_statement_loc = s.java_statement_loc ; 
	  java_statement_node = JSblock l }

and switch_case package_env type_env current_type env t (labels,b) =
  (List.map (switch_label package_env type_env current_type env t) labels, 
   statements package_env type_env current_type env b)

and switch_label package_env type_env current_type env t = function
  | Default -> Default
  | Case e ->
      let te = expr package_env type_env current_type env e in
      match te.java_expr_type with
	| JTYbase t' when subbasetype t' t -> Case te 
	| JTYbase Tinteger -> Case te
	| _ ->
	     typing_error e.java_pexpr_loc "type `%s' expected, got `%a'"
		(string_of_base_type t) print_type te.java_expr_type

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

let location env a = term env a 
  

let behavior package_env type_env current_type pre_state_env post_state_env (id,b) = 
  let throws,ensures_env = 
    match b.java_pbehavior_throws with
      | None -> None,post_state_env
      | Some(c,None) -> 
	  begin
	    match classify_name package_env type_env current_type pre_state_env c with
	      | TypeName (TypeClass ci) ->
		  (* TODO: check it has Throwable as superclass *)
		  (Some ci),post_state_env
	      | TypeName (TypeInterface ci) ->
		  typing_error (fst (List.hd c))
		    "class type expected, not an interface"
	      | TermName _ ->
		  typing_error (fst (List.hd c))
		    "class type expected"
	      | PackageName _ ->
		  typing_error (fst (List.hd c))
		    "class type expected"
	  end
      | Some(c,Some id) -> 
	  assert false (* TODO *)
  in
  (id,
   Option_misc.map (assertion package_env type_env current_type pre_state_env) b.java_pbehavior_assumes,
   throws,
   (* Note: for constructors, the `assigns' clause is typed in
      pre-state environnement: `this' is not allowed there *)
   Option_misc.map (List.map (location package_env type_env current_type pre_state_env)) b.java_pbehavior_assigns,
   assertion package_env type_env current_type ensures_env b.java_pbehavior_ensures)
    


(* methods *)

type method_table_info =
    { mt_method_info : Java_env.method_info;
      mt_requires : Java_tast.assertion option;
      mt_behaviors : (Java_ast.identifier * 
			Java_tast.assertion option * 
			Java_env.java_class_info option *
			Java_tast.term list option * 
			Java_tast.assertion) list ;
      mt_body : Java_tast.block option;
    }


  
let methods_table = Hashtbl.create 97


let type_method_spec_and_body package_env type_env ti mi =
  let (_,req,behs,body) = 
    try
      Hashtbl.find methods_env mi.method_info_tag 
    with Not_found -> assert false
  in
  let local_env =
    if mi.method_info_is_static then [] else
      let this_type =
	match ti with
	  | TypeClass ci -> JTYclass(true,ci)
	  | TypeInterface ii -> JTYinterface ii
      in
      let vi = new_var this_type "this" in
      mi.method_info_has_this <- Some vi;
      [("this",vi)]
  in
  let local_env = 
    List.fold_left
      (fun acc vi -> 
	 (vi.java_var_info_name,vi)::acc)
      local_env mi.method_info_parameters
  in
  let req = Option_misc.map (assertion package_env type_env (Some ti) local_env) req in
  let env_result =
    match mi.method_info_result with
      | None -> local_env
      | Some vi -> (vi.java_var_info_name,vi)::local_env
  in
  let behs = List.map (behavior package_env type_env (Some ti) local_env env_result) behs in
  let body = Option_misc.map (statements package_env type_env (Some ti) env_result) body in
  Hashtbl.add methods_table mi.method_info_tag 
    { mt_method_info = mi;
      mt_requires = req;
      mt_behaviors = behs;
      mt_body = body } 



type constructor_table_info =
    { ct_constr_info : Java_env.constructor_info;
      ct_requires : Java_tast.assertion option;
      ct_behaviors : (Java_ast.identifier * 
			Java_tast.assertion option * 
			Java_env.java_class_info option *
			Java_tast.term list option * 
			Java_tast.assertion) list ;
(*
      ct_eci : int;
*)
      ct_body : Java_tast.block;
    }

let constructors_table = Hashtbl.create 97

let type_constr_spec_and_body package_env type_env current_type ci =
  let (_,req,behs,eci,body) = 
    try
      Hashtbl.find constructors_env ci.constr_info_tag 
    with Not_found -> assert false
  in
  let local_env = 
    List.fold_left
      (fun acc vi -> 
	 (vi.java_var_info_name,vi)::acc)
      [] ci.constr_info_parameters
  in
  let this_type =
    match current_type with
      | TypeClass ci -> JTYclass(true,ci)
      | TypeInterface ii -> JTYinterface ii
  in
  let spec_env =
    (* spec is typed in a env that contains "this" but it will be
       renamed to "\\result" *)
    let vi = new_var this_type "\\result" in
    ci.constr_info_result <- Some vi;
    ("this",vi)::local_env
  in
  let body_env =
    let vi = new_var this_type "this" in
    ci.constr_info_this <- Some vi;
    ("this",vi)::local_env
  in
  let req = Option_misc.map (assertion package_env type_env (Some current_type) local_env) req in
  let behs = List.map (behavior package_env type_env (Some current_type) local_env spec_env) behs in
  match eci with
    | Invoke_none -> 
	let body = statements package_env type_env (Some current_type) body_env body in
	Hashtbl.add constructors_table ci.constr_info_tag 
	  { ct_constr_info = ci;
	    ct_requires = req;
	    ct_behaviors = behs;
	    ct_body = body } 
    | Invoke_this _ | Invoke_super _ -> assert false (* TODO *)



let type_field_initializer package_env type_env ci fi =
  let (_,init) = 
    try
      Hashtbl.find field_prototypes_table fi.java_field_info_tag 
    with Not_found -> assert false
  in
  let tinit = 
    Option_misc.map (type_initializer package_env type_env (Some ci) [] fi.java_field_info_type) init 
  in
  Hashtbl.add fields_table fi.java_field_info_tag tinit
  
let type_decl package_env type_env d = 
    match d with
    | JPTclass c -> 
	(*
	  class_modifiers : modifiers;
	  class_name : identifier;
	  class_extends : qualified_ident option;
	  class_implements : qualified_ident list;
	  class_fields : field_declaration list
	*)
	begin
	  try
	    match List.assoc (snd c.class_name) type_env with	  
	      | TypeInterface _ -> assert false
	      | TypeClass ci as ti ->
		  List.iter (type_field_initializer package_env type_env ti) 
		    ci.class_info_fields;
		  List.iter (type_method_spec_and_body package_env type_env ti) 
		    ci.class_info_methods;
		  List.iter (type_constr_spec_and_body package_env type_env ti) 
		    ci.class_info_constructors
	  with
	      Not_found -> assert false
	end
    | JPTinterface i -> assert false (* TODO *)
    | JPTannot(loc,s) -> assert false
    | JPTaxiom((loc,id),e) -> 
	let te = assertion package_env type_env None [] e in
	Hashtbl.add axioms_table id te
    | JPTlogic_type_decl _ -> assert false (* TODO *)
    | JPTlogic_reads((loc,id),ret_type,params,reads) -> 
	let pl = List.map (type_param package_env type_env) params in
	let env = 
	  List.fold_left
	    (fun acc vi -> 
	       (vi.java_var_info_name,vi)::acc)
	    [] pl
	in
	begin match ret_type with
	  | None ->
	      let fi = logic_info id None pl in
	      let r = List.map (location package_env type_env None env) reads in
	      Hashtbl.add logics_env id fi;
	      Hashtbl.add logics_table fi.java_logic_info_tag (fi,JReads r)
	  | Some ty -> 
	      let fi = logic_info id (Some (type_type package_env type_env ty)) pl in
	      let r = List.map (location package_env type_env None env) reads in
	      Hashtbl.add logics_env id fi;
	      Hashtbl.add logics_table fi.java_logic_info_tag (fi,JReads r)
	end
    | JPTlogic_def((loc,id),ret_type,params,body) -> 
	let pl = List.map (type_param package_env type_env) params in
	let env = 
	  List.fold_left
	    (fun acc vi -> 
	       (vi.java_var_info_name,vi)::acc)
	    [] pl
	in
	begin match ret_type with
	  | None ->
	      let fi = logic_info id None pl in
	      let a = assertion package_env type_env None env body in
	      Hashtbl.add logics_env id fi;
	      Hashtbl.add logics_table fi.java_logic_info_tag (fi,JAssertion a)
	  | Some t -> 
	      let fi = logic_info id (Some (type_type package_env type_env t)) pl in
	      let a = term package_env type_env None env body in
	      Hashtbl.add logics_env id fi;
	      Hashtbl.add logics_table fi.java_logic_info_tag (fi,JTerm a)
	end
	


let get_bodies package_env type_env cu =
  List.iter (type_decl package_env type_env) cu.cu_type_decls


(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
