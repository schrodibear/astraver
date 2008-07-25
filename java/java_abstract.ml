
open Format
open Pp
open Java_env
open Java_ast

let base_type fmt b =
  match b with
    | Tshort -> fprintf fmt "short"
    | Tboolean -> fprintf fmt "boolean"
    | Tbyte -> fprintf fmt "byte"
    | Tchar -> fprintf fmt "char"
    | Tint -> fprintf fmt "int"
    | Tfloat -> fprintf fmt "float"
    | Tlong -> fprintf fmt "long"
    | Tdouble -> fprintf fmt "double"
	  (* native logic types *)
    | Tinteger | Treal | Tunit | Tstring ->  assert false (* TODO *)

let modifier fmt m =
  match m with
  | Static -> fprintf fmt "static "
  | Final -> assert false (* TODO *)
  | Public -> assert false (* TODO *)
  | Private -> assert false (* TODO *)
  | Protected -> assert false (* TODO *)
  | Native -> assert false (* TODO *)
  | Synchronized -> assert false (* TODO *)
  | Abstract -> assert false (* TODO *)
  | Transient (* "threadsafe" ? *) -> assert false (* TODO *)
  | Volatile-> assert false (* TODO *)
  | Strictfp -> assert false (* TODO *)
  | Ghost -> assert false (* TODO *)
  | Model-> assert false (* TODO *)
  | Non_null -> assert false (* TODO *)
  | Nullable -> assert false (* TODO *)
  | Annot_modifier(loc,id) -> assert false (* TODO *)

let type_expr fmt t =
  match t with
    | Base_type b -> base_type fmt b
    | Type_name id -> assert false (* TODO *)
    | Array_type_expr typ ->  assert false (* TODO *)

let literal fmt l =
  match l with
    | Null -> fprintf fmt "null"
    | _ -> assert false (* TODO *)
(*
    | Integer of string
    | Float of string
    | Bool of bool
    | String of string
    | Char of string
*)

let bin_op fmt op =
  match op with
    | Badd -> fprintf fmt "+"
(*
    | Bsub | Bmul | Bdiv | Bmod 
    | Band | Bor | Bimpl | Biff
    | Bbwand | Bbwor | Bbwxor
    | Blsl | Blsr | Basr
    | Beq 
*)
    | Bne -> fprintf fmt "!="
	(*
| Bgt | Blt | Ble | Bge
    | Bconcat (* + for Strings *)
*)
    | _ -> assert false (* TODO *)

let rec qualified_ident fmt qid =
  match qid with
    | [(_,id)] -> fprintf fmt "%s" id
    | (_,id)::l -> fprintf fmt "%s.%a" id qualified_ident l
    | [] -> assert false

let rec expr fmt e =
  match e.java_pexpr_node with
    | JPElit l -> literal fmt l
    | JPEbin(e1,op,e2) ->
	fprintf fmt "(%a %a %a)" expr e1 bin_op op expr e2
    | JPEname qid -> qualified_ident fmt qid
	
	
    | _ -> assert false (* TODO *)
(*
    | JPEun of un_op * pexpr                 (*r (pure) unary operations *)
    | JPEincr of incr_decr_op * pexpr (*r pre-post incr/decr operations *)
    | JPEassign_name of qualified_ident * bin_op * pexpr  
    | JPEassign_field of java_field_access * bin_op * pexpr  
    | JPEassign_array of pexpr * pexpr * bin_op * pexpr  
	(*r [Assign_array(e1,e2,op,e3)] is [e1[e2] op e3] *)
	(*r assignment op is =, +=, etc. *)
    | JPEif of pexpr * pexpr * pexpr
    | JPEthis
    | JPEfield_access of java_field_access
    | JPEcall_name of qualified_ident * pexpr list
    | JPEcall_expr of pexpr * identifier * pexpr list
    | JPEsuper_call of identifier * pexpr list
    | JPEnew of qualified_ident * pexpr list
    | JPEnew_array of type_expr * pexpr list 
	(*r type, explicit dimensions *)
    | JPEarray_access of pexpr * pexpr
    | JPEarray_range of pexpr * pexpr option * pexpr option
    | JPEcast of type_expr * pexpr
    | JPEinstanceof of pexpr * type_expr
	(* in annotations only *)
    | JPEresult  
    | JPEold of pexpr 
    | JPEat of pexpr * identifier 
    | JPEquantifier of quantifier * (type_expr * variable_id list) list * pexpr   
*)

let rec param fmt p =
  match p with
    | Simple_parameter(modifier, typ, (loc,id)) ->
	fprintf fmt "%a %s" type_expr typ id
    | Array_parameter p -> 
	fprintf fmt "%a[]" param p

let method_declarator fmt d =
  match d with
    | Simple_method_declarator((_,id),params) ->
	fprintf fmt "%s(%a);@\n@\n" id (print_list comma param) params
    | Array_method_declarator md ->
	assert false (* TODO *)


let method_declaration fmt md =
  (*
    method_modifiers : modifiers ;
    method_return_type : type_expr option ;
    method_declarator : method_declarator ;
    method_throws : qualified_ident list ;
  *)
  List.iter (modifier fmt) md.method_modifiers;
  begin
    match md.method_return_type with
      | None -> fprintf fmt "void "
      | Some t -> fprintf fmt "%a " type_expr t;
  end;
  method_declarator fmt md.method_declarator
  

let field_declaration fmt f =
(*
  | JPFmethod of method_declaration * block option
  | JPFconstructor of constructor_declaration *
      explicit_constructor_invocation * block
  | JPFvariable of variable_declaration
  | JPFstatic_initializer of block
  | JPFannot of Lexing.position * string
  | JPFinvariant of identifier * pexpr
  | JPFstatic_invariant of identifier * pexpr
  | JPFmethod_spec of 
      pexpr option * pexpr option * (identifier * pbehavior) list
  | JPFclass of class_declaration
  | JPFinterface of interface_declaration
*)
  match f with
    | JPFmethod(md,_block) -> method_declaration fmt md      
    | JPFmethod_spec(req, dec, behs ) -> 
	fprintf fmt "@[/*@@";
	print_option (fun fmt e -> fprintf fmt " requires %a;@\n  @@" expr e) fmt req;
	(* TODO *)
	fprintf fmt "*/@\n@]";	
    | _ -> assert false (* TODO *)

let class_declaration fmt cd =
(*
  class_modifiers : modifiers;
  class_name : identifier;
  class_extends : qualified_ident option;
  class_implements : qualified_ident list;
  class_fields : field_declaration list
*)
  fprintf fmt "@[class %s {@\n@\n  @[<v 0>" (snd cd.class_name);
  List.iter (field_declaration fmt) cd.class_fields;
  fprintf fmt "@]@\n}@\n@]"

let type_declaration fmt d =
  match d with
    | JPTclass cd -> class_declaration fmt cd
    | JPTinterface interface_declaration -> assert false
    | JPTannot _ -> assert false
    | JPTlemma (id,is_axiom,labels,p) -> assert false
    | JPTlogic_type_decl id -> assert false
    | JPTlogic_reads(id,rettype,labels,params,reads) -> assert false
    | JPTlogic_def(id,rettype,labels,param,e) -> assert false
	

let compilation_unit fmt cu =
  (*
    cu_package : qualified_ident;
    cu_imports : import_statement list;
  *)
  List.iter (type_declaration fmt) cu.cu_type_decls

