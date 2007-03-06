(***************************************************************************

Abstract syntax trees for Java source files

$Id: java_ast.mli,v 1.1 2007-03-06 10:44:18 marche Exp $

***************************************************************************)

open Java_env

(*s Qualified identifiers *)

type identifier = Loc.position * string

type qualified_ident = identifier list

(*s Modifiers *)
 
type modifier =
    [ `STATIC | `FINAL | `GHOST | `PUBLIC | `PRIVATE | `PROTECTED | `NATIVE 
    | `SYNCHRONIZED | `ABSTRACT | `TRANSIENT (* "threadsafe" ? *)
    | `PURE | `SPEC_PUBLIC | `MODEL ]  

type modifiers = modifier list

(*s type expressions *)

type type_expr = 
  | Base_type of string
  | Type_name of qualified_ident
  | Array_type_expr of type_expr
;;
 
(*s literals *)

type literal =
  | Integer of string
  | Float of string
  | Bool of bool
  | String of string
  | Char of string
  | Null

(*s expressions *)

type quantifier = Forall | Exists;;

type variable_id =
  | Simple_id of identifier
  | Array_id of variable_id
;;

type incr_decr_op = Preincr | Predecr | Postincr | Postdecr 

type bin_op = 
    | Badd | Bsub | Bmul | Bdiv | Bmod 
    | Band | Bor | Bimpl
    | Bbwand | Bbwor | Bbwxor
    | Blsl | Blsr | Basr
    | Beq | Bne | Bgt | Blt | Ble | Bge

type un_op = Uplus | Uminus | Unot | Ucompl

type java_field_access =
  | Super_access of identifier
  | Primary_access of pexpr * identifier
  | Array_length of pexpr

and pexpr =
  { java_pexpr_loc : Loc.position ;
    java_pexpr_node : pexpr_node }

and pexpr_node =
  | JPElit of literal
  | JPEbin of pexpr * bin_op * pexpr         (*r binary operations *)
  | JPEun of un_op * pexpr                 (*r (pure) unary operations *)
  | JPEincr of incr_decr_op * pexpr (*r pre-post incr/decr operations *)
  | JPEvar of identifier
(*
  | Static_class of class_entry
  | Static_interface of interface_entry
*)
  | Assign_name of qualified_ident * string * pexpr  
(*
  | Assign_local_var of local_variable_entry * string * expr  
*)
  | JPEassign_field of java_field_access * string * pexpr  
  | JPEassign_array of pexpr * pexpr * string * pexpr  
      (*r [Assign_array(e1,e2,op,e3)] is [e1[e2] op e3] *)
      (*r assignment op is =, +=, etc. *)
  | JPEif of pexpr * pexpr * pexpr
  | JPEthis
  | JPEfield_access of java_field_access
  | Method_call of pexpr option * identifier * pexpr list
  | Super_method_call of identifier * pexpr list
(*
  | Logic_call of logic_entry * expr list
*)
  | Class_instance_creation of qualified_ident * pexpr list
  | Array_creation of array_creation
  | Array_access of pexpr * pexpr
  | Cast of type_expr * pexpr
  | Instanceof of pexpr * type_expr
      (* in annotations only *)
  | JPEresult  
  | JPEold of pexpr 
(*
  | JPEfresh of expr 
  | Type of type_expr 
  | Typeof of expr 
*)
  | JPEquantifier of quantifier * type_expr * variable_id list * pexpr   

and array_creation =
  | Explicit_array_creation of pexpr * array_creation
  | Implicit_array_creation of type_expr

(*
and set_ref = 
  | Set_array_index of expr  
      (*r e[e] *)
  | Set_array_interval of expr * expr  
      (*r e[e..e] *)
  | Set_array
      (*r e[*] *)
  | Set_field of instance_variable_entry
      (* e.f *)
  | Set_fieldraw of identifier
*)

(*s variable declarations *)
      
type variable_initializer =
  | Simple_initializer of pexpr
  | Array_initializer of variable_initializer list

type variable_declarator = 
    { variable_id : variable_id ;
      variable_initializer : variable_initializer option }
 
      
type variable_declaration =
    { variable_modifiers : modifiers ;
      variable_type : type_expr ;
      variable_decls : variable_declarator list }


(*s formal parameters *)

type parameter =
  | Simple_parameter of type_expr * identifier
  | Array_parameter of parameter

(*s KML annotations *)

(*
type kml_method_specification =
  { kml_requires : pexpr;
    (* TODO *)
  }

type kml_loop_annotation =
    { kml_loop_invariant : pexpr;
      kml_loop_assigns : pexpr list option; 
      (*r None: everything, Some []: nothing *)
      kml_loop_variant : pexpr;
    }
     
type kml_declaration =
  | Kml_invariant of pexpr

type kml_specification =
  | Kml_declaration of kml_declaration list
  | Kml_method_specification of kml_method_specification
  | Kml_loop_annotation of kml_loop_annotation
  | Kml_assertion of pexpr
  | Kml_axiom of identifier * pexpr
  | Kml_logic_type of identifier
      (*r todo: polymorphic logic types *)
  | Kml_logic_reads of identifier * type_expr option * parameter list * pexpr list
      (*r id, return type (None for Prop), params, reads *)
  | Kml_logic_def of identifier * type_expr option * parameter list * pexpr
      (*r id, return type (None for Prop), params, body *)
*)

(*s statements *)

type switch_label =
  | Case of pexpr
  | Default

type pstatement =
  { java_pstatement_loc : Loc.position ;
    java_pstatement_node : pstatement_node }

and pstatement_node =
  | JPSskip                  (*r empty statement *)
  | JPSexpr of pexpr
  | JPSvar_decl of variable_declaration
  | JPSthrow of pexpr
  | JPSreturn of pexpr option
  | JPSbreak of identifier option
  | JPScontinue of identifier option
  | JPSlabel of identifier * pstatement
  | JPSif of pexpr * pstatement * pstatement
  | JPSwhile of pexpr * pstatement
  | JPSdo of pstatement * pexpr
  | JPSfor of pstatement list * pexpr * pstatement list * pstatement  
  | JPSfor_decl of variable_declaration * pexpr * pstatement list * pstatement
  | JPStry of block * (parameter * block) list * block option
  | JPSswitch of pexpr * (switch_label list * block) list
  | JPSblock of block
  | JPSsynchronized of pexpr * block
  | JPSassert of pexpr
  | JPSannot of Lexing.position * string
(*
  | Kml_annot_statement of jml_annotation_statement
  | Kml_ghost_var_decl of jml_declaration list
  | Annotated of statement_specification * statement
*)

and block = pstatement list
;;

(*s method declarations *)

type method_declarator =
  | Simple_method_declarator of identifier * parameter list
  | Array_method_declarator of method_declarator
;;

type method_declaration =
    { (* method_specification : kml_method_specification option; *)
      method_modifiers : modifiers ;
      method_return_type : type_expr option ;
      method_declarator : method_declarator ;
      method_throws : qualified_ident list }
;;

(*s constructor declarations *)


type explicit_constructor_invocation =
  | Invoke_none
  | Invoke_this of pexpr list
  | Invoke_super of pexpr list

type constructor_declaration =
    { (* constr_specification : kml_method_specification option; *)
      constr_modifiers : modifiers ;
      constr_name : identifier ;
      constr_parameters : parameter list ;
      constr_throws : qualified_ident list;
      constr_body : explicit_constructor_invocation * block }
;;

      
      
      
(*s class declarations *)

type field_declaration =
  | JPFmethod of method_declaration * block option
  | JPFconstructor of constructor_declaration 
  | JPFvariable of variable_declaration
  | JPFstatic_initializer of block
  | JPFannot of Lexing.position * string
  | JPFinvariant of identifier * pexpr
  | JPFmethod_spec of pexpr option * 
      (identifier * (pexpr option * pexpr option * pexpr)) list
;;


type class_declaration =
    { 
      class_modifiers : modifiers;
      class_name : identifier;
      class_extends : qualified_ident option;
      class_implements : qualified_ident list;
      class_fields : field_declaration list
    }

(*s interface declarations *)

type interface_member_declaration =
  | JPIMconstant of variable_declaration
  | JPIMmethod of method_declaration
  | Model_variable of variable_declaration
  | JPIMannot of Lexing.position * string
;;

type interface_declaration =
    { interface_modifiers : modifiers;
      interface_name : identifier;
      interface_extends : qualified_ident list;
      interface_members : interface_member_declaration list
    }
;;

(*s compilation units *)

type type_declaration =
  | JPTclass of class_declaration
  | JPTinterface of interface_declaration
  | JPTannot of Lexing.position * string
  | JPTaxiom of identifier * pexpr
  | JPTlogic_type_decl of identifier 
  | JPTlogic_reads of identifier * type_expr option * parameter list * pexpr list 
  | JPTlogic_def of identifier * type_expr option * parameter list * pexpr 

type import_statement =
  | Import_package of qualified_ident
  | Import_class_or_interface of qualified_ident

type compilation_unit =
    {
      cu_package : qualified_ident;
      cu_imports : import_statement list;
      cu_type_decls : type_declaration list
    }

(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
