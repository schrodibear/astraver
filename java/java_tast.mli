
open Java_env

type bin_op = Java_ast.bin_op
type un_op = Java_ast.un_op
type incr_decr_op = Java_ast.incr_decr_op

type term_node =
    | JTlit of literal
    | JTvar of java_var_info
    | JTold of term
    | JTbin of term * base_type * bin_op * term   
    | JTapp of java_logic_info * term list
    | JTfield_access of term * java_field_info
    | JTstatic_field_access of java_class_info * java_field_info
    | JTarray_length of term 
    | JTarray_access of term * term

and term =
    { java_term_node : term_node;
      java_term_type : java_type;
      java_term_loc : Loc.position;
    }


type quantifier = Java_ast.quantifier

type assertion_node =
    | JAtrue
    | JAfalse
    | JAnot of assertion 
    | JAand of assertion * assertion
    | JAor of assertion * assertion
    | JAimpl of assertion * assertion
    | JAiff of assertion * assertion
    | JAquantifier of quantifier * java_var_info * assertion
    | JAbool_expr of term
    | JAbin of term * base_type * bin_op * term   
    | JAapp of java_logic_info * term list

and assertion =
    { java_assertion_node : assertion_node;
      java_assertion_loc : Loc.position;
    }

(* expressions *)

type expr =
  { java_expr_loc : Loc.position ;
    java_expr_type : java_type;
    java_expr_node : expr_node }

and expr_node =
  | JElit of literal
  | JEvar of java_var_info
  | JEbin of expr * bin_op * expr         (*r binary operations *)
  | JEun of un_op * expr                 (*r (pure) unary operations *)
  | JEincr_local_var of incr_decr_op * java_var_info
      (*r pre-post incr/decr operations *)
  | JEstatic_field_access of java_class_info * java_field_info
  | JEfield_access of expr * java_field_info
  | JEarray_length of expr 
  | JEarray_access of expr * expr
  | JEassign_local_var of java_var_info * expr  
  | JEassign_local_var_op of java_var_info * bin_op * expr  
  | JEassign_field of expr * java_field_info * expr
  | JEassign_field_op of expr * java_field_info * bin_op * expr
  | JEassign_array_op of expr * expr * bin_op * expr
  | JEcall of expr * method_info * expr list
  | JEstatic_call of method_info * expr list
(*
  | Static_class of class_entry
  | Static_interface of interface_entry
  | Assign_name of qualified_ident * string * pexpr  
  | JPEassign_field of java_field_access * string * pexpr  
  | JPEassign_array of pexpr * pexpr * string * pexpr  
      (*r [Assign_array(e1,e2,op,e3)] is [e1[e2] op e3] *)
      (*r assignment op is =, +=, etc. *)
  | JPEif of pexpr * pexpr * pexpr
  | JPEthis
  | Super_method_call of identifier * pexpr list
  | Logic_call of logic_entry * expr list
  | Class_instance_creation of qualified_ident * pexpr list
  | Array_creation of array_creation
  | Cast of type_expr * pexpr
  | Instanceof of pexpr * type_expr
      (* in annotations only *)
  | Type of type_expr 
  | Typeof of expr 
*)

(* statements *)

type initialiser =
  | JIexpr of expr
  | JIlist of initialiser list

type 'a switch_label = 'a Java_ast.switch_label
type statement =
  { java_statement_loc : Loc.position ;
    java_statement_node : statement_node }

and statement_node =
  | JSskip                  (*r empty statement *)
  | JSif of expr * statement * statement
  | JSreturn of expr
  | JSvar_decl of java_var_info * initialiser option * statement
  | JSblock of block
  | JSwhile of expr * assertion * term * statement  
      (*r condition, invariant, variant, loop body *)
  | JSfor_decl of (java_var_info * initialiser option) list * expr * assertion * term * expr list * statement  
      (*r decls, condition, invariant, variant, steps, loop body *)
  | JSexpr of expr
  | JSassert of string option * assertion
  | JSswitch of expr * (expr switch_label list * block) list
  | JSbreak of string option
(*
  | JSvar_decl of variable_declaration
  | JPSthrow of pexpr
  | JPScontinue of identifier option
  | JPSlabel of identifier * pstatement
  | JPSdo of pstatement * pexpr
  | JPSfor of pstatement list * pexpr * pstatement list * pstatement  
  | JPSfor_decl of variable_declaration * pexpr * pstatement list * pstatement
  | JPStry of block * (parameter * block) list * block option
  | JPSsynchronized of pexpr * block
  | JPSannot of Lexing.position * string
  | JPSloop_annot of pexpr * pexpr
*)
(*
  | Kml_annot_statement of jml_annotation_statement
  | Kml_ghost_var_decl of jml_declaration list
  | Annotated of statement_specification * statement
*)

and block = statement list
;;

(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
