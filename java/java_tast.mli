
open Java_env

(*
type var_info =
    {
      java_var_info_tag : int;
      java_var_info_name : string;
      java_var_info_final_name : string;
      java_var_info_type : java_type;
      java_var_info_assigned : bool;
    }

type logic_info =
    {
      java_logic_info_name : string;
      java_logic_info_tag : int;
      java_logic_info_result_type : java_type option;
      java_logic_info_parameters : var_info list;
(*
      java_logic_info_effects = empty_effects;
*)
      java_logic_info_calls : logic_info list;
    }
*)

type bin_op = Java_ast.bin_op
type un_op = Java_ast.un_op
type incr_decr_op = Java_ast.incr_decr_op

type term_node =
    | JTlit of literal
    | JTvar of java_var_info
    | JTapp of java_logic_info * term list

and term =
    { java_term_node : term_node;
      java_term_loc : Loc.position;
    }


type quantifier = Java_ast.quantifier

type assertion_node =
    | JAtrue
    | JAfalse
    | JAand of assertion * assertion
    | JAor of assertion * assertion
    | JAimpl of assertion * assertion
    | JAquantifier of quantifier * java_var_info * assertion
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
  | JEincr of incr_decr_op * expr (*r pre-post incr/decr operations *)
(*
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
(*
  | Type of type_expr 
  | Typeof of expr 
*)
*)

(* statements *)

type initialiser =
  | JIexpr of expr
  | JIlist of initialiser list

type statement =
  { java_statement_loc : Loc.position ;
    java_statement_node : statement_node }

and statement_node =
  | JSskip                  (*r empty statement *)
  | JSif of expr * statement * statement
  | JSreturn of expr
  | JSvar_decl of java_var_info * initialiser option * statement
  | JSblock of block
(*
  | JSexpr of expr
  | JSvar_decl of variable_declaration
  | JPSthrow of pexpr
  | JPSbreak of identifier option
  | JPScontinue of identifier option
  | JPSlabel of identifier * pstatement
  | JPSwhile of pexpr * pstatement
  | JPSdo of pstatement * pexpr
  | JPSfor of pstatement list * pexpr * pstatement list * pstatement  
  | JPSfor_decl of variable_declaration * pexpr * pstatement list * pstatement
  | JPStry of block * (parameter * block) list * block option
  | JPSswitch of pexpr * (switch_label list * block) list
  | JPSsynchronized of pexpr * block
  | JPSassert of pexpr
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
