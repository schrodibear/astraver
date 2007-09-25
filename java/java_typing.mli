
val print_qualified_ident : Format.formatter -> Java_ast.qualified_ident -> unit

val print_type : Format.formatter -> Java_env.java_type -> unit

type type_data =
  | TypeDataClass of Java_env.java_class_info * Java_ast.class_declaration
  | TypeDataInterface of Java_env.interface_info * Java_ast.interface_declaration

val type_table : (int, type_data) Hashtbl.t 

type method_table_info =
    { mt_method_info : Java_env.method_info;
      mt_requires : Java_tast.assertion option;
      mt_assigns : Java_tast.term list option;
      mt_behaviors : (Java_ast.identifier * 
			Java_tast.assertion option * 
			Java_env.java_class_info option *
			Java_tast.term list option * 
			Java_tast.assertion) list ;
      mt_body : Java_tast.block option;
    }

val methods_table : 
  (int, method_table_info) Hashtbl.t

type constructor_table_info =
    { ct_constr_info : Java_env.constructor_info;
      ct_requires : Java_tast.assertion option;
      ct_assigns : Java_tast.term list option;
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

val constructors_table : 
  (int, constructor_table_info) Hashtbl.t

val fields_table : 
  (int, Java_tast.initialiser option) Hashtbl.t

val axioms_table : (string,Java_tast.assertion) Hashtbl.t

type logic_body =
  | JAssertion of Java_tast.assertion
  | JTerm of Java_tast.term
  | JReads of Java_tast.term list

val is_numeric : Java_env.java_type -> bool 

val logics_table : 
  (int,Java_env.java_logic_info * logic_body) Hashtbl.t

exception Typing_error of Loc.position * string

val get_types : 
  Java_ast.compilation_unit -> 
  Java_env.package_info list * 
    (string * Java_env.java_type_info) list

val get_prototypes: 
  Java_env.package_info list ->
  (string * Java_env.java_type_info) list ->
  Java_ast.compilation_unit -> unit

val get_bodies : 
  Java_env.package_info list ->
  (string * Java_env.java_type_info) list ->
  Java_ast.compilation_unit -> unit



(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)
