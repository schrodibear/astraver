

val class_table :
  (string,Java_env.java_class_info) Hashtbl.t

type method_table_info =
    { mt_method_info : Java_env.method_info;
      mt_requires : Java_tast.assertion option;
      mt_behaviors : (Java_ast.identifier * 
			Java_tast.assertion option * 
			Java_tast.term list option * 
			Java_tast.assertion) list ;
      mt_body : Java_tast.block option;
    }

val methods_table : 
  (int, method_table_info) Hashtbl.t


val axioms_table : (string,Java_tast.assertion) Hashtbl.t

type logic_body =
  | JAssertion of Java_tast.assertion
  | JTerm of Java_tast.term
  | JReads of Java_tast.term list

val logics_table : 
  (int,Java_env.java_logic_info * logic_body) Hashtbl.t

exception Typing_error of Loc.position * string

val get_types : Java_ast.compilation_unit -> unit
val get_prototypes: Java_ast.compilation_unit -> unit
val get_bodies : Java_ast.compilation_unit -> unit



(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)
