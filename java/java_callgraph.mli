
val compute_logic_calls : Java_env.java_logic_info -> [< Java_typing.logic_decl_body] -> unit

val compute_calls : Java_env.method_info -> 'a -> Java_tast.statement list -> unit

val compute_constr_calls : Java_env.constructor_info -> 'a -> Java_tast.statement list -> unit

val compute_logic_components : 
  (int, (Java_env.java_logic_info * Java_typing.logic_def_body)) Hashtbl.t -> 
  Java_env.java_logic_info list array

val compute_components : 
  (int, Java_typing.method_table_info) Hashtbl.t -> 
  (int, Java_typing.constructor_table_info) Hashtbl.t -> 
  Java_env.method_or_constructor_info list array

