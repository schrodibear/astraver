

val methods_table : 
  (int,
   Java_env.method_info * 
   Java_tast.assertion option * 
   (Java_ast.identifier * 
    Java_tast.assertion option * 
    unit option * Java_tast.assertion) list *
   Java_tast.block option) Hashtbl.t

exception Typing_error of Loc.position * string

val compilation_unit : Java_ast.compilation_unit -> unit



(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
