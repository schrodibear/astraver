

open Java_env
open Java_tast

let array_struct_table = Hashtbl.create 17

let name_base_type t =
  match t with
    | Tboolean -> "boolean"
    | Tchar -> "char"
    | Tbyte -> "byte"
    | Tinteger -> "integer" 
    | Tshort -> "short"
    | Tlong -> "long"
    | Tint -> "int" 
    | Tnull -> assert false (* "null" ?? *)
    | Tfloat -> "float"
    | Treal -> "real"
    | Tdouble -> "double"

let rec name_type t =
  match t with
    | JTYbase t -> name_base_type t
    | _ -> assert false (* TODO *)

let rec intro_array_struct t =
  try
    let _ = Hashtbl.find array_struct_table t in ()
  with Not_found ->
    let n = name_type t in 
    Hashtbl.add array_struct_table t (n ^ "M", n ^ "P")

let term t = () (* TODO *)

let assertion a = () (* TODO *)

let rec expr e = 
  match e.java_expr_node with
    | JElit l -> ()
    | JEincr_local_var(op,v) -> ()
    | JEun (_, _) -> assert false (* TODO *)
    | JEbin (e1, op, e2) -> expr e1; expr e2 
    | JEvar vi -> ()
    | JEfield_access(e1,fi) -> expr e1
    | JEarray_length(e) -> 
	begin
	  match e.java_expr_type with
	    | JTYarray ty -> intro_array_struct ty 
	    | _ -> assert false
	end
    | JEarray_access(e1,e2) -> 
	expr e1; expr e2;
	begin
	  match e1.java_expr_type with
	    | JTYarray ty -> intro_array_struct ty
	    | _ -> assert false
	end
    | JEassign_local_var(vi,e) -> expr e
    | JEassign_local_var_op(vi,op,e) -> expr e
    | JEassign_field(e1,fi,e2) -> expr e1; expr e2
    | JEassign_field_op(e1,fi,op,e2) -> expr e1; expr e2
    | JEassign_array_op(e1,e2,op,e3) -> expr e1; expr e2; expr e3


let initialiser i = 
  match i with
    | JIexpr e -> expr e
    | _ -> assert false (* TODO *)

let rec statement s =
  match s.java_statement_node with
    | JSskip -> ()
    | JSreturn e -> expr e
    | JSblock l -> List.iter statement l	  
    | JSvar_decl (vi, init, s) ->
	Option_misc.iter initialiser init;
	statement s
    | JSif (e, s1, s2) -> expr e; statement s1; statement s2
    | JSwhile(e,inv,dec,s) ->
	  expr e; assertion inv; term dec; statement s
    | JSfor_decl(decls,e,inv,dec,sl,body) ->
	List.iter 
	  (fun (_,init) -> Option_misc.iter initialiser init) decls;
	expr e;
	assertion inv;
	term dec;
	List.iter expr sl;
	statement body
    | JSexpr e -> expr e
    | JSassert(id,e) -> assertion e

let do_method mi req behs body =

(*
  Option_misc.iter assertion req;
  ... behs
*)
  Option_misc.iter (List.iter statement) body


(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)

