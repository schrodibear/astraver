
(*

  Performs several analyses after Java typing and before interpretation into Jessie code.

  1) determines which structure type to introduce for arrays
  2) disambiguates names:
     . different constructors for the same class are named
         Class_typearg1_..._typeargn

*)

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
    | Tunit -> "unit"
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
    | JEun (_, e1) -> expr e1
    | JEbin (e1, op, e2) -> expr e1; expr e2 
    | JEvar vi -> ()
    | JEstatic_field_access(ci,fi) -> ()
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
    | JEcall(e,mi,args) ->
	expr e;	List.iter expr args
    | JEstatic_call(mi,args) ->
	List.iter expr args
    | JEnew_array(ty,dims) ->
	List.iter expr dims
    | JEnew_object(ci,args) ->
	List.iter expr args
    | JEcast(_,e) -> expr e

let initialiser i = 
  match i with
    | JIexpr e -> expr e
    | _ -> assert false (* TODO *)

let switch_label = function
  | Java_ast.Default -> ()
  | Java_ast.Case e -> expr e
  
let rec statement s =
  match s.java_statement_node with
    | JSskip | JSbreak _ -> ()
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
    | JSthrow e
    | JSreturn e 
    | JSexpr e -> expr e
    | JSassert(id,e) -> assertion e
    | JSswitch(e,l) -> 
	expr e;
	List.iter (fun (labels,b) ->
		     List.iter switch_label labels;
		     List.iter statement b)
	  l
    | JStry(s, catches, finally) ->
	List.iter statement s;
	List.iter (fun (_,s) -> List.iter statement s) catches;
	Option_misc.iter (List.iter statement) finally

let do_method mi req behs body =
(*
  Option_misc.iter assertion req;
  ... behs
*)
  Option_misc.iter (List.iter statement) body


let do_constructor ci reg behs body =
  let l = ci.constr_info_class.class_info_constructors in
  if List.length l >= 2 then
    begin
      ci.constr_info_trans_name <-
	ci.constr_info_class.class_info_name ^
	(List.fold_right
	   (fun vi acc ->
	      "_" ^ name_type vi.java_var_info_type ^ acc)
	   ci.constr_info_parameters "")
    end;
  List.iter statement body


(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)

