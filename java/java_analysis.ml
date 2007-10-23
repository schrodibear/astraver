
(*

  Performs several analyses after Java typing and before interpretation into Jessie code.

  1) determines which structure type to introduce for arrays
  2) disambiguates names:
     . different constructors for the same class are named
         Class_typearg1_..._typeargn
     . methods
         * with same names in different classes or interfaces
             Class_or_Interface_method_name
         * with same names in same class or interface
             Class_or_Interface_method_name_typearg1_..._typeargn

*)

open Java_pervasives
open Java_env
open Java_tast
open Format

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
    | JTYclass(_,c) -> c.class_info_name
    | JTYinterface i -> i.interface_info_name
    | JTYarray ty -> name_type ty ^ "A"
    | JTYnull -> assert false

let rec intro_array_struct t =
  try
    let _ = Hashtbl.find array_struct_table t in ()
  with Not_found ->
    let n = name_type t in 
    Java_options.lprintf "Adding array struct for type %s@." n;
    Hashtbl.add array_struct_table t (n ^ "M", n ^ "P")

let term t = () (* TODO *)

let assertion a = () (* TODO *)

let rec expr e = 
  match e.java_expr_node with
    | JElit l -> ()
    | JEincr_local_var(op,v) -> ()
    | JEincr_field(op,e1,fi) -> expr e1
    | JEun (_, e1) -> expr e1
    | JEbin (e1, _, e2) | JEincr_array (_, e1, e2) -> expr e1; expr e2 
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
    | JEassign_local_var (_, e)
    | JEassign_local_var_op (_, _, e)
    | JEassign_static_field (_, e) 
    | JEassign_static_field_op (_, _, e) -> expr e
    | JEassign_field(e1,fi,e2) -> expr e1; expr e2
    | JEassign_field_op(e1,fi,op,e2) -> expr e1; expr e2
    | JEif(e1,e2,e3) -> expr e1; expr e2; expr e3
    | JEassign_array(e1,e2,e3) 
    | JEassign_array_op(e1,e2,_,e3) -> 
	expr e1; expr e2; expr e3;
	begin
	  match e1.java_expr_type with
	    | JTYarray ty -> intro_array_struct ty
	    | _ -> 
		eprintf "unexpected type: e1:%a e2:%a e3:%a@." 
		  Java_typing.print_type e1.java_expr_type
		  Java_typing.print_type e2.java_expr_type
		  Java_typing.print_type e3.java_expr_type;
		assert false
	end
    | JEcall(e,mi,args) ->
	expr e;	List.iter expr args
    | JEconstr_call (e, _, args) ->
	expr e; List.iter expr args
    | JEstatic_call(mi,args) ->
	List.iter expr args
    | JEnew_array(ty,dims) ->
	List.iter expr dims
	(* intro_array_struct ty ??? *)
    | JEnew_object(ci,args) ->
	List.iter expr args
    | JEinstanceof(e,_)
    | JEcast(_,e) -> expr e

let do_initializer i = 
  match i with
    | JIexpr e -> expr e
    | _ -> assert false (* TODO *)

let switch_label = function
  | Java_ast.Default -> ()
  | Java_ast.Case e -> expr e
  
let rec statement s =
  match s.java_statement_node with
    | JSskip 
    | JSreturn_void
    | JSbreak _ -> ()
    | JSblock l -> List.iter statement l	  
    | JSvar_decl (vi, init, s) ->
	Option_misc.iter do_initializer init;
	statement s
    | JSif (e, s1, s2) -> expr e; statement s1; statement s2
    | JSwhile(e,inv,dec,s) ->
	  expr e; assertion inv; term dec; statement s
    | JSfor (el1, e, inv, dec, el2, body) ->
	List.iter expr el1;
	expr e;
	assertion inv;
	term dec;
	List.iter expr el2;
	statement body
    | JSfor_decl(decls,e,inv,dec,sl,body) ->
	List.iter 
	  (fun (_,init) -> Option_misc.iter do_initializer init) decls;
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

let param vi =
  match vi.java_var_info_type with
    | JTYarray ty -> intro_array_struct ty
    | _ -> ()

let do_method mi req behs body =
(*
  Option_misc.iter assertion req;
  ... behs
*)
  List.iter param mi.method_info_parameters;
  Option_misc.iter (List.iter statement) body;
  Option_misc.iter param mi.method_info_result


let string_of_parameters vil =
  (List.fold_right
     (fun vi acc -> "_" ^ name_type vi.java_var_info_type ^ acc) vil "")

let do_constructor ci reg behs body =
(*
  let l = ci.constr_info_class.class_info_constructors in
  if List.length l >= 2 then
    begin
*)
      ci.constr_info_trans_name <-
	"cons_" ^ ci.constr_info_class.class_info_name ^
	string_of_parameters ci.constr_info_parameters;
(*
    end;
*)
  List.iter statement body

let do_field fi =
  match fi.java_field_info_type with
    | JTYarray ty -> intro_array_struct ty
    | _ -> ()

let do_type ty =
  match ty with
    | TypeClass ci -> 
	List.iter do_field ci.class_info_fields
    | TypeInterface ii -> 
	List.iter do_field ii.interface_info_fields


let disambiguates_method_names () =
  let methods_list =
    Hashtbl.fold (fun _ mt acc -> mt :: acc) Java_typing.methods_table []
  in
  let methods_list =
    List.sort 
      (fun mt1 mt2 -> 
	 let mi1 = mt1.Java_typing.mt_method_info in
	 let mi2 = mt2.Java_typing.mt_method_info in
	   (* compare method names *)
	   match String.compare mi1.method_info_name mi2.method_info_name with
	     | 0 ->
		 (* compare method class or interface names *)
		 begin
		   let ci1 = get_method_info_class_or_interface_name mi1 in
		   let ci2 = get_method_info_class_or_interface_name mi2 in
		     mi1.method_info_trans_name <-
		       ci1 ^ "_" ^ mi1.method_info_name; 
		     mi2.method_info_trans_name <-
		       ci2 ^ "_" ^ mi2.method_info_name;
		     match String.compare ci1 ci2
		     with
		       | 0 ->			 
			   mi1.method_info_trans_name <-
			     mi1.method_info_trans_name ^
			     string_of_parameters
			     mi1.method_info_parameters;
			   mi2.method_info_trans_name <-
			     mi2.method_info_trans_name ^
			     string_of_parameters
			     mi2.method_info_parameters; 0
		       | n -> n
		 end
	     | n -> n)
      methods_list 
  in
    List.iter
      (fun mt -> Hashtbl.replace Java_typing.methods_table
	 mt.Java_typing.mt_method_info.method_info_tag mt)
      methods_list


(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)

