

open Jc_output
open Jc_env
open Jc_ast
open Java_env
open Java_ast
open Java_tast

(*s range types *)

(* byte = int8 *)
let byte_range =
  {
    jc_enum_info_name = "byte";
    jc_enum_info_min = Num.num_of_string "-128";
    jc_enum_info_max = Num.num_of_string "127";
  }

(* short = int16 *)
let short_range =
  {
    jc_enum_info_name = "short";
    jc_enum_info_min = Num.num_of_string "-32768";
    jc_enum_info_max = Num.num_of_string "32767";
  }

(* int = int32 *)
let int_range =
  {
    jc_enum_info_name = "int32";
    jc_enum_info_min = Num.num_of_string "-2147483648";
    jc_enum_info_max = Num.num_of_string "2147483647";
  }

(* long = int64 *)
let long_range =
  {
    jc_enum_info_name = "long";
    jc_enum_info_min = Num.num_of_string "-9223372036854775808";
    jc_enum_info_max = Num.num_of_string "9223372036854775807";
  }

(* char = uint16 *)
let char_range =
  {
    jc_enum_info_name = "char";
    jc_enum_info_min = Num.num_of_string "0";
    jc_enum_info_max = Num.num_of_string "65535";
  }

let range_types acc =
  List.fold_left
    (fun acc ri ->
       JCenum_type_def(ri.jc_enum_info_name,
			ri.jc_enum_info_min,
			ri.jc_enum_info_max)::acc) 
    acc [ byte_range ; short_range ; int_range ; long_range ; char_range ]

let tr_base_type t =
  match t with
    | Tboolean -> JCTnative Jc_env.Tboolean
    | Tinteger -> JCTnative Jc_env.Tinteger
    | Tshort -> JCTenum short_range 
    | Tint -> JCTenum int_range 
    | Tnull -> JCTnull
    | Treal -> assert false (* TODO *)
    | Tdouble -> assert false (* TODO *)
    | Tlong -> JCTenum long_range 
    | Tfloat -> assert false (* TODO *)
    | Tchar -> JCTenum char_range 
    | Tbyte  -> JCTenum byte_range 

(*s class types *)

let get_class ci =
  {
    jc_struct_info_name = ci.class_info_name;
    jc_struct_info_parent = None;
    jc_struct_info_root = ci.class_info_name;
    jc_struct_info_fields = [];
  }

(*s array types *)

let num_zero = Num.Int 0
let num_minus_one = Num.Int (-1)

let array_struct_table = Hashtbl.create 17
      
let rec get_array_struct t = 
  try
    let st = Hashtbl.find array_struct_table t in
    Format.eprintf "got array structure %s@." st.jc_struct_info_name;
    st
  with Not_found -> assert false

and tr_type t =
  match t with
    | JTYbase t -> tr_base_type t	
    | JTYclass(non_null,ci) -> 
	let st = get_class ci in
	JCTpointer(st,num_zero,if non_null then num_zero else num_minus_one)
    | JTYarray t ->
	let st = get_array_struct t in
	JCTpointer(st,num_zero,num_minus_one)

let tr_type_option t =
  match t with
    | None -> JCTnative Tunit
    | Some t -> tr_type t

(*s structure fields *)

let fi_table = Hashtbl.create 97

let get_field fi =
  try
    Hashtbl.find fi_table fi.java_field_info_tag
  with
      Not_found -> 
	let ty = tr_type fi.java_field_info_type in
	let ci = get_class fi.java_field_info_class in
	let nfi =
	  { jc_field_info_name = fi.java_field_info_name;
	    jc_field_info_tag = fi.java_field_info_tag;
	    jc_field_info_type= ty;
	    jc_field_info_root= ci.jc_struct_info_root;
	    (*
	      jc_field_info_final_name = vi.java_field_info_name;
	      jc_var_info_assigned = vi.java_var_info_assigned;
	      jc_var_info_type = tr_type vi.java_var_info_type;
	      jc_var_info_tag = vi.java_var_info_tag;
	    *)
	  }
	in Hashtbl.add fi_table fi.java_field_info_tag nfi;
	nfi

(*s translation of structure types *)

let tr_class ci acc =
  JCstruct_def(ci.class_info_name,
	       List.map get_field ci.class_info_fields) :: acc

let array_types decls =
  Format.eprintf "array types:@.";
  Hashtbl.fold
    (fun t (s,f) acc ->
       let fi =
	 { jc_field_info_name = f;
	   jc_field_info_tag = 0 (* TODO *);
	   jc_field_info_type = tr_type t;
	   jc_field_info_root = s;
	 }
       in
       let st =
	 {
	   jc_struct_info_name = s;
	   jc_struct_info_parent = None;
	   jc_struct_info_root = s;
	   jc_struct_info_fields = [(f, fi)];
	 }
       in
       Format.eprintf "created array structure %s@." st.jc_struct_info_name;
       Hashtbl.add array_struct_table t st;
       JCstruct_def(st.jc_struct_info_name,
		    List.map snd st.jc_struct_info_fields) :: acc)
    Java_analysis.array_struct_table
    decls
      


(* local variables and parameters *)

let vi_table = Hashtbl.create 97

let get_var ?(formal=false) vi =
  try
    Hashtbl.find vi_table vi.java_var_info_tag
  with
      Not_found -> 
	let nvi =
	  { jc_var_info_name = vi.java_var_info_name;
	    jc_var_info_final_name = vi.java_var_info_name;
	    jc_var_info_assigned = vi.java_var_info_assigned;
	    jc_var_info_type = tr_type vi.java_var_info_type;
	    jc_var_info_tag = vi.java_var_info_tag;
	    jc_var_info_static = false; (* TODO *)
	    jc_var_info_formal = formal;
	  }
	in Hashtbl.add vi_table vi.java_var_info_tag nvi;
	nvi

(*s terms *)

let lit l =
  match l with
  | Integer s -> JCCinteger s
  | Float s -> JCCreal s
  | Bool b -> JCCboolean b
  | String s -> assert false (* TODO *)
  | Char s -> assert false (* TODO *)
  | Null  -> JCCnull


let lbin_op t op =
  match op with
    | Bgt -> Bgt_int
    | Bge -> Bge_int
    | Ble -> Ble_int
    | Blt -> Blt_int
    | Bne -> Bneq_int
    | Beq -> Beq_int
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand-> assert false (* TODO *)
    | Biff|Bimpl|Bor|Band -> assert false (* TODO *)
    | Bmod -> Bmod_int
    | Bdiv -> Bdiv_int
    | Bmul -> Bmul_int
    | Bsub -> Bsub_int
    | Badd -> Badd_int


let rec term t =
  let t' =
    match t.java_term_node with
      | JTlit l -> JCTTconst (lit l)
      | JTbin(e1,t,op,e2) -> JCTTbinary(term e1, lbin_op t op, term e2)
      | JTapp (_, _) -> assert false (* TODO *)
      | JTvar vi -> JCTTvar (get_var vi)
      | JTfield_access(t,fi) -> JCTTderef(term t,get_field fi)
      | JTarray_length(t) -> 
	  begin
	    match t.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct ty in
		  JCTToffset(Offset_max,term t,st)
	      | _ -> assert false
	  end
      | JTarray_access(t1,t2) -> 
	  begin
	    match t1.java_term_type with
	      | JTYarray ty ->
		  let st = get_array_struct ty in
		  let t1' = term t1 in
		  let shift = {
		      jc_tterm_loc = t.java_term_loc;
		      jc_tterm_type = t1'.jc_tterm_type;
		      jc_tterm_node = JCTTshift(t1', term t2)
		    }
		  in
		  JCTTderef(shift,snd (List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end
      | JTold t -> JCTTold(term t)

  in { jc_tterm_loc = t.java_term_loc ; 
       jc_tterm_type = tr_type t.java_term_type ;
       jc_tterm_node = t' }
  
let rec assertion a =
  let a' =
    match a.java_assertion_node with
      | JAtrue -> JCTAtrue
      | JAbin(e1,t,op,e2) -> JCTArelation(term e1, lbin_op t op, term e2)
      | JAapp (_, _)-> assert false (* TODO *)
      | JAquantifier (Forall, vi , a)-> 
	  let vi = get_var vi in
	  JCTAforall(vi,assertion a)
      | JAquantifier (q, vi , a)-> 	  assert false (* TODO *)
      | JAimpl (a1, a2)-> 
	  JCTAimplies(assertion a1,assertion a2)
      | JAor (_, _)-> assert false (* TODO *)
      | JAand (a1, a2)-> 
	  JCTAand [assertion a1 ; assertion a2]
       | JAfalse -> assert false (* TODO *)

  in { jc_tassertion_loc = a.java_assertion_loc ; jc_tassertion_node = a' }
    
let assertion_option a =
  match a with
    | None -> { jc_tassertion_loc = Loc.dummy_position; 
		jc_tassertion_node = JCTAtrue }
    | Some a -> assertion a

let behavior (id,a,assigns,e) =
  (snd id,
  { jc_tbehavior_assumes = Option_misc.map assertion a;
    jc_tbehavior_assigns = None ;
    jc_tbehavior_ensures = assertion e;
    jc_tbehavior_throws = None;
  })
    
let bin_op op =
  match op with
    | Badd -> Badd_int
    | Bmod -> Bmod_int
    | Bdiv -> Bdiv_int
    | Bmul -> Bmul_int
    | Bsub -> Bsub_int
    | Biff|Bor|Band|Bimpl  -> assert false (* TODO *) 
    | Bgt -> Bgt_int
    | Bne -> Bneq_int
    | Beq -> Beq_int
    | Bge -> Bge_int
    | Ble -> Ble_int
    | Blt -> Blt_int
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand -> assert false (* TODO *) 

let incr_op op =
  match op with
    | Preincr -> Prefix_inc
    | Predecr -> Prefix_dec
    | Postincr -> Postfix_inc
    | Postdecr -> Postfix_dec

let rec expr e =
  let e' =
    match e.java_expr_node with
      | JElit l -> JCTEconst (lit l)
      | JEincr_local_var(op,v) -> 
	  JCTEincr_local(incr_op op,get_var v)
      | JEun (_, _) -> assert false (* TODO *)
      | JEbin (e1, op, e2) -> 
	  let e1 = expr e1 and e2 = expr e2 in
	  JCTEbinary(e1,bin_op op,e2)	  
      | JEvar vi -> JCTEvar (get_var vi)
      | JEassign_local_var(vi,e) ->
	  JCTEassign_var(get_var vi,expr e)
      | JEassign_local_var_op(vi,op,e) ->
	  JCTEassign_var_op(get_var vi,bin_op op, expr e)
      | JEassign_field(e1,fi,e2) ->
	  JCTEassign_heap(expr e1,get_field fi,expr e2)
      | JEassign_field_op(e1,fi,op,e2) ->
	  JCTEassign_heap_op(expr e1,get_field fi,bin_op op,expr e2)
      | JEfield_access(e1,fi) -> 
	  JCTEderef(expr e1,get_field fi)
      | JEarray_length(e) -> 
	  begin
	    match e.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct ty in
		  JCTEoffset(Offset_max,expr e,st)
	      | _ -> assert false
	  end
      | JEarray_access(e1,e2) -> 
	  begin
	    match e1.java_expr_type with
	      | JTYarray ty ->
		  let st = get_array_struct ty in
		  let e1' = expr e1 in
		  let shift = {
		      jc_texpr_loc = e.java_expr_loc;
		      jc_texpr_type = e1'.jc_texpr_type;
		      jc_texpr_node = JCTEshift(e1', expr e2)
		    }
		  in
		  JCTEderef(shift,snd (List.hd st.jc_struct_info_fields))
	      | _ -> assert false
	  end

	  

  in { jc_texpr_loc = e.java_expr_loc ; 
       jc_texpr_type = tr_type e.java_expr_type ;
       jc_texpr_node = e' }

let initialiser e =
  match e with
    | JIexpr e -> expr e
    | _ -> assert false (* TODO *)

let rec statement s =
  let s' =
    match s.java_statement_node with
      | JSskip -> JCTSblock []
      | JSreturn e -> JCTSreturn (tr_type e.java_expr_type,expr e)
      | JSblock l -> JCTSblock (List.map statement l)	  
      | JSvar_decl (vi, init, s) -> 
	  JCTSdecl(get_var vi, Option_misc.map initialiser init, statement s)
      | JSif (e, s1, s2) ->
	  JCTSif (expr e, statement s1, statement s2)
      | JSwhile(e,inv,dec,s) ->
	  let la =
	    { jc_tloop_invariant = assertion inv;
	      jc_tloop_variant = term dec }
	  in
	  JCTSwhile(expr e, la, statement s)
      | JSfor_decl(decls,e,inv,dec,sl,body) ->
	  let la =
	    { jc_tloop_invariant = assertion inv;
	      jc_tloop_variant = term dec }
	  in
	  let decls = List.map
	    (fun (vi,init) -> (get_var vi, Option_misc.map initialiser init))
	    decls
	  in
	  let res =
	    List.fold_right
	      (fun (vi,init) acc -> 
		 { jc_tstatement_loc = acc.jc_tstatement_loc ;
		   jc_tstatement_node = JCTSdecl(vi,init, acc) })
	      decls
	      { jc_tstatement_loc = s.java_statement_loc ;
		jc_tstatement_node = 
		  JCTSfor(expr e, List.map expr sl, la, statement body) }
	  in res.jc_tstatement_node
      | JSexpr e -> JCTSexpr (expr e)
      | JSassert(id,e) -> JCTSassert(id,assertion e)


  in { jc_tstatement_loc = s.java_statement_loc ; jc_tstatement_node = s' }

and statements l = List.map statement l

let tr_method mi req behs b acc =
  match b with
    | None -> assert false
    | Some l ->	
	let params = List.map get_var mi.method_info_parameters in
	let params =
	  match mi.method_info_has_this with
	    | None -> params
	    | Some vi -> 
		(get_var vi) :: params
	in
	JCfun_def(tr_type_option mi.method_info_return_type,
		  mi.method_info_trans_name,
		  params,
		  { jc_tfun_requires = assertion_option req;
		    jc_tfun_behavior = List.map behavior behs},
		  Some (statements l))::acc
	  
(*s axioms *)

let tr_axiom (_,id) p acc =
  JCaxiom_def(id,assertion p)::acc

  

(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)

