

open Jc_output
open Jc_env
open Jc_ast
open Java_env
open Java_ast
open Java_tast

let int16_range =
  {
    jc_range_info_name = "int16";
    jc_range_info_min = Num.num_of_string "-32768";
    jc_range_info_max = Num.num_of_string "32767";
  }

let int32_range =
  {
    jc_range_info_name = "int32";
    jc_range_info_min = Num.num_of_string "-2147483648";
    jc_range_info_max = Num.num_of_string "2147483647";
  }

let range_types acc =
  List.fold_left
    (fun acc ri ->
       JCrange_type_def(ri.jc_range_info_name,
			ri.jc_range_info_min,
			ri.jc_range_info_max)::acc) 
    acc [ int16_range ; int32_range ]

let tr_base_type t =
  match t with
    | Tboolean -> JCTnative Jc_env.Tboolean
    | Tinteger -> JCTnative Jc_env.Tinteger
    | Tshort -> JCTrange int16_range 
    | Tint -> JCTrange int32_range 
    | _ -> assert false (* TODO *)


let tr_type t =
  match t with
    | JTYbase t -> tr_base_type t	
    | JTYclass _ -> assert false (* TODO *)
    | JTYarray _ -> assert false (* TODO *)

let tr_type_option t =
  match t with
    | None -> JCTnative Tunit
    | Some t -> tr_type t

let vi_table = Hashtbl.create 97

let get_var vi =
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
	  }
	in Hashtbl.add vi_table vi.java_var_info_tag nvi;
	nvi
  
(*
let tr_param vi =
  (tr_type vi.java_var_info_type,vi.java_var_info_name)
*)

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
    | Bgt -> Jc_pervasives.gt_int
    | Bge -> Jc_pervasives.ge_int
    | Ble -> Jc_pervasives.le_int
    | Blt -> Jc_pervasives.lt_int
    | Bne -> Jc_pervasives.neq
    | Beq -> Jc_pervasives.eq
    | Basr|Blsr|Blsl|Bbwxor|Bbwor|Bbwand-> assert false (* TODO *)
    |Biff|Bimpl|Bor|Band -> assert false (* TODO *)
    | Bmod -> Jc_pervasives.mod_int
    | Bdiv -> Jc_pervasives.div_int
    | Bmul -> Jc_pervasives.mul_int
    | Bsub -> Jc_pervasives.sub_int
    | Badd -> Jc_pervasives.add_int


let rec term t =
  let t' =
    match t.java_term_node with
      | JTlit l -> JCTTconst (lit l)
      | JTbin(e1,t,op,e2) -> JCTTapp(lbin_op t op,[term e1; term e2])
      | JTapp (_, _) -> assert false (* TODO *)
      | JTvar vi -> JCTTvar (get_var vi)
      | JTfield_access _ -> assert false (* TODO *)

  in { jc_tterm_loc = t.java_term_loc ; jc_tterm_node = t' }
  
let rec assertion a =
  let a' =
    match a.java_assertion_node with
      | JAtrue -> JCTAtrue
      | JAbin(e1,t,op,e2) -> JCTAapp(lbin_op t op,[term e1; term e2])
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
    | Badd -> Jc_pervasives.add_int_
    | Bmod -> Jc_pervasives.mod_int_
    | Bdiv -> Jc_pervasives.div_int_
    | Bmul -> Jc_pervasives.mul_int_
    | Bsub -> Jc_pervasives.sub_int_
    | Biff|Bor|Band|Bimpl  -> assert false (* TODO *) 
    | Bgt -> Jc_pervasives.gt_int_
    | Bne -> Jc_pervasives.neq_int_
    | Beq -> Jc_pervasives.eq_int_
    | Bge -> Jc_pervasives.ge_int_
    | Ble -> Jc_pervasives.le_int_
    | Blt -> Jc_pervasives.lt_int_
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
	  JCTEcall(bin_op op,[e1;e2])
	  
      | JEvar vi -> JCTEvar (get_var vi)
      | JEassign_local_var(vi,e) ->
	  JCTEassign_local(get_var vi,expr e)
      | JEfield_access _ -> assert false (* TODO *)

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
      | JSskip -> assert false (* TODO *)
      | JSreturn e -> JCTSreturn (expr e)
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
      | JSexpr e -> JCTSexpr (expr e)

  in { jc_tstatement_loc = s.java_statement_loc ; jc_tstatement_node = s' }

and statements l = List.map statement l

let tr_method mi req behs b acc =
  match b with
    | None -> assert false
    | Some l ->	
	JCfun_def(tr_type_option mi.method_info_return_type,
		  mi.method_info_trans_name,
		  List.map get_var mi.method_info_parameters,
		  { jc_tfun_requires = assertion_option req;
		    jc_tfun_behavior = List.map behavior behs},
		  statements l)::acc
	  
  



(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)

