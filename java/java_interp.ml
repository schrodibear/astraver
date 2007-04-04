

open Jc_output
open Jc_env
open Jc_ast
open Java_env
open Java_tast

let int_range =
  {
    jc_range_info_name = "int";
    jc_range_info_min = Num.num_of_string "-2147483648";
    jc_range_info_max = Num.num_of_string "2147483647";
  }

let tr_base_type t =
  match t with
    | Tboolean -> JCTnative Jc_env.Tboolean
    | Tinteger -> JCTnative Jc_env.Tinteger
    | Tint -> JCTrange int_range
    | _ -> assert false (* TODO *)


let tr_type t =
  match t with
    | JTYbase t -> tr_base_type t	
    | JTYarray _ -> assert false

let tr_type_option t =
  match t with
    | None -> JCTnative Tunit
    | Some t -> tr_type t

let tr_param vi =
  (tr_type vi.java_var_info_type,vi.java_var_info_name)

let lit l =
  match l with
  | Integer s -> JCCinteger s
  | Float s -> JCCreal s
  | Bool b -> JCCboolean b
  | String s -> assert false (* TODO *)
  | Char s -> assert false (* TODO *)
  | Null  -> JCCnull

let rec assertion a =
  let a' =
    match a.java_assertion_node with
      | JAtrue -> JCTAtrue
      | _ -> assert false (* TODO *)
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
  
let rec expr e =
  let e' =
    match e.java_expr_node with
      | JElit l -> JCTEconst (lit l)
      | JEincr (_, _) -> assert false (* TODO *) 
      | JEun (_, _) -> assert false (* TODO *)
      | JEbin (e1, op, e2) -> 
	  let _e1 = expr e1 and _e2 = expr e2 in
	  assert false
	  
      | JEvar vi -> JCTEvar (get_var vi)

  in { jc_texpr_loc = e.java_expr_loc ; 
       jc_texpr_type = tr_type e.java_expr_type ;
       jc_texpr_node = e' }

let rec statement s =
  let s' =
    match s.java_statement_node with
      | JSskip -> assert false (* TODO *)
      | JSreturn e -> JCTSreturn (expr e)
      | JSblock _ -> assert false (* TODO *)
      | JSvar_decl (_, _, _) -> assert false (* TODO *)
      | JSif (e, s1, s2) ->
	  JCTSif (expr e, statement s1, statement s2)
  in { jc_tstatement_loc = s.java_statement_loc ; jc_tstatement_node = s' }

and statements l = List.map statement l

let tr_method mi req behs b acc =
  match b with
    | None -> assert false
    | Some l ->	
	JCfun_def(tr_type_option mi.method_info_return_type,
		  mi.method_info_trans_name,
		  List.map tr_param mi.method_info_parameters,
		  { jc_tfun_requires = assertion_option req;
		    jc_tfun_behavior = List.map behavior behs},
		  statements l)::acc
	  
  



(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)

