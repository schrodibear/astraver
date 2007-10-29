
open Format
open Jc_env
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Pp

type jc_decl =
  | JCfun_def of jc_type * string * var_info list *
      fun_spec * tstatement list option
  | JCenum_type_def of string * Num.num * Num.num
  | JCstruct_def of string * string option * field_info list 
  | JCrec_struct_defs of jc_decl list
  | JCrec_fun_defs of jc_decl list
  | JCvar_def of jc_type * string * texpr option
  | JCaxiom_def of string * assertion
  | JClogic_fun_def of jc_type option * string 
      * var_info list * term_or_assertion      
  | JCexception_def of string * exception_info
  | JCglobinv_def of string * assertion
  | JClogic_const_def of jc_type * string * term option
  | JClogic_type_def of string

let const fmt c =
  match c with
    | JCCinteger s -> fprintf fmt "%s" s
    | JCCreal s -> fprintf fmt "%s" s
    | JCCboolean b -> fprintf fmt "%B" b
    | JCCnull -> fprintf fmt "null"
    | JCCvoid -> fprintf fmt "()"


let lbin_op op =
(*
  if op == Jc_pervasives.ge_int then ">=" else
  if op == Jc_pervasives.le_int then "<=" else
  if op == Jc_pervasives.gt_int then ">" else
  if op == Jc_pervasives.lt_int then "<" else
  if op == Jc_pervasives.eq then "==" else
  if op == Jc_pervasives.neq then "!=" else
  if op == Jc_pervasives.add_int then "+" else
  if op == Jc_pervasives.sub_int then "-" else
  if op == Jc_pervasives.mul_int then "*" else
  if op == Jc_pervasives.div_int then "/" else
  if op == Jc_pervasives.mod_int then "%" else
  if op == Jc_pervasives.shift then "+" else
*)
  raise Not_found

let bin_op = function
  | Blt_int | Blt_real -> "<"
  | Bgt_int | Bgt_real -> ">"
  | Ble_int | Ble_real -> "<="
  | Bge_int | Bge_real -> ">="
  | Beq_int | Beq_real | Beq_bool | Beq_pointer -> "=="
  | Bneq_int | Bneq_real | Bneq_bool | Bneq_pointer -> "!="
  | Badd_int | Badd_real -> "+"
  | Bsub_int | Bsub_real -> "-"
  | Bmul_int | Bmul_real -> "*"
  | Bdiv_int | Bdiv_real -> "/"
  | Bmod_int -> "%"
  | Bland -> "&&"
  | Blor -> "||"
  | Bimplies -> "==>"
  | Biff -> "<==>"
  | Bbw_and -> "&"
  | Bbw_or -> "|"
  | Bbw_xor -> "^"
  | Blogical_shift_right -> ">>"
  | Barith_shift_right -> ">>>"
  | Bshift_left -> "<<"

let unary_op = function
  | Uplus_int | Uplus_real -> "+"
  | Uminus_int | Uminus_real -> "-"
  | Unot -> "!"
  | Ubw_not -> "~"

let offset_kind fmt k =
  match k with
    | Offset_max -> fprintf fmt "ax"
    | Offset_min -> fprintf fmt "in"



let rec term fmt t =
  match t.jc_term_node with
    | JCTvar vi -> fprintf fmt "%s" vi.jc_var_info_name
    | JCTbinary(t1,op,t2) ->
	fprintf fmt "@[(%a %s %a)@]" term t1 (bin_op op) term t2
    | JCTunary(op,t1) ->
	fprintf fmt "@[(%s %a)@]" (unary_op op) term t1
    | JCTif (t1,t2,t3) -> 
	fprintf fmt "@[(%a ? %a : %a)@]" term t1 term t2 term t3
    | JCTcast (t, si) ->
	fprintf fmt "(%a :> %s)" term t si.jc_struct_info_name
    | JCTinstanceof (t, si) ->
	fprintf fmt "(%a <: %s)" term t si.jc_struct_info_name
    | JCToffset (k,t,_)->
	fprintf fmt "@[\\offset_m%a(%a)@]" offset_kind k term t
    | JCTold t -> fprintf fmt "@[\\old(%a)@]" term t
    | JCTapp (op, [t1]) ->
(*
	begin try 
	  ignore 
	    (Hashtbl.find Jc_typing.enum_conversion_logic_functions_table op);
	  (* conversion due to enumeration. Ignore it. *)
	  term fmt t1
	with Not_found ->
*)
	  fprintf fmt "%s(@[%a@])" op.jc_logic_info_name term t1
(*
	end
*)
    | JCTapp (op, ([t1;t2] as l)) ->
	begin try
	  let s = lbin_op op in
	  fprintf fmt "@[(%a %s %a)@]" term t1 s term t2
	with Not_found ->
	  fprintf fmt "@[%s(%a)@]" op.jc_logic_info_name
	    (print_list comma term) l 
	end
    | JCTapp (op, l) ->
	fprintf fmt "%s(@[%a@])" op.jc_logic_info_name
	  (print_list comma term) l 
    | JCTderef (t, fi)-> 
	fprintf fmt "@[%a.%s@]" term t fi.jc_field_info_name	
    | JCTshift (t1, t2) -> 
	fprintf fmt "@[(%a + %a)@]" term t1 term t2
    | JCTsub_pointer (t1, t2) -> 
	fprintf fmt "@[(%a - %a)@]" term t1 term t2
    | JCTconst c -> const fmt c
    | JCTrange (t1,t2) -> 
	fprintf fmt "@[[%a..%a]@]" (print_option term) t1 (print_option term) t2

let quantifier fmt = function
  | Forall -> fprintf fmt "forall"
  | Exists -> fprintf fmt "exists"

let rec assertion fmt a =
  if a.jc_assertion_label <> "" then
    fprintf fmt "@[(%s : %a)@]" 
      a.jc_assertion_label assertion {a with jc_assertion_label =""}
  else
  match a.jc_assertion_node with
    | JCAtrue -> fprintf fmt "true"
    | JCAif (_, _, _)-> assert false (* TODO *)
    | JCAbool_term t -> term fmt t
    | JCAinstanceof (t, st) ->
	fprintf fmt "(%a <: %s)" term t st.jc_struct_info_name
    | JCAold a -> fprintf fmt "\\old(%a)" assertion a
    | JCAquantifier (q,vi, a)-> 
	fprintf fmt "@[<v 3>(\\%a %a %s;@ %a)@]"
	  quantifier q
	  print_type vi.jc_var_info_type
	  vi.jc_var_info_name
	  assertion a
    | JCArelation (t1, op, t2) ->
	fprintf fmt "@[(%a %s %a)@]" term t1 (bin_op op) term t2
    | JCAapp (op, ([t1;t2] as l)) ->
	begin
	  try
	    let s = lbin_op op in
	    fprintf fmt "@[(%a %s %a)@]" term t1 s term t2
	  with Not_found ->
	    fprintf fmt "@[%s(%a)@]" op.jc_logic_info_name
	      (print_list comma term) l 
	end
    | JCAapp (op, l) ->
	 fprintf fmt "@[%s(%a)@]" op.jc_logic_info_name
	      (print_list comma term) l 
    | JCAnot a1 ->
	fprintf fmt "@[(!@ %a)@]" assertion a1
    | JCAiff (a1, a2)-> 
	fprintf fmt "@[(%a <==>@ %a)@]" assertion a1 assertion a2
    | JCAimplies (a1, a2)-> 
	fprintf fmt "@[(%a ==>@ %a)@]" assertion a1 assertion a2
    | JCAor [] -> assert false
    | JCAor (a::l) -> 
	fprintf fmt "@[(%a" assertion a;
	List.iter
	  (fun a -> fprintf fmt " ||@ %a" assertion a)
	  l;
	fprintf fmt ")@]"
    | JCAand [] -> assert false
    | JCAand (a::l) -> 
	fprintf fmt "@[(%a" assertion a;
	List.iter
	  (fun a -> fprintf fmt " &&@ %a" assertion a)
	  l;
	fprintf fmt ")@]"
    | JCAfalse -> fprintf fmt "false"
    | JCAmutable _ -> assert false (* TODO *)
    | JCAtagequality _ -> assert false (* TODO *)

let rec location_set fmt = function
  | JCLSvar vi-> 
      fprintf fmt "%s" vi.jc_var_info_name
  | JCLSderef (locset, fi) ->
      fprintf fmt "%a.%s" location_set locset fi.jc_field_info_name
  | JCLSrange (locset, t1, t2) ->
      fprintf fmt "(%a + [%a..%a])" location_set locset 
	(print_option term) t1 (print_option term) t2

let location fmt = function
  | JCLvar vi -> 
      fprintf fmt "%s" vi.jc_var_info_name
  | JCLderef (locset, fi) ->
      fprintf fmt "%a.%s" location_set locset fi.jc_field_info_name

let behavior fmt (id,b) =
  fprintf fmt "@\n@[<v 2>behavior %s:" id;
  Option_misc.iter
    (fun a -> fprintf fmt "@\nassumes %a;" assertion a) 
    b.jc_behavior_assumes;
  Option_misc.iter
  (fun a -> fprintf fmt "@\nthrows %s;" a.jc_exception_info_name) 
    b.jc_behavior_throws;    
  Option_misc.iter 
    (fun locs -> fprintf fmt "@\nassigns %a;" 
       (print_list_or_default "\\nothing" comma location) locs)
    b.jc_behavior_assigns;
  fprintf fmt "@\nensures %a;@]" assertion b.jc_behavior_ensures
  
let print_spec fmt s =
  fprintf fmt "@\n@[<v 2>  requires @[%a@];" assertion s.jc_fun_requires;
  List.iter (behavior fmt) s.jc_fun_behavior;
  fprintf fmt "@]"

let call_bin_op op =
(*
  if op == Jc_pervasives.shift_ then "+" else
*)
  raise Not_found

let rec expr fmt e =
  if e.jc_texpr_label <> "" then
    fprintf fmt "@[(%s : %a)@]" 
      e.jc_texpr_label expr {e with jc_texpr_label =""}
  else
  match e.jc_texpr_node with
    | JCTEvar vi -> 
	fprintf fmt "%s" vi.jc_var_info_name
    | JCTEbinary (e1, op, e2) ->
	fprintf fmt "@[(%a %s %a)@]" expr e1 (bin_op op) expr e2
    | JCTEunary(op,e1) ->
	fprintf fmt "@[(%s %a)@]" (unary_op op) expr e1
    | JCTEif (e1,e2,e3) -> 
	fprintf fmt "@[(%a ? %a : %a)@]" expr e1 expr e2 expr e3
    | JCTEincr_heap (op, e, fi) -> 
	begin
	  match op with
	    | Prefix_inc ->
		fprintf fmt "++(%a.%s)" expr e fi.jc_field_info_name
	    | Prefix_dec ->
		fprintf fmt "--(%a.%s)" expr e fi.jc_field_info_name
	    | Postfix_inc ->
		fprintf fmt "(%a.%s)++" expr e fi.jc_field_info_name
	    | Postfix_dec ->
		fprintf fmt "(%a.%s)--" expr e fi.jc_field_info_name
	end
    | JCTEincr_local (op, v) -> 
	begin
	  match op with
	    | Prefix_inc ->
		fprintf fmt "++%s" v.jc_var_info_name
	    | Prefix_dec ->
		fprintf fmt "--%s" v.jc_var_info_name
	    | Postfix_inc ->
		fprintf fmt "%s++" v.jc_var_info_name
	    | Postfix_dec ->
		fprintf fmt "%s--" v.jc_var_info_name
	end
    | JCTEassign_heap (e1, fi, e2) -> 
	fprintf fmt "%a.%s = %a" expr e1 fi.jc_field_info_name expr e2
    | JCTEassign_heap_op (e1, fi, op, e2) -> 
	fprintf fmt "%a.%s %s= %a" expr e1 fi.jc_field_info_name 
	  (bin_op op) expr e2
    | JCTEassign_var (v, e) -> 
	fprintf fmt "(%s = %a)" v.jc_var_info_name expr e
    | JCTEassign_var_op (v, op, e) -> 
	fprintf fmt "%s %s= %a" v.jc_var_info_name (bin_op op) expr e
    | JCTEcast (e, si) ->
	fprintf fmt "(%a :> %s)" expr e si.jc_struct_info_name
    | JCTErange_cast (ri, e) ->
	fprintf fmt "(%a :> %s)" expr e ri.jc_enum_info_name
    | JCTEalloc (e, si) ->
	fprintf fmt "(new %s[%a])" si.jc_struct_info_name expr e 
    | JCTEfree (e) ->
	fprintf fmt "(free(%a))" expr e 
    | JCTEoffset(k,e, _) ->
	fprintf fmt "\\offset_m%a(%a)" offset_kind k expr e 
    | JCTEinstanceof (e, si) ->
	fprintf fmt "(%a <: %s)" expr e si.jc_struct_info_name
    | JCTEcall (op, ([t1;t2] as l)) ->
	begin
	  try
	    let s = call_bin_op op in
	    fprintf fmt "@[(%a %s %a)@]" expr t1 s expr t2
	  with Not_found ->
	    fprintf fmt "@[%s(%a)@]" op.jc_fun_info_name
	      (print_list comma expr) l 
	end
    | JCTEcall (op, l) -> 
	fprintf fmt "@[%s(%a)@]" op.jc_fun_info_name
	  (print_list comma expr) l 
    | JCTEderef (e, fi) -> 
	fprintf fmt "%a.%s" expr e fi.jc_field_info_name 
    | JCTEshift (e1, e2) -> 
	fprintf fmt "@[(%a + %a)@]" expr e1 expr e2
    | JCTEsub_pointer (e1, e2) -> 
	fprintf fmt "@[(%a - %a)@]" expr e1 expr e2
    | JCTEconst c -> const fmt c

let rec statement fmt s =
  match s.jc_tstatement_node with
    | JCTSreturn (t,e) ->
	fprintf fmt "@\nreturn %a;" expr e
    | JCTSreturn_void ->
	fprintf fmt "@\nreturn;"
    | JCTSunpack (_, _, _) -> assert false (* TODO *) 
    | JCTSpack (_, _, _) -> assert false (* TODO *) 
    | JCTSthrow (ei, eo) ->
	fprintf fmt "@\nthrow %s %a;" 
	  ei.jc_exception_info_name 
	  (print_option_or_default "()" expr) eo
    | JCTStry (s, hl, fs) ->
	fprintf fmt 
	  "@\n@[<v 2>try %a@]%a@\n@[<v 2>finally%a@]"
	  statement s 
	  (print_list nothing handler) hl
	  statement fs
    | JCTSgoto lab -> 
	fprintf fmt "@\ngoto %s;" lab
    | JCTSlabel (lab, s) -> 
	fprintf fmt "@\n%s:%a" lab statement s
    | JCTScontinue lab -> 
	fprintf fmt "@\ncontinue %s;" lab
    | JCTSbreak lab -> 
	fprintf fmt "@\nbreak %s;" lab
    | JCTSwhile (e, la, s)-> 
	fprintf fmt "@\n@[while (%a)@\ninvariant %a;%a%a@]"
	  expr e assertion la.jc_loop_invariant 
	  (print_option (fun fmt t -> fprintf fmt "@\nvariant %a;" term t))
	  la.jc_loop_variant
	  block [s]
    | JCTSfor (cond, updates, loop_annot, body)-> 
	fprintf fmt "@\n@[for ( ; %a ; %a)@\ninvariant %a;%a%a@]"
	  expr cond (print_list comma expr) updates
	  assertion loop_annot.jc_loop_invariant 
	  (print_option (fun fmt t -> fprintf fmt "@\nvariant %a;" term t))
	  loop_annot.jc_loop_variant
	  block [body]
    | JCTSif (e, s1, s2) | JCTScut_if (_, e, s1, s2) ->
	fprintf fmt "@\n@[<v 2>if (%a) %a@]@\n@[<v 2>else %a@]"
	  expr e statement s1 statement s2
    | JCTSdecl (vi, None, s)-> 
	fprintf fmt "{@\n%a %s;%a}" print_type vi.jc_var_info_type
	  vi.jc_var_info_name statement s
    | JCTSdecl (vi, Some e, s)-> 
	fprintf fmt "{@\n%a %s = %a;%a}" 
	  print_type vi.jc_var_info_type 
	  vi.jc_var_info_name expr e statement s
    | JCTSassert(None,a)-> 
	fprintf fmt "@\nassert %a;" assertion a
    | JCTSassert(Some n,a)-> 
	fprintf fmt "@\nassert %s: %a;" n assertion a
    | JCTSexpr e -> fprintf fmt "@\n%a;" expr e
    | JCTSblock l -> block fmt l
    | JCTSswitch (e, csl) ->
	fprintf fmt "@\n@[<v 2>switch (%a) {%a@]@\n}"
	  expr e (print_list nothing case) csl
	
and case fmt (c,sl) =
  let onecase fmt = function
    | Some c ->
	fprintf fmt "@\ncase %a:" expr c
    | None ->
	fprintf fmt "@\ndefault:"
  in
  fprintf fmt "%a%a" (print_list nothing onecase) c block sl

and handler fmt (ei,vio,s) =
  fprintf fmt "@\n@[<v 2>catch %s %a %a@]"
    ei.jc_exception_info_name 
    (print_option_or_default "__dummy"
      (fun fmt vi -> fprintf fmt "%s" vi.jc_var_info_name)) vio
    statement s

and statements fmt l = List.iter (statement fmt) l

and block fmt b =
  fprintf fmt "@\n@[<v 0>{@[<v 2>  ";
  statements fmt b;
  fprintf fmt "@]@\n}@]"


let param fmt vi =
  fprintf fmt "%a %s" print_type vi.jc_var_info_type vi.jc_var_info_name

let field fmt fi =
  fprintf fmt "@\n%a %s;" 
    print_type fi.jc_field_info_type fi.jc_field_info_name

let term_or_assertion fmt = function
  | JCAssertion a -> 
      fprintf fmt "=@\n%a" assertion a
  | JCTerm t ->
      fprintf fmt "=@\n%a" term t
  | JCReads [] -> 
      fprintf fmt "reads \\nothing;"
  | JCReads locs -> 
      fprintf fmt "reads %a;" (print_list comma location) locs

let print_super fmt = function
  | None -> ()
  | Some id -> fprintf fmt "%s with " id

let rec print_decl fmt d =
  match d with
    | JCfun_def(ty,id,params,spec,body) ->
	fprintf fmt "@\n@[%a %s(@[%a@])%a%a@]@." print_type ty id
	  (print_list comma param) params 
	  print_spec spec 
	  (print_option_or_default "\n;" block) body
    | JCenum_type_def(id,min,max) ->
	fprintf fmt "@\n@[type %s = %s..%s@]@."
	  id (Num.string_of_num min) (Num.string_of_num max)
    | JCstruct_def(id,extends,fields) ->
	fprintf fmt "@\n@[<v 2>type %s = %a{%a@]@\n}@."
	  id print_super extends (print_list space field) fields
    | JCrec_struct_defs dlist | JCrec_fun_defs dlist ->
	print_list (fun fmt () -> fprintf fmt "@\nand") print_decl fmt dlist
    | JCvar_def(ty,id,init) ->
	fprintf fmt "@\n@[%a %s%a;@]@." print_type ty id
	  (print_option (fun fmt e -> fprintf fmt " = %a" expr e)) init
    | JCaxiom_def(id,a) ->
	fprintf fmt "@\n@[axiom %s : %a@]@." id assertion a
    | JCglobinv_def(id,a) ->
	fprintf fmt "@\n@[invariant %s : %a@]@." id assertion a
    | JCexception_def(id,ei) ->
	fprintf fmt "@\n@[exception %s of %a@]@." id
	  (print_option_or_default "unit" print_type)
	  ei.jc_exception_info_type
    | JClogic_const_def(ty,id,None) ->
	fprintf fmt "@\n@[logic %a %s@]@." print_type ty id
    | JClogic_const_def(ty,id,Some t) ->
	fprintf fmt "@\n@[logic %a %s = %a@]@." print_type ty id
	  term t
    | JClogic_fun_def(ty,id,[],JCReads l) ->
	assert (l=[]);
	fprintf fmt "@\n@[logic %a %s@]@." 
	  (print_option print_type) ty id
    | JClogic_fun_def(ty,id,[],JCTerm t) ->
	fprintf fmt "@\n@[logic %a %s = %a@]@." 
	  (print_option print_type) ty id term t
    | JClogic_fun_def(ty,id,params,body) ->
	fprintf fmt "@\n@[logic %a %s(@[%a@]) %a@]@." 
	  (print_option print_type) ty 
	  id (print_list comma param) params
	  term_or_assertion body 
    | JClogic_type_def id ->
	fprintf fmt "@\n@[logic type %s@]@." id
   
let rec print_decls fmt d =
  match d with
    | [] -> ()
    | d::r -> print_decl fmt d; print_decls fmt r

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte bin/krakatoa.byte"
End: 
*)
