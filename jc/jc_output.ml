

open Format
open Jc_env
open Jc_fenv
open Jc_ast
open Pp

type jc_decl =
  | JCfun_def of jc_type * string * var_info list *
      tfun_spec * tstatement list
  | JCenum_type_def of string * Num.num * Num.num
  | JCstruct_def of string * field_info list 
  | JCrec_struct_defs of jc_decl list
  | JCvar_def of jc_type * string * texpr
  | JCaxiom_def of string * tassertion
      
let string_of_native t =
  match t with
    | Tunit -> "unit"
    | Tinteger -> "integer"
    | Treal -> "real"
    | Tboolean -> "boolean"



let print_type fmt t =
  match t with
    | JCTnative n -> fprintf fmt "%s" (string_of_native n)
    | JCTlogic s -> fprintf fmt "%s" s
    | JCTenum ri -> fprintf fmt "%s" ri.jc_enum_info_name
    | JCTpointer (s,a,b) -> 
	if Num.gt_num a b then
	  fprintf fmt "%s[..]" s.jc_struct_info_name
	else
	  if Num.eq_num a b then
	  fprintf fmt "%s[%s]" s.jc_struct_info_name
	    (Num.string_of_num a)
	else
	  fprintf fmt "%s[%s..%s]" s.jc_struct_info_name
	  (Num.string_of_num a) (Num.string_of_num b)
    | JCTnull -> assert false

let const fmt c =
  match c with
    | JCCinteger s -> fprintf fmt "%s" s
    | JCCreal s -> fprintf fmt "%s" s
    | JCCboolean b -> fprintf fmt "%B" b
    | JCCnull -> fprintf fmt "null"
    | JCCvoid -> fprintf fmt "()"

let lbin_op op =
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
  raise Not_found

let rec term fmt t =
  match t.jc_tterm_node with
    | JCTTvar vi -> fprintf fmt "%s" vi.jc_var_info_name
    | JCTTif (_, _, _)-> assert false (* TODO *)
    | JCTTcast (_, _)-> assert false (* TODO *)
    | JCTTinstanceof (_, _)-> assert false (* TODO *)
    | JCTToffset_min (t, _)->
	fprintf fmt "@[\\offset_min(%a)@]" term t
    | JCTToffset_max (t, _)->
	fprintf fmt "@[\\offset_max(%a)@]" term t
    | JCTTold t -> fprintf fmt "@[\\old(%a)@]" term t
    | JCTTapp (op, ([t1;t2] as l)) ->
	begin
	  try
	    let s = lbin_op op in
	    fprintf fmt "@[(%a %s %a)@]" term t1 s term t2
	  with Not_found ->
	    fprintf fmt "@[%s(%a)@]" op.jc_logic_info_name
	      (print_list comma term) l 
	end
    | JCTTapp (op, l) ->
	fprintf fmt "%s(@[%a@])" op.jc_logic_info_name
	  (print_list comma term) l 
    | JCTTderef (t, fi)-> 
	fprintf fmt "@[%a.%s@]" term t fi.jc_field_info_name	
    | JCTTshift (_, _)-> assert false (* TODO *)
    | JCTTconst c -> const fmt c
    | JCTTrange (t1,t2) -> 
	fprintf fmt "@[%a..%a@]" term t1 term t2

let rec assertion fmt a =
  match a.jc_tassertion_node with
    | JCTAtrue -> fprintf fmt "true"
    | JCTAif (_, _, _)-> assert false (* TODO *)
    | JCTAbool_term _-> assert false (* TODO *)
    | JCTAinstanceof (_, _)-> assert false (* TODO *)
    | JCTAold _-> assert false (* TODO *)
    | JCTAforall (vi, a)-> 
	fprintf fmt "@[(\\forall %a %s;@ %a)@]"
	  print_type vi.jc_var_info_type
	  vi.jc_var_info_name
	  assertion a
    | JCTAapp (op, ([t1;t2] as l)) ->
	begin
	  try
	    let s = lbin_op op in
	    fprintf fmt "@[(%a %s %a)@]" term t1 s term t2
	  with Not_found ->
	    fprintf fmt "@[%s(%a)@]" op.jc_logic_info_name
	      (print_list comma term) l 
	end
    | JCTAapp (op, l) ->
	 fprintf fmt "@[%s(%a)@]" op.jc_logic_info_name
	      (print_list comma term) l 

    | JCTAnot _-> assert false (* TODO *)
    | JCTAiff (_, _)-> assert false (* TODO *)
    | JCTAimplies (a1, a2)-> 
	fprintf fmt "@[(%a =>@ %a)@]" assertion a1 assertion a2
    | JCTAor _-> assert false (* TODO *)
    | JCTAand [] -> assert false
    | JCTAand (a::l) -> 
	fprintf fmt "@[(%a" assertion a;
	List.iter
	  (fun a -> fprintf fmt " &&@ %a" assertion a)
	  l;
	fprintf fmt ")@]"
    | JCTAfalse -> assert false (* TODO *)


let behavior fmt (id,b) =
  fprintf fmt "@[<v 2>behavior %s:@\n" id;
  Option_misc.iter
    (fun a -> fprintf fmt "assumes %a;@\n" assertion a) 
    b.jc_tbehavior_assumes;
  fprintf fmt "ensures %a;@]@\n" assertion b.jc_tbehavior_ensures
  
let print_spec fmt s =
  fprintf fmt "@[<v 2>  requires @[%a@];@ " assertion s.jc_tfun_requires;
  List.iter (behavior fmt) s.jc_tfun_behavior;
  fprintf fmt "@]"

let call_bin_op op =
  if op == Jc_pervasives.shift_ then "+" else
  raise Not_found

let bin_op = function
  | Blt_int | Blt_real -> "<"
  | Bgt_int | Bgt_real -> ">"
  | Ble_int | Ble_real -> "<="
  | Bge_int | Bge_real -> ">="
  | Beq_int | Beq_real | Beq_pointer -> "=="
  | Bneq_int | Bneq_real | Bneq_pointer -> "!="
  | Badd_int | Badd_real -> "+"
  | Bsub_int | Bsub_real -> "-"
  | Bmul_int | Bmul_real -> "*"
  | Bdiv_int | Bdiv_real -> "/"
  | Bmod_int -> "%"
  | Bland -> "&&"
  | Blor -> "||"
  | Bimplies -> "=>"
  | Biff -> "<=>"

let unary_op = function
  | Uplus_int | Uplus_real -> "+"
  | Uminus_int | Uminus_real -> "-"
  | Unot -> "!"

let rec expr fmt e =
  match e.jc_texpr_node with
    | JCTEvar vi -> 
	fprintf fmt "%s" vi.jc_var_info_name
    | JCTEbinary(e1,op,e2) ->
	fprintf fmt "@[(%a %s %a)@]" expr e1 (bin_op op) expr e2
    | JCTEunary(op,e1) ->
	fprintf fmt "@[(%s %a)@]" (unary_op op) expr e1
    | JCTEif (_, _, _) -> assert false (* TODO *)
    | JCTEincr_heap (_, _, _) -> assert false (* TODO *)
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
(*
    | JCTEassign_op_heap (_, _, _, _, _) -> assert false (* TODO *)
    | JCTEassign_op_local (_, _, _, _) -> assert false (* TODO *)
*)
    | JCTElet(v,e1,e2) -> 
	fprintf fmt "let %s = %a@ in %a" v.jc_var_info_name expr e1 expr e2
    | JCTEassign_heap (e1, fi, e2) -> 
	fprintf fmt "%a.%s = %a" expr e1 fi.jc_field_info_name expr e2
    | JCTEassign_local (v, e) -> 
	fprintf fmt "%s = %a" v.jc_var_info_name expr e
    | JCTEassign_local_op (v, op, e) -> 
	fprintf fmt "%s %s= %a" (bin_op op) v.jc_var_info_name expr e
    | JCTEcast (_, _) -> assert false (* TODO *)
    | JCTEinstanceof (_, _) -> assert false (* TODO *)
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
    | JCTEshift (_, _) -> assert false (* TODO *)
    | JCTEconst c -> const fmt c

let rec statement fmt s =
  match s.jc_tstatement_node with
    | JCTSreturn e ->
	fprintf fmt "return %a;@\n" expr e
    | JCTSunpack (_, _) -> assert false (* TODO *) 
    | JCTSpack (_, _) -> assert false (* TODO *) 
    | JCTSthrow (_, _) -> assert false (* TODO *) 
    | JCTStry (_, _, _) -> assert false (* TODO *) 
    | JCTSgoto _-> assert false (* TODO *) 
    | JCTSlabel _-> assert false (* TODO *) 
    | JCTScontinue _-> assert false (* TODO *) 
    | JCTSbreak _-> assert false (* TODO *) 
    | JCTSwhile (e, la, s)-> 
	fprintf fmt "@[while (%a)@\ninvariant %a;@\nvariant %a;@\n%a@]@\n"
	  expr e assertion la.jc_tloop_invariant term la.jc_tloop_variant
	  statement s
    | JCTSif (e, s1, s2)->
	fprintf fmt "@[if (%a)@ %a@ else@ %a@]@\n"
	  expr e statement s1 statement s2
    | JCTSdecl (vi, None, s)-> 
	fprintf fmt "%a %s;@\n%a" print_type vi.jc_var_info_type
	  vi.jc_var_info_name statement s
    | JCTSdecl (vi, Some e, s)-> 
	fprintf fmt "%a %s = %a;@\n%a" 
	  print_type vi.jc_var_info_type 
	  vi.jc_var_info_name expr e statement s
    | JCTSassert _-> assert false (* TODO *) 
    | JCTSexpr e -> fprintf fmt "%a;@\n" expr e
    | JCTSblock l -> block fmt l
    | JCTSswitch (e, csl) ->
	fprintf fmt "@[switch (%a) {@\n@[<v 2>  %a@]@\n}@]"
	  expr e (print_list newline case) csl
	
and case fmt (c,sl) =
  fprintf fmt "@[%a    %a@]"
    (fun fmt c -> match c with
       | Case c ->
	   fprintf fmt "case %a:@\n" const c
       | Default ->
	   fprintf fmt "default:@\n") c
    block sl

and block fmt b =
  fprintf fmt "@[<v 0>{@ @[<v 2>  ";
  List.iter (statement fmt) b;
  fprintf fmt "@]@ }@]"


let param fmt vi =
  fprintf fmt "%a %s" print_type vi.jc_var_info_type vi.jc_var_info_name

let field fmt fi =
  fprintf fmt "%a %s;@\n" 
    print_type fi.jc_field_info_type fi.jc_field_info_name

let rec print_decl fmt d =
  match d with
    | JCfun_def(ty,id,params,spec,body) ->
	fprintf fmt "@[%a %s(@[%a@])@\n%a@\n%a@]@\n@." print_type ty id
	  (print_list comma param) params 
	  print_spec spec block body 
    | JCenum_type_def(id,min,max) ->
	fprintf fmt "@[type %s = %s..%s@]@\n@."
	  id (Num.string_of_num min) (Num.string_of_num max)
    | JCstruct_def(id,fields) ->
	fprintf fmt "@[<v 2>type %s = {@\n%a}@]@\n@."
	  id (print_list space field) fields
    | JCrec_struct_defs dlist ->
	print_list (fun fmt () -> fprintf fmt " and ") print_decl fmt dlist
    | JCvar_def(ty,id,init) ->
	fprintf fmt "@[%a %s = %a@]@\n@." print_type ty id expr init
    | JCaxiom_def(id,a) ->
	fprintf fmt "@[axiom %s : %a@]@\n@." id assertion a
	
   
let rec print_decls fmt d =
  match d with
    | [] -> ()
    | d::r -> print_decl fmt d; print_decls fmt r

(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
