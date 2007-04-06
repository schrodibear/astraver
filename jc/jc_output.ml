

open Format
open Jc_env
open Jc_fenv
open Jc_ast
open Pp

type jc_decl =
  | JCfun_def of jc_type * string * var_info list *
      tfun_spec * tstatement list
  | JCrange_type_def of string * Num.num * Num.num

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
    | JCTrange ri -> fprintf fmt "%s" ri.jc_range_info_name
    | JCTpointer (s,_,_) -> fprintf fmt "%s" s.jc_struct_info_name

let const fmt c =
  match c with
    | JCCinteger s -> fprintf fmt "%s" s
    | JCCreal _
    | JCCboolean _
    | JCCnull
    | JCCvoid -> assert false (* TODO *)

let lbin_op op =
  if op == Jc_pervasives.ge_int then ">=" else
  if op == Jc_pervasives.le_int then "<=" else
  if op == Jc_pervasives.gt_int then ">" else
  if op == Jc_pervasives.lt_int then "<" else
  if op == Jc_pervasives.add_int then "+" else
  if op == Jc_pervasives.sub_int then "-" else
  if op == Jc_pervasives.mul_int then "*" else
  if op == Jc_pervasives.div_int then "/" else
  if op == Jc_pervasives.mod_int then "%" else
  raise Not_found

let rec term fmt t =
  match t.jc_tterm_node with
    | JCTTvar vi -> fprintf fmt "%s" vi.jc_var_info_name
    | JCTTif (_, _, _)-> assert false (* TODO *)
    | JCTTcast (_, _)-> assert false (* TODO *)
    | JCTTinstanceof (_, _)-> assert false (* TODO *)
    | JCTToffset_min (_, _)-> assert false (* TODO *)
    | JCTToffset_max (_, _)-> assert false (* TODO *)
    | JCTTold _-> assert false (* TODO *)
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
    | JCTTderef (_, _)-> assert false (* TODO *)
    | JCTTshift (_, _)-> assert false (* TODO *)
    | JCTTconst c -> const fmt c

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

let bin_op op =
  if op == Jc_pervasives.gt_int_ then ">"
  else raise Not_found

let rec expr fmt e =
  match e.jc_texpr_node with
    | JCTEvar vi -> 
	fprintf fmt "%s" vi.jc_var_info_name
    | JCTEif (_, _, _) -> assert false (* TODO *)
    | JCTEincr_heap (_, _, _) -> assert false (* TODO *)
    | JCTEincr_local (_, _) -> assert false (* TODO *)
    | JCTEassign_op_heap (_, _, _, _) -> assert false (* TODO *)
    | JCTEassign_op_local (_, _, _) -> assert false (* TODO *)
    | JCTEassign_heap (_, _, _) -> assert false (* TODO *)
    | JCTEassign_local (_, _) -> assert false (* TODO *)
    | JCTEcast (_, _) -> assert false (* TODO *)
    | JCTEinstanceof (_, _) -> assert false (* TODO *)
    | JCTEcall (op, ([t1;t2] as l)) ->
	begin
	  try
	    let s = bin_op op in
	    fprintf fmt "@[(%a %s %a)@]" expr t1 s expr t2
	  with Not_found ->
	    fprintf fmt "@[%s(%a)@]" op.jc_fun_info_name
	      (print_list comma expr) l 
	end
    | JCTEcall (op, l) -> 
	fprintf fmt "@[%s(%a)@]" op.jc_fun_info_name
	  (print_list comma expr) l 
    | JCTEderef (_, _) -> assert false (* TODO *)
    | JCTEshift (_, _) -> assert false (* TODO *)
    | JCTEconst _ -> assert false (* TODO *)

let rec statement fmt s =
  match s.jc_tstatement_node with
    | JCTSreturn e ->
	fprintf fmt "return %a;" expr e
    | JCTSunpack (_, _) -> assert false (* TODO *) 
    | JCTSpack (_, _) -> assert false (* TODO *) 
    | JCTSthrow (_, _) -> assert false (* TODO *) 
    | JCTStry (_, _, _) -> assert false (* TODO *) 
    | JCTSgoto _-> assert false (* TODO *) 
    | JCTScontinue _-> assert false (* TODO *) 
    | JCTSbreak _-> assert false (* TODO *) 
    | JCTSwhile (_, _, _)-> assert false (* TODO *) 
    | JCTSif (e, s1, s2)->
	fprintf fmt "@[if (%a)@ %a@ else@ %a@]"
	  expr e statement s1 statement s2
	
    | JCTSdecl (_, _, _)-> assert false (* TODO *) 
    | JCTSassert _-> assert false (* TODO *) 
    | JCTSexpr _ -> assert false (* TODO *) 
    | JCTSblock _ -> assert false (* TODO *) 


let block fmt b =
  fprintf fmt "{ @[<v 0>";
  List.iter (statement fmt) b;
  fprintf fmt "@]@\n}"


let param fmt vi =
  fprintf fmt "%a %s" print_type vi.jc_var_info_type vi.jc_var_info_name

let print_decl fmt d =
  match d with
    | JCfun_def(ty,id,params,spec,body) ->
	fprintf fmt "@[%a %s(@[%a@])@\n%a@\n%a@]@\n@." print_type ty id
	  (print_list comma param) params 
	  print_spec spec block body 
    | JCrange_type_def(id,min,max) ->
	fprintf fmt "@[type %s = %s..%s@]@\n@."
	  id (Num.string_of_num min) (Num.string_of_num max)
	  

let rec print_decls fmt d =
  match d with
    | [] -> ()
    | d::r -> print_decl fmt d; print_decls fmt r

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
