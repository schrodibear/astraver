

open Format
open Jc_env
open Jc_fenv
open Jc_ast
open Pp

type jc_decl =
  | JCfun_def of jc_type * string * (jc_type * string) list *
      tfun_spec * tstatement list

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

let rec term fmt t =
  match t.jc_tterm_node with
    | JCTTvar vi -> fprintf fmt "%s" vi.jc_var_info_name
    | JCTTif (_, _, _)-> assert false (* TODO *)
    | JCTTcast (_, _)-> assert false (* TODO *)
    | JCTTinstanceof (_, _)-> assert false (* TODO *)
    | JCTToffset_min (_, _)-> assert false (* TODO *)
    | JCTToffset_max (_, _)-> assert false (* TODO *)
    | JCTTold _-> assert false (* TODO *)
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
	fprintf fmt "@[(forall %a %s; %a)@]"
	  print_type vi.jc_var_info_type
	  vi.jc_var_info_name
	  assertion a
    | JCTAapp (op, l) ->
	fprintf fmt "%s(@[%a@])" op.jc_logic_info_name
	  (print_list comma term) l 
    | JCTAnot _-> assert false (* TODO *)
    | JCTAiff (_, _)-> assert false (* TODO *)
    | JCTAimplies (a1, a2)-> 
	fprintf fmt "@[(%a => %a)@]" assertion a1 assertion a2
    | JCTAor _-> assert false (* TODO *)
    | JCTAand (a::l) -> 
	fprintf fmt "@[(%a" assertion a;
	List.iter
	  (fun a -> fprintf fmt " && %a" assertion a)
	  l;
	fprintf fmt ")@]"
    | JCTAfalse -> assert false (* TODO *)


let behavior fmt (id,b) =
  fprintf fmt "@[<v 2>behavior %s:@\n" id;
  Option_misc.iter
    (fun a -> fprintf fmt "assumes %a;@\n" assertion a) 
    b.jc_tbehavior_assumes;
  fprintf fmt "ensures %a;@]" assertion b.jc_tbehavior_ensures
  
let print_spec fmt s =
  fprintf fmt "requires @[%a@];@ " assertion s.jc_tfun_requires;
  List.iter (behavior fmt) s.jc_tfun_behavior

let print_decl fmt d =
  match d with
    | JCfun_def(ty,id,params,spec,body) ->
	fprintf fmt "@[%a %s()@ %a@ { }@]@." print_type ty id
	  print_spec spec (* print_block body *)
	  

let rec print_decls fmt d =
  match d with
    | [] -> ()
    | d::r -> print_decl fmt d; print_decls fmt r

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
