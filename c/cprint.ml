(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: cprint.ml,v 1.29 2006-06-30 12:22:19 hubert Exp $ i*)

(* Pretty-printer for normalized AST *)

open Format
open Ctypes
open Clogic
open Cast
open Info
open Pp

let declare_struct fmt s (_,fields) =
  fprintf fmt "@[<hov 2>struct %s {@\n" s;
  begin match Cenv.tag_type_definition s with
    | Cenv.TTStructUnion(_,fields) ->
	List.iter (fun f ->
		     fprintf fmt "%a %s;@\n" ctype f.var_type f.var_unique_name) fields 
    | _ -> assert false
  end;
  fprintf fmt "};@]@\n@\n"

let term_unop = function
  | Clogic.Uminus -> "-"
  | Clogic.Utilde -> "~"
  | Clogic.Ustar -> "*"
  | Clogic.Uamp -> "&"
  | Clogic.Ufloat_of_int -> "float_of_int"
  | Clogic.Uint_of_float -> "int_of_float"
  | Clogic.Ufloat_conversion -> "float_conversion"
  | Clogic.Uabs_real -> "abs_real"
  | Clogic.Usqrt_real -> "sqrt_real"
  | Clogic.Uround_error -> "round_error"
  | Clogic.Utotal_error -> "total_error"
  | Clogic.Uexact -> "exact"
  | Clogic.Umodel -> "model"

let term_binop = function
  | Clogic.Badd -> "+"
  | Clogic.Bsub -> "-"
  | Clogic.Bmul -> "*"
  | Clogic.Bdiv -> "/"
  | Clogic.Bmod -> "%"
  | Clogic.Bpow_real -> "^^"
 
let rec nterm fmt t = match t.nterm_node with
  | NTconstant (IntConstant s | RealConstant s) ->
      fprintf fmt "%s" s
  | NTvar x ->
      fprintf fmt "%s" x.var_unique_name
  | NTapp {napp_pred = li; napp_args = tl;} ->
      fprintf fmt "%s(%a)" li.logic_name (print_list comma nterm) tl
  | NTunop (op, t) ->
      fprintf fmt "%s%a" (term_unop op) nterm_p t
(*  | NTstar t ->
      fprintf fmt "*%a" nterm_p t*)
  | NTbinop (t1, op, t2) ->
      fprintf fmt "%a %s %a" nterm_p t1 (term_binop op) nterm_p t2
  | NTarrow (t,_, vi) ->
      fprintf fmt "%a->%s" nterm_p t vi.var_unique_name
  | NTif (t1, t2, t3) ->
      fprintf fmt "%a ? %a : %a" nterm_p t1 nterm_p t2 nterm_p t3
  | NTold t ->
      fprintf fmt "\\old(%a)" nterm t
  | NTat (t, l) ->
      fprintf fmt "\\at(%a, %s)" nterm t l
  | NTbase_addr t ->
      fprintf fmt "\\base_addr(%a)" nterm t
  | NToffset t ->
      fprintf fmt "\\offset(%a)" nterm t
  | NTblock_length t ->
      fprintf fmt "\\block_length(%a)" nterm t
  | NTcast (ty, t) ->
      fprintf fmt "(%a)%a" ctype ty nterm t
  | NTrange (t1, t2, t3, _,_) ->
      fprintf fmt "%a[%a..%a]" nterm t1 nterm_option t2 nterm_option t3

and nterm_p fmt t = match t.nterm_node with
  | NTconstant _ | NTvar _ | NTapp _ | NTold _ | NTat _ ->
      nterm fmt t
  | _ ->
      fprintf fmt "(%a)" nterm t

and nterm_option fmt = function
  | None -> ()
  | Some t -> nterm fmt t

let quantifier fmt (ty, x) = fprintf fmt "%a %s" ctype ty x.var_unique_name

let quantifiers = print_list comma quantifier

let relation = function
  | Lt -> "<"
  | Gt -> ">"
  | Le -> "<="
  | Ge -> ">="
  | Eq -> "=="
  | Neq -> "!="
 
let rec npredicate fmt p = match p.npred_node with
  | NPfalse ->
      fprintf fmt "false"
  | NPtrue ->
      fprintf fmt "true"
  | NPapp {napp_pred = li; napp_args = tl;} ->
      fprintf fmt "%s(%a)" li.logic_name (print_list comma nterm) tl
  | NPrel (t1, rel, t2) ->
      fprintf fmt "%a %s %a" nterm t1 (relation rel) nterm t2
  | NPand (p1, p2) ->
      fprintf fmt "%a &&@ %a" npredicate p1 npredicate p2
  | NPor (p1, p2) ->
      fprintf fmt "%a ||@ %a" npredicate p1 npredicate p2
  | NPimplies (p1, p2) ->
      fprintf fmt "%a ->@ %a" npredicate p1 npredicate p2
  | NPiff (p1, p2) ->
      fprintf fmt "%a <->@ %a" npredicate p1 npredicate p2
  | NPnot p ->
      fprintf fmt "! %a" npredicate p
  | NPif (t, p1, p2) ->
      fprintf fmt "%a ? %a : %a" nterm t npredicate p1 npredicate p2
  | NPforall (q, p) ->
      fprintf fmt "\\forall %a;@ %a" quantifiers q npredicate p
  | NPexists (q, p) ->
      fprintf fmt "\\exists %a;@ %a" quantifiers q npredicate p
  | NPold p ->
      fprintf fmt "\\old(%a)" npredicate p
  | NPat (p, l) ->
      fprintf fmt "\\at(%a, %s)" npredicate p l
  | NPvalid t ->
      fprintf fmt "\\valid(%a)" nterm t
  | NPvalid_index (t1, t2) ->
      fprintf fmt "\\valid_index(%a, %a)" nterm t1 nterm t2
  | NPvalid_range (t1, t2, t3) ->
      fprintf fmt "\\valid_range(%a, %a, %a)" nterm t1 nterm t2 nterm t3
  | NPfresh t ->
      fprintf fmt "\\fresh(%a)" nterm t
  | NPnamed (id, p) ->
      fprintf fmt "%s:: %a" id npredicate p

let parameter fmt  x = fprintf fmt "%a %s" ctype x.var_type x.var_unique_name

let parameters = print_list comma parameter

let logic_parameter fmt (x, ty) = fprintf fmt "%a %s" ctype ty x.var_unique_name

let logic_parameters = print_list comma logic_parameter

let location = nterm
(****
let location fmt = function
  | Lterm t -> nterm fmt t
  | Lstar t -> fprintf fmt "%a[*]" nterm t
  | Lrange (t1, t2, t3) -> fprintf fmt "%a[%a..%a]" nterm t1 nterm t2 nterm t3
****)

let locations = print_list comma location

let nlogic_symbol fmt li = function
  | NPredicate_reads (pl, locs) ->
      fprintf fmt "/*@@ @[predicate %s(%a) reads %a@] */@\n" li.logic_name
	logic_parameters pl locations locs
  | NPredicate_def (pl, p) ->
      fprintf fmt "/*@@ @[predicate %s(%a) { %a }@] */@\n" li.logic_name
	logic_parameters pl npredicate p
  | NFunction (pl, ty, locs) ->
      fprintf fmt "/*@@ @[logic %a %s(%a) reads %a@] */@\n" ctype ty 
	li.logic_name logic_parameters pl locations locs
  | NFunction_def (pl, ty, t) ->
      fprintf fmt "/*@@ @[logic %a %s(%a) { %a }@] */@\n" ctype ty 
	li.logic_name logic_parameters pl nterm t
	
let spec fmt = function
  | { requires = None; assigns = None; ensures = None; decreases = None } ->
      ()
  | s ->
      let requires fmt p = fprintf fmt "@[requires %a@]@\n" npredicate p in
      let assigns fmt a = fprintf fmt "@[assigns %a@]@\n" locations a in
      let ensures fmt p = fprintf fmt "@[ensures %a@]@\n" npredicate p in
      let decreases fmt = function
	| (t, None) -> fprintf fmt "@[decreases %a@]@\n" nterm t
	| (t, Some r) -> fprintf fmt "@[decreases %a for %s@]@\n" nterm t r
      in
      fprintf fmt "/*@@ @[%a%a%a%a@] */@\n"
	(print_option requires) s.requires
	(print_option assigns) s.assigns
	(print_option ensures) s.ensures
	(print_option decreases) s.decreases

let loop_annot fmt = function
  | { invariant = None; loop_assigns = None; variant = None } ->
      ()
  | a ->
      let invariant fmt p = fprintf fmt "@[invariant %a@]@\n" npredicate p in
      let loop_assigns fmt a = fprintf fmt "@[assigns %a@]@\n" locations a in
      let variant fmt = function
	| (t, None) -> fprintf fmt "@[variant %a@]@\n" nterm t
	| (t, Some r) -> fprintf fmt "@[variant %a for %s@]@\n" nterm t r
      in
      fprintf fmt "/*@@ @[%a%a%a@] */@\n"
	(print_option invariant) a.invariant
	(print_option loop_assigns) a.loop_assigns
	(print_option variant) a.variant

let binop fmt = function
  | Badd | Badd_int _ | Badd_float _ | Badd_pointer_int -> fprintf fmt "+" 
  | Bsub | Bsub_int _ | Bsub_float _ | Bsub_pointer -> fprintf fmt "-"
  | Bmul | Bmul_int _ | Bmul_float _ -> fprintf fmt "*"
  | Bdiv | Bdiv_int _ | Bdiv_float _ -> fprintf fmt "/"
  | Bmod | Bmod_int _ -> fprintf fmt "%%" 
  | Blt | Blt_int | Blt_float _ | Blt_pointer -> fprintf fmt "<"
  | Bgt | Bgt_int | Bgt_float _ | Bgt_pointer -> fprintf fmt ">"
  | Ble | Ble_int | Ble_float _ | Ble_pointer -> fprintf fmt "<="
  | Bge | Bge_int | Bge_float _ | Bge_pointer -> fprintf fmt ">="
  | Beq | Beq_int | Beq_float _ | Beq_pointer -> fprintf fmt "=="
  | Bneq | Bneq_int | Bneq_float _ | Bneq_pointer -> fprintf fmt "!=" 
  | Bbw_and -> fprintf fmt "&"
  | Bbw_xor -> fprintf fmt "^"
  | Bbw_or -> fprintf fmt "|"
  | Band -> fprintf fmt "&&"
  | Bor -> fprintf fmt "||"
  | Bshift_left -> fprintf fmt "<<"
  | Bshift_right -> fprintf fmt ">>"


let unop fmt = function
  | Uplus -> fprintf fmt "+"
  | Uminus -> fprintf fmt "-"
  | Unot -> fprintf fmt "!"
  | Ustar -> fprintf fmt "*"
  | Uamp -> fprintf fmt "&"
  | Utilde -> fprintf fmt "~"
  (* these are introduced during typing *)
  | Ufloat_of_int -> fprintf fmt "float_of_int"
  | Uint_of_float -> fprintf fmt "int_of_float"
  | Ufloat_conversion -> fprintf fmt "float_conversion"
  | Uint_conversion -> fprintf fmt "int_conversion"

let rec nexpr fmt e = match e.nexpr_node with
  | NEnop ->
      ()
  | NEconstant (IntConstant s | RealConstant s) ->
      fprintf fmt "%s" s
  | NEstring_literal s ->
      fprintf fmt "\"%S\"" s
  | NEvar (Var_info x) ->
      fprintf fmt "%s" x.var_unique_name
  | NEvar (Fun_info x) ->
      fprintf fmt "%s" x.fun_name
  | NEarrow (e,_,x) ->
      fprintf fmt "%a->%s" nexpr_p e x.var_unique_name
(*  | NEstar e ->
      fprintf fmt "*%a" nexpr_p e*)
  | NEseq (e1, e2) ->
      fprintf fmt "%a, %a" nexpr e1 nexpr e2
  | NEassign (e1, e2) ->
      fprintf fmt "%a = %a" nexpr e1 nexpr e2
  | NEassign_op (e1, op, e2) ->
      fprintf fmt "%a %a= %a" nexpr e1 binop op nexpr e2
  | NEunary (op, e) ->
      fprintf fmt "%a%a" unop op nexpr_p e
  | NEincr (Uprefix_inc, e) -> fprintf fmt "++%a" nexpr_p e
  | NEincr (Uprefix_dec, e) -> fprintf fmt "--%a" nexpr_p e
  | NEincr (Upostfix_inc, e) -> fprintf fmt "%a++" nexpr_p e
  | NEincr (Upostfix_dec, e) -> fprintf fmt "%a--" nexpr_p e
  | NEbinary (e1, op, e2) ->
      fprintf fmt "%a %a %a" nexpr_p e1 binop op nexpr_p e2
  | NEcall { ncall_fun = e ; ncall_args = l } ->
      fprintf fmt "%a(%a)" nexpr e (print_list comma nexpr) l
  | NEcond (e1, e2, e3) ->
      fprintf fmt "%a ? %a : %a" nexpr e1 nexpr e2 nexpr e3
  | NEcast (ty, e) ->
      fprintf fmt "(%a)%a" ctype ty nexpr_p e
  | NEmalloc (ty, e) ->
      fprintf fmt "(%a*)malloc(%a * sizeof(%a))" ctype ty nexpr_p e ctype ty

and nexpr_p fmt e = match e.nexpr_node with
  | NEnop | NEconstant _ | NEstring_literal _ | NEvar _ -> nexpr fmt e
  | _ -> fprintf fmt "(@[%a@])" nexpr e

let rec c_initializer fmt = function
  | Iexpr e -> nexpr fmt e
  | Ilist l -> fprintf fmt "@[{ %a }@]" (print_list comma c_initializer) l

let rec nstatement fmt s = match s.nst_node with
  | NSnop -> 
      fprintf fmt ";"
  | NSexpr e ->
      fprintf fmt "@[%a;@]" nexpr e
  | NSif (e, s1, s2) ->
      fprintf fmt "@[if (%a) {@\n    @[%a@]@\n} else {@\n    @[%a@]@\n}@]"
	nexpr e nstatement_nb s1 nstatement_nb s2
  | NSwhile (a, e, s) ->
      fprintf fmt "@[%awhile (%a) {@\n    @[%a@]@\n}@]" 
	loop_annot a nexpr e nstatement_nb s
  | NSdowhile (a, s, e) ->
      fprintf fmt "@[%ado {@\n    @[%a@]@\n} while (%a);@]" 
	loop_annot a nstatement_nb s nexpr e 
  | NSfor (a, e1, e2, e3, s) ->
      fprintf fmt "@[%afor (%a; %a; %a) {@\n    @[%a@]@\n}@]"
	loop_annot a nexpr e1 nexpr e2 nexpr e2 nstatement_nb s
  | NSreturn None ->
      fprintf fmt "return;"
  | NSreturn (Some e) ->
      fprintf fmt "@[return %a;@]" nexpr e
  | NSbreak ->
      fprintf fmt "break;"
  | NScontinue ->
      fprintf fmt "continue;"
  | NSlabel (l, s) ->
      fprintf fmt "%s: %a" l nstatement s
  | NSswitch (e, m, l) ->
      (*** nexpr * (nexpr Cconst.IntMap.t) * 
      ((nexpr Cconst.IntMap.t * nstatement list) list) ***)
      fprintf fmt "<switch>"
  | NSassert p ->
      fprintf fmt "/*@@ assert %a */" npredicate p
  | NSlogic_label l ->
      fprintf fmt "/*@@ label %s */" l
  | NSspec (sp, s) ->
      fprintf fmt "%a%a" spec sp nstatement s
  | NSblock b ->
      fprintf fmt "@[{@\n  @[%a@]@\n}@]" nblock b
  | NSdecl (ty, vi, None,rem) ->
      fprintf fmt "@[<hov 2>{@\n%a %s;@\n" ctype ty vi.var_unique_name;
      nstatement fmt rem;
      fprintf fmt "}@\n@]"
  | NSdecl (ty, vi, Some i, rem) ->
      fprintf fmt "@[<hov 2>{@\n%a %s = %a;@\n" ctype ty vi.var_unique_name 
	c_initializer i;
      nstatement fmt rem;
      fprintf fmt "}@\n@]"

and nstatement_nb fmt s = match s.nst_node with
  | NSblock b -> nblock fmt b
  | _ -> nstatement fmt s

and nblock fmt sl =
  fprintf fmt "@[%a@]" 
    (print_list newline nstatement) sl

and ndecl fmt d = match d.node with
  | Nlogic (li, ls) -> 
      nlogic_symbol fmt li ls
  | Naxiom (x, p) -> 
      fprintf fmt "/*@@ @[axiom %s:@ %a@] */@\n" x npredicate p
  | Ninvariant (x, p) -> 
      fprintf fmt "/*@@ @[<hov 2>invariant %s:@ %a@] */@\n" x npredicate p 
  | Ninvariant_strong (x, p) -> 
      fprintf fmt "/*@@ @[<hov 2>strong invariant %s:@ %a@] */@\n" x 
	npredicate p
  | Ntypedef (ty, x) ->
      fprintf fmt "typedef %a %s;@\n" ctype ty x
  | Ntypedecl ty ->
      fprintf fmt "%a;@\n" ctype ty
  | Ndecl (ty, vi, None) ->
      fprintf fmt "%a %s;@\n" ctype ty vi.var_unique_name
  | Ndecl (ty, vi, Some i) ->
      fprintf fmt "%a %s = %a;@\n" ctype ty vi.var_unique_name c_initializer i
(*  | Nfunspec (s, ty, fi) ->
      fprintf fmt "%a%a %s(@[%a@]);@\n" spec s ctype ty fi.fun_name
	parameters fi.args
  | Nfundef (s, ty, fi, st) ->
      fprintf fmt "%a%a %s(@[%a@])@\n%a@\n" spec s ctype ty fi.fun_name
	 parameters fi.args nstatement st
*)
  | Ntype s ->
      fprintf fmt "/*@@ type %s */@\n" s

let nfile fmt p = 
  fprintf fmt "@[";
  Cenv.iter_all_struct (declare_struct fmt);
  List.iter (fun d -> ndecl fmt d; fprintf fmt "@\n") p;
  fprintf fmt "@]@."


let nfunctions fmt =
  Hashtbl.iter
    (fun f (s, ty, fi, st,_) -> 
       match st with
	 | Some st ->
	     fprintf fmt "%a%a %s(@[%a@])@\n%a@\n" spec s ctype ty fi.fun_name
	       parameters fi.args nstatement st
	 | None ->
	     fprintf fmt "%a%a %s(@[%a@]);@\n" spec s ctype ty fi.fun_name
	       parameters fi.args)
    Cenv.c_functions


