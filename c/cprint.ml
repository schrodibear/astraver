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

(*i $Id: cprint.ml,v 1.2 2004-12-08 10:59:24 filliatr Exp $ i*)

(* Pretty-printer for normalized AST *)

open Format
open Ctypes
open Clogic
open Cast
open Info
open Pp

let rec ctype fmt ty =
  ctype_node fmt ty.Ctypes.ctype_node

and ctype_node fmt = function
  | Tvoid -> fprintf fmt "void"
  | Tint _ -> fprintf fmt "int"
  | Tfloat _ -> fprintf fmt "float"
  | Ctypes.Tvar s -> fprintf fmt "%s" s
  | Tarray (ty, None) -> fprintf fmt "%a[]" ctype ty
  | Tarray (ty, Some n) -> fprintf fmt "%a[%Ld]" ctype ty n
  | Tpointer ty -> fprintf fmt "%a*" ctype ty
  | Tstruct s -> fprintf fmt "struct %s" s
  | Tunion s -> fprintf fmt "union %s" s
  | Tenum s -> fprintf fmt "enum %s" s
  | Tfun _ -> fprintf fmt "<fun>"

let nterm fmt t = 
  fprintf fmt "<term>"

let npredicate fmt p = 
  fprintf fmt "<predicate>"

let parameter fmt (ty, x) = fprintf fmt "%a %s" ctype ty x.var_name

let parameters = print_list comma parameter

let logic_parameter fmt (x, ty) = fprintf fmt "%a %s" ctype ty x.var_name

let logic_parameters = print_list comma logic_parameter

let locations fmt l = fprintf fmt "<locations>"

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
	
let spec fmt = function
  | { requires = None; assigns = None; ensures = None; decreases = None } ->
      ()
  | s ->
      let requires fmt p = fprintf fmt "requires %a@\n" npredicate p in
      let assigns fmt a = fprintf fmt "assigns %a@\n" locations a in
      let ensures fmt p = fprintf fmt "ensures %a@\n" npredicate p in
      let decreases fmt = function
	| (t, None) -> fprintf fmt "decreases %a@\n" nterm t
	| (t, Some r) -> fprintf fmt "decreases %a for %s@\n" nterm t r
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
      let invariant fmt p = fprintf fmt "invariant %a@\n" npredicate p in
      let loop_assigns fmt a = fprintf fmt "assigns %a@\n" locations a in
      let variant fmt = function
	| (t, None) -> fprintf fmt "variant %a@\n" nterm t
	| (t, Some r) -> fprintf fmt "variant %a for %s@\n" nterm t r
      in
      fprintf fmt "/*@@ @[%a%a%a@] */@\n"
	(print_option invariant) a.invariant
	(print_option loop_assigns) a.loop_assigns
	(print_option variant) a.variant

let binop fmt = function
  | Badd | Badd_int | Badd_float | Badd_pointer_int -> fprintf fmt "+" 
  | Bsub | Bsub_int | Bsub_float | Bsub_pointer -> fprintf fmt "-"
  | Bmul | Bmul_int | Bmul_float -> fprintf fmt "*"
  | Bdiv | Bdiv_int | Bdiv_float -> fprintf fmt "/"
  | Bmod | Bmod_int -> fprintf fmt "%%" 
  | Blt | Blt_int | Blt_float | Blt_pointer -> fprintf fmt "<"
  | Bgt | Bgt_int | Bgt_float | Bgt_pointer -> fprintf fmt ">"
  | Ble | Ble_int | Ble_float | Ble_pointer -> fprintf fmt "<="
  | Bge | Bge_int | Bge_float | Bge_pointer -> fprintf fmt ">="
  | Beq | Beq_int | Beq_float | Beq_pointer -> fprintf fmt "=="
  | Bneq | Bneq_int | Bneq_float | Bneq_pointer -> fprintf fmt "!=" 
  | Bbw_and -> fprintf fmt "&"
  | Bbw_xor -> fprintf fmt "<bw_xor>"
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

let rec nexpr fmt e = match e.nexpr_node with
  | NEnop ->
      ()
  | NEconstant (IntConstant s | FloatConstant s) ->
      fprintf fmt "%s" s
  | NEstring_literal s ->
      fprintf fmt "\"%S\"" s
  | NEvar (Var_info x) ->
      fprintf fmt "%s" x.var_name
  | NEvar (Fun_info x) ->
      fprintf fmt "%s" x.fun_name
  | NEarrow (e, x) ->
      fprintf fmt "(%a->%s)" nexpr e x.var_name
  | NEstar e ->
      fprintf fmt "( *%a)" nexpr e
  | NEseq (e1, e2) ->
      fprintf fmt "(%a, %a)" nexpr e1 nexpr e2
  | NEassign (e1, e2) ->
      fprintf fmt "(%a = %a)" nexpr e1 nexpr e2
  | NEassign_op (e1, op, e2) ->
      fprintf fmt "(%a %a= %a)" nexpr e1 binop op nexpr e2
  | NEunary (op, e) ->
      fprintf fmt "(%a %a)" unop op nexpr e
  | NEincr (Uprefix_inc, e) -> fprintf fmt "(++%a)" nexpr e
  | NEincr (Uprefix_dec, e) -> fprintf fmt "(--%a)" nexpr e
  | NEincr (Upostfix_inc, e) -> fprintf fmt "(%a++)" nexpr e
  | NEincr (Upostfix_dec, e) -> fprintf fmt "(%a--)" nexpr e
  | NEbinary (e1, op, e2) ->
      fprintf fmt "(%a %a %a)" nexpr e1 binop op nexpr e2
  | NEcall (e, l) ->
      fprintf fmt "%a(%a)" nexpr e (print_list comma nexpr) l
  | NEcond (e1, e2, e3) ->
      fprintf fmt "(%a ? %a : %a)" nexpr e1 nexpr e2 nexpr e3
  | NEcast (ty, e) ->
      fprintf fmt "((%a) %a)" ctype ty nexpr e

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
      fprintf fmt "@[{@\n    @[%a@]@\n}@]" nblock b

and nstatement_nb fmt s = match s.nst_node with
  | NSblock b -> nblock fmt b
  | _ -> nstatement fmt s

and nblock fmt (dl, sl) =
  fprintf fmt "@[%a%a@]" 
    (print_list nothing ndecl) dl (print_list newline nstatement) sl

and ndecl fmt d = match d.node with
  | Nlogic (li, ls) -> 
      nlogic_symbol fmt li ls
  | Naxiom (x, p) -> 
      fprintf fmt "/*@@ @[axiom %s:@ %a@] */@\n" x npredicate p
  | Ninvariant (x, p) -> 
      fprintf fmt "/*@@ @[invariant %s:@ %a@] */@\n" x npredicate p 
  | Ntypedef (ty, x) ->
      fprintf fmt "typedef %a %s;@\n" ctype ty x
  | Ntypedecl ty ->
      fprintf fmt "%a;@\n" ctype ty
  | Ndecl (ty, vi, None) ->
      fprintf fmt "%a %s;@\n" ctype ty vi.var_name
  | Ndecl (ty, vi, Some i) ->
      fprintf fmt "%a %s = %a;@\n" ctype ty vi.var_name c_initializer i
  | Nfunspec (s, ty, fi, pl) ->
      fprintf fmt "%a%a %s(@[%a@]);@\n" spec s ctype ty fi.fun_name
	parameters pl
  | Nfundef (s, ty, fi, pl, st) ->
      fprintf fmt "%a@\n%a %s(@[%a@])@\n%a@\n" spec s ctype ty fi.fun_name
	(print_list comma parameter) pl nstatement st

let nfile fmt p = 
  fprintf fmt "@[";
  List.iter (fun d -> ndecl fmt d; fprintf fmt "@\n") p;
  fprintf fmt "@]@."


