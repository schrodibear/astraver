(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
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

(*i $Id: ocaml.ml,v 1.9 2003-04-02 11:58:57 filliatr Exp $ i*)

(*s Ocaml code output *)

open Format
open Options
open Ident
open Logic
open Misc
open Util
open Types
open Env
open Ast

(*s pre- and postconditions *)

let pre = 
  let print fmt p = fprintf fmt "(* @[%a@] *)" print_predicate p.a_value in
  print_list newline print

let post fmt q = 
  let exn fmt (x,a) = fprintf fmt "%a => %a" Ident.print x print_assertion a in
  match q with 
    | (a, []) -> 
	fprintf fmt "(* @[%a@] *)" print_assertion a 
    | (a, al) -> 
	fprintf fmt "(* @[%a@ | %a@] *)" 
	  print_assertion a (print_list alt exn) al

(*s types and constants *)

let identifiers = print_list comma Ident.print

let rec typev fmt = function
  | Ref v -> 
      fprintf fmt "(%a ref)" typev v
  | Array v -> 
      fprintf fmt "(%a array)" typev v
  | Arrow (bl, c) -> 
      fprintf fmt "%a ->@ %a" (print_list arrow binder_type) bl typec c
  | PureType pt -> 
      print_pure_type fmt pt

and typec fmt c = match c.c_pre, c.c_post with
  | [], None ->
      fprintf fmt "%a" typev c.c_result_type
  | [], Some q ->
      fprintf fmt "%a@ %a" typev c.c_result_type post q
  | p, None ->
      fprintf fmt "%a@ %a" pre p typev c.c_result_type
  | p, Some q ->
      fprintf fmt "%a@ %a@ %a" pre p typev c.c_result_type post q

and binder_type fmt = function
  | id, BindType v when id == Ident.anonymous -> typev fmt v
  | id, BindType v -> fprintf fmt "(*%a:*)%a" Ident.print id typev v
  | _, (BindSet | Untyped) -> assert false

let binder_id fmt = function
  | id, BindType v -> fprintf fmt "%a (*:%a*)" Ident.print id typev v
  | id, Untyped -> Ident.print fmt id
  | _, BindSet -> assert false

let binder_ids = print_list space binder_id

let constant fmt = function
  | ConstInt n -> fprintf fmt "%d" n
  | ConstBool b -> fprintf fmt "%b" b
  | ConstUnit -> fprintf fmt "()"
  | ConstFloat f -> fprintf fmt "%s" f

(*s logical expressions *)

let caml_infix id = is_arith_binop id || is_relation id

let infix id = 
  if id == t_add_int then "+" 
  else if id == t_sub_int then "-" 
  else if id == t_mul_int then "*"
  else if id == t_div_int then "/"
  else if id == t_mod_int then "mod"
  else if id == t_add_int then "+." 
  else if id == t_sub_int then "-." 
  else if id == t_mul_int then "*."
  else if id == t_div_int then "/."
  else if is_eq id then "="
  else if is_neq id then "<>"
  else if id == t_lt_int || id == t_lt_float then "<"
  else if id == t_le_int || id == t_le_float then "<="
  else if id == t_gt_int || id == t_gt_float then ">"
  else if id == t_ge_int || id == t_ge_float then ">="
  else assert false

let prefix fmt id = fprintf fmt "( %s )" (infix id)

let rec expression fmt = function
  | Tvar id -> 
      Ident.print fmt id
  | Tconst c -> 
      constant fmt c
  | Tderef id ->
      fprintf fmt "!%a" Ident.print id
  | Tapp (id, [Tderef t]) when id == Ident.array_length ->
      fprintf fmt "(Array.length %a)" Ident.print t
  | Tapp (id, [t]) when id == t_neg_int ->
      fprintf fmt "(-%a)" expression t
  | Tapp (id, [t]) when id == t_neg_float ->
      fprintf fmt "(-. %a)" expression t
  | Tapp (id, [t]) when id == t_sqrt_float ->
      fprintf fmt "(sqrt %a)" expression t
  | Tapp (id, [t]) when id == t_float_of_int ->
      fprintf fmt "(float %a)" expression t
  | Tapp (id, [a; b]) when id == access ->
      fprintf fmt "%a.(%a)" expression a expression b
  | Tapp (id, [a; b]) when caml_infix id ->
      fprintf fmt "(%a %s %a)" expression a (infix id) expression b
  | Tapp (id, tl) -> 
      fprintf fmt "(%a %a)" Ident.print id (print_list space expression) tl

(*s program expressions *)

let rec expr fmt e = 
  let k = e.info.kappa in
  let p = k.c_pre in
  let q = k.c_post in
  if not ocaml_annot || (p = [] && q = None) then
    fprintf fmt "@[%a@]" exprd e.desc
  else match p, q with
    | [], Some q -> 
	fprintf fmt "@[<hv>%a@ %a@]" exprd e.desc post q
    | p, None ->
	fprintf fmt "@[<hv>%a@ %a@]" pre p exprd e.desc
    | p, Some q ->
	fprintf fmt "@[<hv>%a@ %a@ %a@]" pre p exprd e.desc post q

and exprd fmt = function
  | Var id when caml_infix id ->
      fprintf fmt "%a" prefix id
  | Var id ->
      Ident.print fmt id
  | Acc id ->
      fprintf fmt "!%a" Ident.print id
  | Aff (id, e) ->
      fprintf fmt "@[<hov 2>(%a := %a)@]" Ident.print id expr e
  | TabAcc (_, id, e) ->
      fprintf fmt "%a.(%a)" Ident.print id expr e
  | TabAff (_, id, e1, e2) ->
      fprintf fmt "@[<hov 2>(%a.(%a) <-@ %a)@]" Ident.print id expr e1 expr e2
  | Seq bl ->
      fprintf fmt "@[<hv>begin@;<1 2>%a@ end@]" block bl
  | While (e1, inv, var, { desc = Seq e2 }) ->
      fprintf fmt "@[<hv>while %a do@;<1 2>%a@ done@]" expr e1 block e2
  | While (e1, inv, var, e2) ->
      fprintf fmt "@[<hv>while %a do@;<1 2>%a@ done@]" expr e1 expr e2
  | If (e1, e2, e3) ->
      fprintf fmt "(@[<hv>if %a then@;<1 2>%a@ else@;<1 2>%a@])" 
	expr e1 expr e2 expr e3
  | Lam (bl, e) ->
      fprintf fmt "@[<hov 2>(fun %a ->@ %a)@]" binder_ids bl expr e
  | App ({desc=App ({desc=Var id}, Term e1, _)}, Term e2, _) 
    when is_poly id || id == t_mod_int ->
      fprintf fmt "@[<hov 2>(%a %s@ %a)@]" expr e1 (infix id) expr e2
  | App (e, a, _) ->
      fprintf fmt "@[<hov 2>(%a@ %a)@]" expr e arg a
  | LetRef (id, e1, e2) ->
      fprintf fmt "@[(@[<hov 2>let %a =@ ref %a in@]@\n%a)@]" 
	Ident.print id expr e1 expr e2
  | LetIn (id, e1, e2) ->
      fprintf fmt "@[(@[<hov 2>let %a =@ %a in@]@\n%a)@]" 
	Ident.print id expr e1 expr e2
  | Rec (id, bl, v, var, e) ->
      fprintf fmt "@[<hov 2>(let rec %a %a =@ %a in@ %a)@]" 
	Ident.print id binder_ids bl expr e Ident.print id
  | Raise (id, None) ->
      fprintf fmt "@[<hov 2>(raise %a)@]" Ident.print id
  | Raise (id, Some e) ->
      fprintf fmt "@[<hov 2>(raise@ (%a %a))@]" Ident.print id expr e
  | Try (e, hl) ->
      fprintf fmt "(@[<hv>try@;<1 2>%a@ with@ @[<v>%a@]@])" 
	expr e (print_list newline handler) hl
  | Expression t -> 
      expression fmt t
  | Absurd ->
      fprintf fmt "@[assert false@]"

and block fmt = fprintf fmt "@[<hv>%a@]" (print_list space block_st)

and block_st fmt = function
  | Label l -> fprintf fmt "(* label %s *)" l
  | Assert a -> fprintf fmt "(* assert %a *)" print_assertion a
  | Statement e -> fprintf fmt "%a;" expr e

and arg fmt = function
  | Term e -> expr fmt e
  | Refarg id -> Ident.print fmt id
  | Type _ -> assert false

and handler fmt = function
  | (id, None), e -> 
      fprintf fmt "| %a -> %a" Ident.print id expr e
  | (id, Some id'), e -> 
      fprintf fmt "| %a %a -> %a" Ident.print id Ident.print id' expr e

let decl fmt (id, e) =
  fprintf fmt "@[<hov 2>let %a =@ %a@]@\n@\n" Ident.print id expr e

(*s Parameters (collected to make a functor) *)

let params = Queue.create ()

let push_parameters ids v = List.iter (fun id -> Queue.add (id, v) params) ids

(*s We make a functor if some parameters are present *)

let parameter fmt (id, v) =
  fprintf fmt "@\n@[<hov 2>val %a : %a@]@\n" Ident.print id typev v 

let progs = Queue.create ()

let push_program id p = Queue.add (id, p) progs

let output fmt = 
  fprintf fmt "(* code generated by why --ocaml *)@\n@\n";
  let print_decls fmt () = Queue.iter (decl fmt) progs in
  if Queue.is_empty params then
    fprintf fmt "@[%a@]" print_decls ()
  else begin
    fprintf fmt "@[module type Parameters = sig@\n  @[";
    Queue.iter (parameter fmt) params;
    fprintf fmt "@]@\nend@\n@\n@]";
    fprintf fmt "@[module Make(P : Parameters) = struct@\n";
    fprintf fmt "  open P@\n@\n";
    fprintf fmt "  @[%a@]@\nend@\n@]" print_decls ()
  end



