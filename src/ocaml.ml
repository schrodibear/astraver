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

(*i $Id: ocaml.ml,v 1.1 2002-10-31 12:27:00 filliatr Exp $ i*)

(*s Ocaml code output *)

open Format
open Ident
open Logic
open Misc
open Util
open Types
open Ptree

(*s types and constants *)

let identifiers = print_list comma Ident.print

let rec typev fmt = function
  | PVref v -> 
      fprintf fmt "(%a ref)" typev v
  | PVarray (_, v) -> 
      fprintf fmt "(%a array)" typev v
  | PVarrow (bl, c) -> 
      fprintf fmt "%a -> %a" (print_list arrow binder_type) bl typec c
  | PVpure pt -> 
      print_pure_type fmt pt

and typec fmt c = 
  fprintf fmt "%a" typev c.pc_result_type

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

let rec lexpr fmt a = 
  fprintf fmt "<lexpr>"

(*s program expressions *)

let infix id = 
  if id == t_add then "+" 
  else if id == t_sub then "-" 
  else if id == t_mul then "*"
  else if id == t_div then "/"
  else "todo"

let rec expr fmt e = 
  fprintf fmt "%a" exprd e.pdesc

and exprd fmt = function
  | Svar id ->
      Ident.print fmt id
  | Srefget id ->
      fprintf fmt "!%a" Ident.print id
  | Srefset (id, e) ->
      fprintf fmt "%a := %a" Ident.print id expr e
  | Sarrget (_, id, e) ->
      fprintf fmt "%a.(%a)" Ident.print id expr e
  | Sarrset (_, id, e1, e2) ->
      fprintf fmt "%a.(%a) <- %a" Ident.print id expr e1 expr e2
  | Sseq bl ->
      fprintf fmt "@[begin %a end@]" block bl
  | Swhile (e1, inv, var, { pdesc = Sseq e2 }) ->
      fprintf fmt "while %a do %a done" expr e1 block e2
  | Swhile _ ->
      assert false
  | Sif (e1, e2, e3) ->
      fprintf fmt "@[if %a then %a else %a@]" expr e1 expr e2 expr e3
  | Slam (bl, e) ->
      fprintf fmt "(fun %a -> %a)" binder_ids bl expr e
  | Sapp ({pdesc=Sapp ({pdesc=Svar id}, Sterm e1)}, Sterm e2) 
    when is_poly id || id == t_mod_int ->
      fprintf fmt "(%a %s %a)" expr e1 (infix id) expr e2
  | Sapp (e, a) ->
      fprintf fmt "(%a %a)" expr e arg a
  | Sletref (id, e1, e2) ->
      fprintf fmt "@[@[<hov 2>let %a =@ ref %a in@]@\n%a@]" 
	Ident.print id expr e1 expr e2
  | Sletin (id, e1, e2) ->
      fprintf fmt "@[@[<hov 2>let %a =@ %a in@]@\n%a@]" 
	Ident.print id expr e1 expr e2
  | Srec (id, bl, v, var, e) ->
      fprintf fmt "(let rec %a %a = %a in %a)" 
	Ident.print id binder_ids bl expr e Ident.print id
  | Sraise (id, None, vo) ->
      fprintf fmt "raise %a" Ident.print id
  | Sraise (id, Some e, vo) ->
      fprintf fmt "raise (%a %a)" Ident.print id expr e
  | Stry (e, hl) ->
      fprintf fmt "(try %a with %a)" expr e (print_list alt handler) hl
  | Sconst c -> 
      constant fmt c

and block fmt = fprintf fmt "@[%a@]" (print_list space block_st)

and block_st fmt = function
  | Slabel l -> fprintf fmt "(* label %s *)" l
  | Sassert a -> fprintf fmt "(* assert %a *)" lexpr a
  | Sstatement e -> fprintf fmt "%a;" expr e

and arg fmt = function
  | Sterm e -> expr fmt e
  | Stype _ -> assert false

and handler fmt = function
  | (id, None), e -> 
      fprintf fmt "%a -> %a" Ident.print id expr e
  | (id, Some id'), e -> 
      fprintf fmt "%a %a -> %a" Ident.print id Ident.print id' expr e

let decl fmt = function
  | Program (id, e) -> 
      fprintf fmt "@[<hov 2>let %a =@ %a@]" Ident.print id expr e
  | Parameter _ ->
      assert false
  | External (_, ids, v) ->
      fprintf fmt "@[<hov 2>(* external %a :@ %a *)@]" identifiers ids typev v
  | Exception (_, id, None) ->
      fprintf fmt "exception %a" Ident.print id
  | Exception (_, id, Some pt) ->
      fprintf fmt "exception %a of %a" Ident.print id print_pure_type pt
  | Logic (_, id, lt) ->
      fprintf fmt "(* logic %a : %a *)" Ident.print id print_logic_type lt
  | QPvs s ->
      fprintf fmt "(* pvs \"%s\" *)" (String.escaped s)

(*s [functorize] collects the parameters *)

let functorize =
  let rec collect (pl, dl) = function
    | [] -> List.rev pl, List.rev dl
    | Parameter (_, ids, v) :: r -> collect ((ids, v) :: pl, dl) r
    | d :: r -> collect (pl, d :: dl) r
  in
  collect ([], [])

(*s We make a functor if some parameters are present *)

let parameter fmt (ids, v) =
  let print fmt id = 
    fprintf fmt "@[<hov 2>val %a : %a@]" Ident.print id typev v 
  in
  print_list newline print fmt ids

let output fmt p = 
  fprintf fmt "(* code generated by why --ocaml *)@\n@\n";
  let print_decl fmt d = fprintf fmt "@[%a@]@\n" decl d in
  let print_decls = print_list newline print_decl in
  let parameters = print_list newline parameter in
  match functorize p with
    | [], dl -> 
	fprintf fmt "@[%a@]" print_decls dl
    | pl, dl ->
	fprintf fmt "@[module type Parameters = sig@\n";
	fprintf fmt "  @[%a@]@\nend@\n@\n@]" parameters pl;
	fprintf fmt "@[module Make(P : Parameters) = struct@\n";
	fprintf fmt "  open P@\n@\n";
	fprintf fmt "  @[%a@]@\nend@\n@]" print_decls dl



