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

(*i $Id: ctyping.ml,v 1.2 2003-12-23 15:45:53 filliatr Exp $ i*)

open Cast

(* Typing C programs *)

let located_app f x = { node = f x.node; loc = x.loc }

let option_app f = function Some x -> Some (f x) | None -> None

let rec type_type ty = { ty with ctype_node = type_type_node ty.ctype_node }

and type_type_node = function
  | CTvoid | CTint _ | CTfloat _ as ty -> 
      ty
  | CTvar _ as ty -> 
      ty (* TODO: qq chose à vérifier ici ? *)
  | CTarray (tyn, eo) -> 
      (* TODO: vérifier type int *)
      CTarray (type_type_node tyn, type_expr_option eo)
  | CTpointer tyn -> 
      CTpointer (type_type_node tyn)
  | CTbitfield (tyn, e) ->
      CTbitfield (type_type_node tyn, type_expr e)
  | CTstruct_named x | CTunion_named x | CTenum_named x as ty ->
      (* TODO: vérifier existence *)
      ty
  | CTstruct_decl (x, fl) ->
      CTstruct_decl (x, List.map type_field fl)
  | CTunion_decl (x, fl) ->
      CTunion_decl (x, List.map type_field fl)
  | CTenum_decl (x, fl) ->
      CTenum_decl (x, List.map (fun (f,eo) -> (f, type_expr_option eo)) fl)
  | CTfun (pl, tyn) ->
      CTfun (List.map type_parameter pl, type_type_node tyn)

and type_expr e =
  assert false (*TODO*)

and type_expr_option eo = option_app type_expr eo

and type_parameter (ty, x) = (type_type ty, x)

and type_field (ty, x, bf) = (type_type ty, x, type_expr_option bf)

let rec type_initializer = function
  | Inothing -> Inothing
  | Iexpr e -> Iexpr (type_expr e)
  | Ilist el -> Ilist (List.map type_initializer el)

let rec type_statement s =
  assert false (*TODO*)

and type_block bl = 
  assert false (*TODO*)
 
let type_decl = function
  | Cspecdecl a -> assert false (*TODO*)
  | Ctypedef (ty, x) -> Ttypedef (type_type ty, x)
  | Ctypedecl ty -> Ttypedecl (type_type ty)
  | Cdecl (ty, x, i) -> Tdecl (type_type ty, x, type_initializer i)
  | Cfundef (ty, f, pl, bl) -> 
      Tfundef (type_type ty, f, List.map type_parameter pl, 
	       located_app type_block bl)

let type_file = List.map (located_app type_decl)

