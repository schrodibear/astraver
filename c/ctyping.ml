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

(*i $Id: ctyping.ml,v 1.3 2003-12-23 16:34:36 filliatr Exp $ i*)

open Cast
open Cerror
open Creport

(* Typing C programs *)

let located_app f x = { node = f x.node; loc = x.loc }

let option_app f = function Some x -> Some (f x) | None -> None

let error l s = raise (Error (Some l, AnyMessage s))

let noattr tyn = { ctype_node = tyn; 
		   ctype_storage = No_storage;
		   ctype_const = false;
		   ctype_volatile = false }
let c_void = noattr CTvoid
let c_int = noattr (CTint (Signed, Int))
let c_char = noattr (CTint (Unsigned, Char))
let c_float = noattr (CTfloat Float)
let c_string = noattr (CTpointer c_char)

(*s Environments for local variables *)

module Env = Map.Make(String)

(*s Types *)

let rec type_type ty = { ty with ctype_node = type_type_node ty.ctype_node }

and type_type_node = function
  | CTvoid | CTint _ | CTfloat _ as ty -> 
      ty
  | CTvar _ as ty -> 
      ty (* TODO: qq chose à vérifier ici ? *)
  | CTarray (tyn, eo) -> 
      (* TODO: vérifier type int *)
      CTarray (type_type tyn, type_int_expr_option Env.empty eo)
  | CTpointer tyn -> 
      CTpointer (type_type tyn)
  | CTstruct_named x | CTunion_named x | CTenum_named x as ty ->
      (* TODO: vérifier existence *)
      ty
  | CTstruct_decl (x, fl) ->
      CTstruct_decl (x, List.map type_field fl)
  | CTunion_decl (x, fl) ->
      CTunion_decl (x, List.map type_field fl)
  | CTenum_decl (x, fl) ->
      let type_enum_field (f, eo) = (f, type_int_expr_option Env.empty eo) in
      CTenum_decl (x, List.map type_enum_field fl)
  | CTfun (pl, tyn) ->
      CTfun (List.map type_parameter pl, type_type tyn)

(*s Expressions *)

and type_expr env e = 
  let tn,ty = type_expr_node e.loc env e.node in
  { texpr_node = tn; texpr_type = ty; texpr_loc = e.loc }

and type_expr_node loc env = function
  | CEnop ->
      TEnop, c_void
  | CEconstant s ->
      (try 
	 let _ = int_of_string s in TEconstant s, c_int
       with _ -> 
	 TEconstant s, c_float)
  | CEstring_literal s ->
      TEstring_literal s, c_string
  | CEvar x ->
      assert false (*TODO*)
  | CEdot (e, x) ->
      let te = type_lvalue env e in
      assert false (*TODO type_of_field te.texpr_type x *)
  | CEarrow (e, x) ->
      let te = type_lvalue env e in
      assert false (*TODO type_of_field te.texpr_type x *)
  | CEarrget (e1, e2) ->
      let te1 = type_lvalue env e1 in
      (match te1.texpr_type.ctype_node with
	 | CTarray (ty, _) | CTpointer ty ->
	     let te2 = type_int_expr env e2 in
	     TEarrget (te1, te2), ty
	 | _ ->
	     error loc "subscripted value is neither array nor pointer")
(**
  | CEseq of cexpr * cexpr
  | CEassign of cexpr * assign_operator * cexpr
  | CEunary of unary_operator * cexpr
  | CEbinary of cexpr * binary_operator * cexpr
  | CEcall of cexpr * cexpr list
  | CEcond of cexpr * cexpr * cexpr
  | CEshift of cexpr * shift * cexpr
  | CEcast of cexpr ctype * cexpr
  | CEsizeof_expr of cexpr
  | CEsizeof of cexpr ctype
**)
  | _ ->
      assert false (*TODO*)

and type_lvalue env e = type_expr env e (*TODO*)

and type_expr_option env eo = option_app (type_expr env) eo

and type_int_expr_option env eo = option_app (type_int_expr env) eo

and type_int_expr env e = match type_expr env e with
  | { texpr_type = { ctype_node = CTint _ } } as te -> te
  | _ -> error e.loc "expected int"

and type_parameter (ty, x) = (type_type ty, x)

and type_field (ty, x, bf) = (type_type ty, x, type_expr_option Env.empty bf)

let rec type_initializer ty = function
  | Inothing -> Inothing
  | Iexpr e -> Iexpr (type_expr Env.empty e) (* TODO: vérifier type = ty *)
  | Ilist el -> Ilist (List.map (type_initializer ty) el) (* TODO: FAUX! *)

let rec type_statement s =
  assert false (*TODO*)

and type_block bl = 
  assert false (*TODO*)
 
let type_decl = function
  | Cspecdecl a -> 
      assert false (*TODO*)
  | Ctypedef (ty, x) -> 
      Ttypedef (type_type ty, x)
  | Ctypedecl ty -> 
      Ttypedecl (type_type ty)
  | Cdecl (ty, x, i) -> 
      let ty = type_type ty in
      Tdecl (ty, x, type_initializer ty i)
  | Cfundef (ty, f, pl, bl) -> 
      Tfundef (type_type ty, f, List.map type_parameter pl, 
	       located_app type_block bl)

let type_file = List.map (located_app type_decl)

