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

(*i $Id: ctyping.ml,v 1.1 2003-12-23 15:11:00 filliatr Exp $ i*)

open Cast

(* Typing C programs *)

let located_app f x = { node = f x.node; loc = x.loc }

let rec type_type ty =
  assert false (*TODO*)

and type_expr e =
  assert false (*TODO*)

and type_parameters pl =
  assert false (*TODO*)

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
      Tfundef (type_type ty, f, type_parameters pl, located_app type_block bl)

let type_file = List.map (located_app type_decl)

