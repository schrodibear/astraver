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

(*i $Id: creport.ml,v 1.4 2004-02-10 08:18:02 filliatr Exp $ i*)

open Format
open Cerror
open Cast

exception Error of (Loc.t option) * Cerror.t

(*s Pretty-printing of types *)

let rec print_type fmt t = match t.ctype_node with
  | CTvoid -> fprintf fmt "void"
  | CTint (s, i) -> fprintf fmt "%a %a" print_sign s print_integer i
  | CTfloat f -> print_float fmt f
  | CTvar x -> fprintf fmt "%s" x
  | CTarray (ty, None) -> fprintf fmt "%a[]" print_type ty
  | CTarray (ty, Some e) -> fprintf fmt "%a[_]" print_type ty
  | CTpointer ty -> fprintf fmt "%a*" print_type ty
  | CTstruct_named x -> fprintf fmt "struct %s" x
  | CTstruct (_, fl) -> fprintf fmt "struct _ { %a}" print_fields fl
  | CTunion_named x -> fprintf fmt "union %s" x
  | CTunion (_, fl) -> fprintf fmt "union _ { %a}" print_fields fl
  | CTenum_named x -> fprintf fmt "enum %s" x
  | CTenum (_, el) -> fprintf fmt "enum _ { %a}" print_enums el
  | CTfun (pl, ty) -> fprintf fmt "%a fun(...)" print_type ty

and print_sign fmt = function
  | Signed -> fprintf fmt "signed"
  | Unsigned -> fprintf fmt "unsigned"

and print_integer fmt = function
  | Char -> fprintf fmt "char"
  | Short -> fprintf fmt "short"
  | Int -> fprintf fmt "int"
  | Long -> fprintf fmt "long"
  | LongLong -> fprintf fmt "long long"

and print_float fmt = function
  | Float -> fprintf fmt "float"
  | Double -> fprintf fmt "double"
  | LongDouble -> fprintf fmt "long double"

and print_fields fmt = function
  | [] -> ()
  | (ty, x, _) :: fl -> fprintf fmt "%a %s; %a" print_type ty x print_fields fl

and print_enums fmt = function
  | [] -> ()
  | (x, _) :: el -> fprintf fmt "%s, %a" x print_enums el

let report fmt = function
  | AnyMessage s -> 
      fprintf fmt "Error: %s" s
  | ExpectedType (t1, t2) -> 
      fprintf fmt "Error: this term has type @[%a@]@ but is expected to have type @[%a@]" print_type t1 print_type t2
  | TooManyArguments ->
      fprintf fmt "Error: too many arguments"
  | PartialApp ->
      fprintf fmt "Error: this application is partial"

let raise_located loc e = raise (Error (Some loc, e))
let raise_unlocated e = raise (Error (None, e))
let raise_locop locop e = raise (Error (locop, e))

let error l s = raise (Error (Some l, AnyMessage s))
let warning l s = 
  Format.eprintf "%a warning: %s\n" Loc.report_line (fst l) s

