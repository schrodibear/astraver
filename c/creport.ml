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

(*i $Id: creport.ml,v 1.10 2004-10-11 15:22:48 hubert Exp $ i*)

open Format
open Cerror
open Cast

exception Error of (Loc.t option) * Cerror.t

(*s Pretty-printing of types *)

let rec print_type fmt t = 
  print_type_node fmt t.ctype_node

and print_type_node fmt = function
  | CTvoid -> fprintf fmt "void"
  | CTint (s, i) -> fprintf fmt "%a %a" print_sign s print_integer i
  | CTfloat f -> print_float fmt f
  | CTvar x -> fprintf fmt "%s" x
  | CTarray (ty, None) -> fprintf fmt "%a[]" print_type ty
  | CTarray (ty, Some e) -> fprintf fmt "%a[_]" print_type ty
  | CTpointer ty -> fprintf fmt "%a*" print_type ty
  | CTstruct (x, Tag) -> 
      fprintf fmt "struct %s" x
  | CTstruct (x, Decl fl) -> 
      fprintf fmt "struct %s { %a}" x print_fields fl
  | CTunion (x, Tag) -> 
      fprintf fmt "union %s <incomplete>" x
  | CTunion (x, Decl fl) -> 
      fprintf fmt "union %s { %a}" x print_fields fl
  | CTenum (x, Tag) -> fprintf fmt "enum %s" x
  | CTenum (x, Decl el) -> fprintf fmt "enum %s { %a}" x print_enums el
  | CTfun (pl, ty) -> fprintf fmt "%a fun(...)" print_type ty
  | CTtyped_fun (pl, ty) -> fprintf fmt "%a fun(...)" print_type ty

and print_sign fmt = function
  | Signed -> fprintf fmt "signed"
  | Unsigned -> fprintf fmt "unsigned"

and print_integer fmt = function
  | Char -> fprintf fmt "char"
  | Short -> fprintf fmt "short"
  | Int -> fprintf fmt "int"
  | Long -> fprintf fmt "long"
  | LongLong -> fprintf fmt "long long"
  | Bitfield _ -> fprintf fmt "int (bitfield)"

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
  | Unsupported s ->
      fprintf fmt "Error: unsupported feature (%s)" s

let raise_located loc e = raise (Error (Some loc, e))
let raise_unlocated e = raise (Error (None, e))
let raise_locop locop e = raise (Error (locop, e))
let unsupported s = raise (Error (None, Unsupported s))

let error l s = raise (Error (Some l, AnyMessage s))
let warning l s = 
  Format.eprintf "@[%a warning: %s@]@." Loc.report_line (fst l) s;
  if Coptions.werror then exit 1


