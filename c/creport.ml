(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: creport.ml,v 1.19 2006-07-19 15:27:37 marche Exp $ i*)

open Format
open Cerror
open Ctypes

exception Error of (Loc.position option) * Cerror.t

(*s Pretty-printing of types *)

let rec print_type fmt t = 
  print_type_node fmt t.ctype_node

and print_type_node fmt = function
  | Tvoid -> fprintf fmt "void"
  | Tint (s, i) -> fprintf fmt "%a %a" print_sign s print_integer i
  | Tfloat f -> print_float fmt f
  | Tvar x -> fprintf fmt "%s" x
  | Tarray (_,ty,_) -> fprintf fmt "%a[]" print_type ty
  | Tpointer (_,ty) -> fprintf fmt "%a*" print_type ty
  | Tstruct (x) -> fprintf fmt "struct %s" x
  | Tunion (x) -> fprintf fmt "union %s" x
  | Tenum (x) -> fprintf fmt "enum %s" x
  | Tfun (pl, ty) -> fprintf fmt "%a fun(...)" print_type ty

and print_sign fmt = function
  | Signed -> fprintf fmt "signed"
  | Unsigned -> fprintf fmt "unsigned"

and print_integer fmt = function
  | Char -> fprintf fmt "char"
  | Short -> fprintf fmt "short"
  | Int -> fprintf fmt "int"
  | Long -> fprintf fmt "long"
  | LongLong -> fprintf fmt "long long"
  | Bitfield _  -> fprintf fmt "int (bitfield)"

and print_float fmt = function
  | Float -> fprintf fmt "float"
  | Double -> fprintf fmt "double"
  | LongDouble -> fprintf fmt "long double"
  | Real -> fprintf fmt "real"

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

let offset = ref 0

let reloc (ls, le) = (!offset + ls, !offset + le)

let with_offset ofs f x =
  let old_offset = !offset in
  try
    offset := ofs;
    let r = f x in
    offset := old_offset;
    r
  with e ->
    offset := old_offset;
    raise e
(*** 
    | Stdpp.Exc_located (loc, e) -> 
	raise (Stdpp.Exc_located (Compat.offset ofs loc, e))
    | Error (Some loc, e) ->
	raise (Error (Some (offset ofs loc), e))
***)

let option_app f = function Some x -> Some (f x) | None -> None

let raise_located loc e = raise (Error (Some (loc), e))
let raise_unlocated e = raise (Error (None, e))
let raise_locop locop e = raise (Error (locop, e))
let unsupported loc s = raise (Error (Some loc, Unsupported s))

let error l s = raise (Error (Some l, AnyMessage s))
let errorf l f = ksprintf (fun s -> raise (Error (Some l, AnyMessage s))) f

let wtbl = Hashtbl.create 17;;

let warning l s = 
  let n = try Hashtbl.find wtbl s with Not_found -> 0 in
  if n <= 2 then
    begin
      Hashtbl.add wtbl s (n+1);
      Format.eprintf "@[%a warning: %s@]@." Loc.report_line (fst l) s;
      if n = 2 then Format.eprintf "(this repeated warning will not appear anymore)@.";
      if Coptions.werror then exit 1
    end

