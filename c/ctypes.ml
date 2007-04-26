(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: ctypes.ml,v 1.24 2007-04-26 13:41:19 filliatr Exp $ i*)

open Format
open Coptions
open Lib


type storage_class = No_storage | Extern | Auto | Static | Register

type sign = Signed | Unsigned

type cinteger = 
  | Char | Short | Int | Long | LongLong | Bitfield of int64
  | ExactInt

type cfloat = Float | Double | LongDouble | Real

type valid = Valid of int64 * int64 | Not_valid 

type ctype_node =
  | Tvoid
  | Tint of (sign * cinteger)
  | Tfloat of cfloat
  | Tvar of string
  | Tarray of valid * ctype * int64 option
  | Tpointer of valid * ctype
  | Tstruct of string 
  | Tunion of string 
  | Tenum of string 
  | Tfun of ctype list * ctype

and ctype = { 
  ctype_node : ctype_node;
  ctype_storage : storage_class;
  ctype_const : bool;
  ctype_volatile : bool;
  ctype_ghost : bool;
}

let noattr tyn = { ctype_node = tyn; 
		   ctype_storage = No_storage;
		   ctype_const = false;
		   ctype_volatile = false; 
		   ctype_ghost = false;
		 }
let c_void = noattr Tvoid
let c_int = noattr (Tint (Signed, Int))
let c_exact_int = noattr (Tint (Signed, ExactInt))
let c_char = noattr (Tint (Unsigned, Char))
let c_float fk = noattr (Tfloat fk)
let c_string valid = noattr (Tpointer(valid, c_char))
let c_array valid ty = noattr (Tarray (valid,ty,None))
let c_array_size valid ty n = noattr (Tarray (valid,ty,Some n))
let c_pointer valid ty = noattr (Tpointer(valid, ty))
let c_void_star valid = c_pointer valid c_void
let c_real = noattr (Tfloat Real)
let c_addr = noattr (Tvar "addr")


let stack = ref [ref Sset.empty]

let add s = match !stack with
  | m :: _ -> 
      if debug then eprintf "Ctypes.add %s@." s; 
      m := Sset.add s !m
  | [] -> assert false

let _ = add "__builtin_va_list"

let remove s = match !stack with
  | m :: _ -> 
      if debug then eprintf "Ctypes.remove %s@." s; 
      m := Sset.remove s !m
  | [] -> assert false

let mem s = match !stack with
  | m :: _ -> Sset.mem s !m
  | [] -> assert false

let push () = match !stack with
  | (m :: _) as s -> stack := ref !m :: s
  | [] -> assert false

let pop () = match !stack with
  | _ :: s -> stack := s
  | [] -> assert false

let rec ctype fmt ty =
  (if ty.ctype_ghost then fprintf fmt "ghost "else ());
  (if ty.ctype_const then fprintf fmt "const "else ());
  ctype_node fmt ty.ctype_node

and ctype_node fmt = function
  | Tvoid -> fprintf fmt "void"
  | Tint _ -> fprintf fmt "int"
  | Tfloat _ -> fprintf fmt "float"
  | Tvar s -> fprintf fmt "%s" s
  | Tarray (_,ty, None) -> fprintf fmt "%a[]" ctype ty
  | Tarray (_,ty, Some n) -> fprintf fmt "%a[%Ld]" ctype ty n
  | Tpointer (_,ty) -> fprintf fmt "%a*" ctype ty
  | Tstruct s -> fprintf fmt "struct %s" s
  | Tunion s -> fprintf fmt "union %s" s
  | Tenum s -> fprintf fmt "enum %s" s
  | Tfun _ -> fprintf fmt "<fun>"

let is_pointer ty = 
  match ty.ctype_node with
    | Tarray _ | Tpointer _ -> true
    | _ -> false
