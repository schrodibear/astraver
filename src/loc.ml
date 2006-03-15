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

(*i $Id: loc.ml,v 1.16 2006-03-15 08:57:08 filliatr Exp $ i*)

let join (b,_) (_,e) = (b,e)

(*s Error locations. *)

let finally ff f x =
  let y = try f x with e -> ff (); raise e in ff (); y

(***
let linenum f b =
  let cin = open_in f in
  let rec lookup n l cl =
    if n = b then 
      (l,cl)
    else 
      let c = input_char cin in
      lookup (succ n) (if c == '\n' then succ l else l) 
	(if c == '\n' then 0 else succ cl)
  in
  try let r = lookup 0 1 0 in close_in cin; r with e -> close_in cin; raise e

let safe_linenum f b = try linenum f b with _ -> (1,1)
***)

open Format
open Lexing

(*s Line number *)

let report_line fmt l = fprintf fmt "%s:%d:" l.pos_fname l.pos_lnum

(* Lexing positions *)

type position = Lexing.position * Lexing.position

exception Located of position * exn

let dummy_position = Lexing.dummy_pos, Lexing.dummy_pos

let gen_report_position fmt (b,e) = 
  fprintf fmt "File \"%s\", " b.pos_fname;
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  fprintf fmt "line %d, characters %d-%d" l fc lc

let report_position fmt pos = fprintf fmt "%a:@\n" gen_report_position pos

let string =
  let buf = Buffer.create 1024 in
  fun loc ->
    let fmt = Format.formatter_of_buffer buf in
    Format.fprintf fmt "%a@?" gen_report_position loc;
    let s = Buffer.contents buf in
    Buffer.reset buf;
    s

let report_obligation_position fmt (b,e) =
  fprintf fmt "Why obligation from file \"%s\", " b.pos_fname;
  let l = b.pos_lnum in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  fprintf fmt "line %d, characters %d-%d:" l fc lc
  
let current_offset = ref 0
let reloc p = { p with pos_cnum = p.pos_cnum + !current_offset }

(* Identifiers localization *)

let ident_t = Hashtbl.create 97
let add_ident = Hashtbl.add ident_t
let ident = Hashtbl.find ident_t
