(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
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

(*i $Id: simplify_lexer.mll,v 1.1 2006-11-16 15:03:12 filliatr Exp $ i*)

{

  open Lexing 
  open Simplify_ast

  let atoms = Hashtbl.create 1021
  let () = 
    List.iter (fun (s,a) -> Hashtbl.add atoms s a)
      [
    "DEFPRED", Defpred;
    "BG_PUSH", Bg_push;
    "@true", True;
    "AND", And;
    "IMPLIES", Implies;
    "IFF", Iff;
    "FORALL", Forall;
    "MPAT", Mpat;
    "PATS", Pats;
    "AND", And;
    "OR", Or;
    "LBLPOS", Lblpos;
    "LBLNEG", Lblneg;
    "DISTINCT", Distinct;
    "EQ", Eq;
    "NEQ", Neq;
      ]

  type token = LPAR | RPAR | ATOM of atom | EOF

  let mk_ident s =
    let is_char_ok i = function
      | 'a'..'z' | 'A'..'Z' | '_' -> true
      | '0'..'9' when i > 0 -> true
      | _ -> false
    in
    for i = 0 to String.length s - 1 do
      if not (is_char_ok i s.[i]) then s.[i] <- 'a'
    done;
    if Hashtbl.mem atoms s then begin
      let rec loop n = 
	let sn = s ^ string_of_int n in
	if Hashtbl.mem atoms sn then loop (n+1) else sn
      in
      loop 0
    end else
      s

  let atom s =
    try
      Hashtbl.find atoms s
    with Not_found ->
      let s' = mk_ident (String.copy s) in
      Format.eprintf "atom %s -> %s@." s s';
      let a = Ident s' in 
      Hashtbl.add atoms s a; a

}

let space = [' ' '\t' '\n' '\r']
let ident = ['a'-'z' 'A'-'Z']+

rule token = parse
  | space+
      { token lexbuf }
  | ";" [^'\n']* '\n' 
      { token lexbuf }
  | "(" 
      { LPAR }
  | ")" 
      { RPAR }
  | eof 
      { EOF }
  | '|' ([^ '|']+ as s) '|'
      { ATOM (atom s) }
  | [^' ' '\t' '\n' '\r' ';' '(' ')']+ as s
      { ATOM (atom s) }
  | _ as c 
      { Format.eprintf  "simplify_lexer: illegal character %c@." c; exit 1 }

{

  let () =
    let lb = from_channel stdin in
    try while true do token lb done with End_of_file -> ()

}

