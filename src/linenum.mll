(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: linenum.mll,v 1.9 2008-11-05 14:03:17 filliatr Exp $ i*)

(* code from Ocaml sources *)

{

  open Lexing

  let bol = ref 0 (* beginning of line, in chars *)
  let line = ref 1 (* current line number *)
  let file = ref ""

}

rule one_line = parse
  | '#' [' ' '\t']* (['0'-'9']+ as l) [' ' '\t']*
    ("\"" ([^ '\n' '\r' '"' (* '"' *) ]* as f) "\"")?
    [^ '\n' '\r']* ('\n' | '\r' | "\r\n")
      { line := int_of_string l;
	begin match f with Some f -> file := f | None -> () end;
	bol := lexeme_start lexbuf;
	lexeme_end lexbuf }
  | [^ '\n' '\r']*
    ('\n' | '\r' | "\r\n")
      { incr line;
        bol := lexeme_start lexbuf;
        lexeme_end lexbuf }
  | [^ '\n' '\r'] * eof
      { incr line;
        bol := lexeme_start lexbuf;
        raise End_of_file }

{

  let from_char f c =
    let cin = open_in_bin f in
    let lb = from_channel cin in
    file := f;
    line := 1;
    bol := 0;
    begin try while one_line lb <= c do () done with End_of_file -> () end;
    close_in cin;
    (!file, !line - 1, c - !bol)

}
