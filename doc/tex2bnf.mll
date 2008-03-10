(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
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

(* $Id: tex2bnf.mll,v 1.1 2008-02-05 12:35:59 marche Exp $ *)

{ open Lexing;; }

rule main = parse
    "\\begin{syntax}" {
      print_string "\\begin{syntax}";
      syntax lexbuf }
  | "\\@" {
      print_string "@";
      main lexbuf }
  | _ {
      print_char (lexeme_char lexbuf 0); main lexbuf }
  | eof {
      () }

and syntax = parse
    "\\end{syntax}" {
      print_string "\\end{syntax}";
      main lexbuf }
  | ";" ([^ '\n']* as s) '\n' [' ''\t']* '|' {
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\alt{}";
      syntax lexbuf }
  | ";" ([^ '\n']* as s) '\n' {
      print_string "& \\textrm{";
      print_string s;
      print_string "} \\newl{}";
      syntax lexbuf }
  | "@" {
      print_string "}";
      main lexbuf }
  | '\'' {
      print_string "\\term{";
      inquote lexbuf }
  | '"' {
      print_string "\\term{";
      indoublequote lexbuf }
  | "below" { print_string "\\below"; syntax lexbuf }
  | "epsilon" { print_string "\\emptystring"; syntax lexbuf }
  | ['A'-'Z''a'-'z''-'] + {
      print_string "\\nonterm{";
      print_string (lexeme lexbuf);
      print_string"}";
      syntax lexbuf }
  | '\\' ['a'-'z''A'-'Z'] + {
      print_string (lexeme lexbuf);
      syntax lexbuf }
  | ['_' '^'] _ {
      print_string (lexeme lexbuf);
      syntax lexbuf }
  | "*" { print_string "\\repetstar{}"; syntax lexbuf }
  | "+" { print_string "\\repetplus{}"; syntax lexbuf }
  | "?" { print_string "\\repetone{}"; syntax lexbuf }
  | "(" { print_string "\\lparen{}"; syntax lexbuf }
  | ")" { print_string "\\rparen{}"; syntax lexbuf }
  | "::=" { print_string "\\is{}"; syntax lexbuf }
  | "|" { print_string "\\orelse{}"; syntax lexbuf }
  | "\\" { print_string "\\sep{}"; syntax lexbuf }
  | "{" { print_string "\\notimplemented"; check_rq lexbuf }
  | "}" { print_string "}"; syntax lexbuf }
  | _ {
      print_char (lexeme_char lexbuf 0);
      syntax lexbuf }

and inquote = parse
    ['A'-'Z' 'a'-'z' '0'-'9'] {
      print_char (lexeme_char lexbuf 0);
      inquote lexbuf }
  | '\'' {
      print_string "}";
      syntax lexbuf }
  | _ {
      print_string "\\char";
      print_int (int_of_char (lexeme_char lexbuf 0));
      inquote lexbuf }

and indoublequote = parse
    ['A'-'Z' 'a'-'z' '0'-'9'] {
      print_char (lexeme_char lexbuf 0);
      indoublequote lexbuf }
  | '"' {
      print_string "}";
      syntax lexbuf }
  | _ {
      print_string "\\char";
      print_int (int_of_char (lexeme_char lexbuf 0));
      indoublequote lexbuf }
and check_rq = parse
  | "[" { print_string "["; inbrack lexbuf }
  | "" { print_string "{"; syntax lexbuf }
and inbrack = parse
    "]" { print_string "]{"; syntax lexbuf }
  | _  { print_char (lexeme_char lexbuf 0);
           inbrack lexbuf }

{

let run () =
  let lexbuf = Lexing.from_channel stdin in
  print_string "% automatically generated DO NOT EDIT\n";
  main lexbuf; flush stdout; exit 0

let _ = Printexc.print run ()

}