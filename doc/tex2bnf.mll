(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                  *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
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

(* $Id: tex2bnf.mll,v 1.3 2008-11-05 14:03:14 filliatr Exp $ *)

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
