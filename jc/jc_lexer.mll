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

(*i $Id: jc_lexer.mll,v 1.38 2007-07-28 11:15:59 nrousset Exp $ i*)

{
  open Jc_ast
  open Jc_parser
  open Lexing

  type location = Lexing.position * Lexing.position

  let loc lexbuf : location = (lexeme_start_p lexbuf, lexeme_end_p lexbuf)

  exception Lexical_error of location * string
  exception Syntax_error of location

  let lex_error lexbuf s =
    raise (Lexical_error(loc lexbuf,s))

  let buf = Buffer.create 1024

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  (* Update the current location with file name and line number. *)

  let update_loc lexbuf file line absolute chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with
      | None -> pos.pos_fname
      | Some s -> s
    in
    lexbuf.lex_curr_p <- 
      { pos with
	  pos_fname = new_file;
	  pos_lnum = if absolute then line else pos.pos_lnum + line;
	  pos_bol = pos.pos_cnum - chars;
      }


  exception Dotdot of string

}

let space = [' ' '\t' '\012' '\r']

let rD =	['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rFS	= ('f'|'F'|'l'|'L')
let rIS = ('u'|'U'|'l'|'L')*

rule token = parse
  | [' ' '\t' '\012' '\r']+ { token lexbuf }
  | '\n'                    { newline lexbuf; token lexbuf }
  | "/*"                    { comment lexbuf; token lexbuf }
  | "//" [^ '\n']* '\n'     { newline lexbuf; token lexbuf }
  | "and"                   { AND }
  | "assert"                { ASSERT }
  | "assigns"               { ASSIGNS }
  | "assumes"               { ASSUMES }
  | "axiom"                 { AXIOM }
  | "behavior"              { BEHAVIOR }
  | "boolean"               { BOOLEAN }
  | "break"                 { BREAK }
  | "case"                  { CASE }
  | "default"               { DEFAULT }
  | "catch"                 { CATCH }
  | "continue"              { CONTINUE }
  | "do"                    { DO }
(*
  | "double"                { DOUBLE }
*)
  | "else"                  { ELSE }
  | "ensures"               { ENSURES }
(*
  | "enum"                  { ENUM }
*)
  | "exception"             { EXCEPTION }
  | "false"                 { CONSTANT (JCCboolean false) }
(*
  | "float"                 { FLOAT }
*)
  | "for"                   { FOR }
  | "free"                  { FREE }
  | "goto"                  { GOTO }
  | "if"                    { IF }
  | "integer"               { INTEGER }
  | "invariant"             { INVARIANT }
  | "logic"                 { LOGIC }
  | "new"                   { NEW }
  | "null"                  { NULL }
  | "of"                    { OF }
  | "pack"                  { PACK }
  | "reads"                 { READS }
  | "real"                  { REAL}
  | "rep"                   { REP }
  | "requires"              { REQUIRES }
  | "return"                { RETURN }
  | "switch"                { SWITCH }
  | "throw"                 { THROW }
  | "throws"                { THROWS }
  | "true"                  { CONSTANT (JCCboolean true) }
  | "try"                   { TRY }
  | "type"                  { TYPE }
  | "unit"                  { UNIT }
  | "unpack"                { UNPACK }
  | "variant"               { VARIANT }
  | "while"                 { WHILE }
  | "with"                  { WITH }
  | "\\bottom"              { BSBOTTOM }
  | "\\forall"              { BSFORALL }
  | "\\exists"              { BSEXISTS }
  | "\\mutable"             { BSMUTABLE }
  | "\\nothing"             { BSNOTHING }
  | "\\offset_max"          { BSOFFSET_MAX }
  | "\\offset_min"          { BSOFFSET_MIN }
  | "\\old"                 { BSOLD }
  | "\\result"              { BSRESULT }
  | "\\typeeq"              { BSTYPEEQ }
  | "\\typeof"              { BSTYPEOF }
  | "\\" rL*                { lex_error lexbuf ("Illegal escape sequence " ^ lexeme lexbuf) }

  | "#" [' ' '\t']* (['0'-'9']+ as num) [' ' '\t']*
        ("\"" ([^ '\010' '\013' '"' ] * as name) "\"")?
        [^ '\010' '\013'] * '\n'
      { update_loc lexbuf name (int_of_string num) true 0;
        token lexbuf }
  | '#' [^'\n']* '\n'       { newline lexbuf; token lexbuf }

  | rL (rL | rD)*       { let s = lexeme lexbuf in IDENTIFIER s }

  | '0'['x''X'] rH+ rIS?    { CONSTANT (JCCinteger (lexeme lexbuf)) }
  | '0' rD+ rIS?            { CONSTANT (JCCinteger (lexeme lexbuf)) }
  | rD+ rIS?                { CONSTANT (JCCinteger (lexeme lexbuf)) }
  | 'L'? "'" [^ '\n' '\'']+ "'"     { CONSTANT (JCCinteger (lexeme lexbuf)) }

  | rD+ rE rFS?             { CONSTANT (JCCreal (lexeme lexbuf)) }
  | rD* "." rD+ (rE)? rFS?  { CONSTANT (JCCreal (lexeme lexbuf)) }
  | rD+ "." rD* (rE)? rFS?  { CONSTANT (JCCreal (lexeme lexbuf)) }

      (* trick to deal with intervals like 0..10 *)

  | (rD+ as n) ".."         { raise (Dotdot n) }

      (* character constants *)

  | 'L'? '"' [^ '"']* '"'     { STRING_LITERAL (lexeme lexbuf) }

(*
  | ">>="                   { RIGHT_ASSIGN }
  | "<<="                   { LEFT_ASSIGN }
*)
  | "+="                    { PLUSEQ }
  | "-="                    { MINUSEQ }
  | "*="                    { STAREQ }
  | "/="                    { SLASHEQ }
  | "%="                    { PERCENTEQ }
(*
  | "&="                    { AND_ASSIGN }
  | "^="                    { XOR_ASSIGN }
  | "|="                    { OR_ASSIGN }
*)
  | ">>"                    { RSHIFT }
  | "<<"                    { LSHIFT }
  | "++"                    { PLUSPLUS }
  | "--"                    { MINUSMINUS }
  | "&&"                    { AMPAMP }
  | "||"                    { BARBAR }
  | "==>"                   { EQEQGT }
  | "<==>"                  { LTEQEQGT }
  | "<="                    { LTEQ }
  | ">="                    { GTEQ }
  | "=="                    { EQEQ }
  | "!="                    { BANGEQ }
  | ";"                     { SEMICOLON }
  | "{"                     { LBRACE }
  | "}"                     { RBRACE }
  | ","                     { COMMA }
  | ":"                     { COLON }
  | "="                     { EQ }
  | "()"                    { LPARRPAR }
  | "("                     { LPAR }
  | ")"                     { RPAR }
  | "["                     { LSQUARE }
  | "]"                     { RSQUARE }
  | "."                     { DOT }
  | ".."                    { DOTDOT }
  | "<:"                    { LTCOLON } 
  | ":>"                    { COLONGT } 
  | "&"                     { AMP }
  | "!"                     { EXCLAM }
  | "~"                     { TILDE }
  | "-"                     { MINUS }
  | "+"                     { PLUS }
  | "*"                     { STAR }
  | "/"                     { SLASH }
  | "%"                     { PERCENT }
  | "<"                     { LT }
  | ">"                     { GT }
  | "^"                     { HAT }
  | "|"                     { PIPE }
  | "?"                     { QUESTION }
  | eof { EOF }
  | '"' { lex_error lexbuf "unterminated string" }
  | _   { lex_error lexbuf ("illegal character " ^ lexeme lexbuf) }

and comment = parse
  | "*/" { () }
  | "/*" { comment lexbuf ; comment lexbuf }
  | eof  { lex_error lexbuf "unterminated comment" }
  | '\n' { newline lexbuf; comment lexbuf }
  | _    { comment lexbuf }
      
{

let dotdot_mem = ref false
 
let next_token lexbuf =
  if !dotdot_mem then
    begin
      dotdot_mem := false;
      DOTDOT
    end
  else
    begin
      try
	token lexbuf
      with
	Dotdot(n) ->
	  dotdot_mem := true;
	  CONSTANT(JCCinteger n)
    end

  let parse f c =
    let lb = from_channel c in
    lb.lex_curr_p <- { lb.lex_curr_p with pos_fname = f };
    try
      Jc_parser.file next_token lb
    with Parsing.Parse_error ->
      Jc_options.parsing_error (loc lb) ""
	
}


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
