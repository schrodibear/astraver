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

(*i $Id: cllexer.mll,v 1.26 2004-07-21 08:07:08 filliatr Exp $ i*)

(* tokens for the C annotations *)

{

  open Clparser
  open Lexing
  open Cerror

  let loc lexbuf = (lexeme_start lexbuf, lexeme_end lexbuf)

  let lex_error lexbuf s =
    Creport.raise_located (loc lexbuf) (AnyMessage ("lexical error: " ^ s))

}

let space = [' ' '\t' '\012' '\r']

let rD =	['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rFS	= ('f'|'F'|'l'|'L')
let rIS = ('u'|'U'|'l'|'L')*

rule token = parse
  | '@' | [' ' '\t' '\012' '\r' '\n']+ { token lexbuf }
  | "(*"                    { comment lexbuf; token lexbuf }

  | "\\forall"  { FORALL }
  | "\\exists"  { EXISTS }
  | "=>" { IMPLIES }
  | "<=>" { IFF }
  | "&"     { AMP }
  | "&&"     { AND }
  | "||"      { OR }
  | "!"     { NOT }
  | "\\true"    { TRUE }
  | "\\false"   { FALSE }
  | "\\old"    { OLD }
  | "\\at"    { AT }
  | "\\result" { RESULT }
  | "\\base_addr" { BASE_ADDR }
  | "\\block_length" { BLOCK_LENGTH }
  | "\\valid" { VALID }
  | "\\fresh" { FRESH }
  | "\\valid_index" { VALID_INDEX }
  | "\\valid_range" { VALID_RANGE }
  | "if"                    { IF }
  | "then"                  { THEN }
  | "else"                  { ELSE }
  | "invariant" { INVARIANT }
  | "variant"   { VARIANT }
  | "decreases"   { DECREASES }
  | "for"       { FOR }
  | "assert"    { ASSERT }
  | "label"     { LABEL }
  | "requires"       { REQUIRES }
  | "ensures"      { ENSURES } 
  | "assigns"     { ASSIGNS }
  | "loop_assigns"     { LOOP_ASSIGNS }
  | "\\nothing"   { NOTHING }
  | "reads"      { READS }
  | "logic"    { LOGIC }
  | "predicate"    { PREDICATE }
  | "axiom"    { AXIOM }
  | "int" { INT }
  | "float" { FLOAT }
  | "\\null" { NULL }

  | rL (rL | rD)*       { let s = lexeme lexbuf in IDENTIFIER s }

  | '0'['x''X'] rH+ rIS?    { CONSTANT (lexeme lexbuf)}
  | '0' rD+ rIS?            { CONSTANT (lexeme lexbuf) }
  | rD+ rIS?                { CONSTANT (lexeme lexbuf) }
  | 'L'? "'" [^ '\n' '\'']+ "'"     { CONSTANT (lexeme lexbuf) }

  | rD+ rE rFS?             { CONSTANT (lexeme lexbuf) }
  | rD* "." rD+ (rE)? rFS?  { CONSTANT (lexeme lexbuf) }
  | rD+ "." rD* (rE)? rFS?  { CONSTANT (lexeme lexbuf) }
  | 'L'? '"' [^ '"']* '"'   { STRING_LITERAL (lexeme lexbuf) }

  | "@"                     { AT }
  | ","                     { COMMA }
  | "->"                    { ARROW }
  | "?"                     { QUESTION }
  | ";"                     { SEMICOLON }
  | ":"                     { COLON }
  | "."                     { DOT }
  | ".."                    { DOTDOT }
  | "-"                     { MINUS }
  | "+"                     { PLUS }
  | "*"                     { STAR }
  | "&"                     { AMP }
  | "/"                     { SLASH }
  | "%"                     { PERCENT }
  | "<"                     { LT }
  | ">"                     { GT }
  | "<="                    { LE }
  | ">="                    { GE }
  | "=="                    { EQ }
  | "!="                    { NE }
  | "("                     { LPAR }
  | ")"                     { RPAR }
  | "{"                     { LBRACE }
  | "}"                     { RBRACE }
  | ("["|"<:")              { LSQUARE }
  | ("]"|":>")              { RSQUARE }

  | eof { EOF }
  | '\\' rL (rL | rD)* 
    { lex_error lexbuf ("Illegal escape sequence " ^ lexeme lexbuf) }
  | _   { lex_error lexbuf ("Illegal character " ^ lexeme lexbuf) }
 
and comment = parse
  | "*)" { () }
  | "(*" { comment lexbuf; comment lexbuf }
  | eof  { lex_error lexbuf "Unterminated_comment" }
  | _    { comment lexbuf }


{

  let parse_with_offset f (ofs, s) =
    let lb = from_string s in
    try
      f token lb
    with 
      | Parsing.Parse_error as e -> 
	  let loc = ofs + lexeme_start lb, ofs + lexeme_end lb in
	  Creport.raise_located loc (AnyMessage "Syntax error")
      | Stdpp.Exc_located (loc, e) -> 
	  raise (Stdpp.Exc_located (Compat.offset ofs loc, e))

  let annot = parse_with_offset Clparser.annot

}
