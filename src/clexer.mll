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

(* from http://www.lysator.liu.se/c/ANSI-C-grammar-l.html *)

{

  open Cparser
  open Lexing

  let loc lexbuf = (lexeme_start lexbuf, lexeme_end lexbuf)

  let lex_error lexbuf s =
    raise (Stdpp.Exc_located (loc lexbuf, Stream.Error s))

  let buf = Buffer.create 1024

}

let rD =	['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rFS	= ('f'|'F'|'l'|'L')
let rIS = ('u'|'U'|'l'|'L')*

rule token = parse
  | [' ' '\t' '\n']+        { token lexbuf }
  | "/*"                    { comment lexbuf; token lexbuf }
  | "/*@"                   { Buffer.clear buf; annot lexbuf }

  | "auto"                  { AUTO }
  | "break"                 { BREAK }
  | "case"                  { CASE }
  | "char"                  { CHAR }
  | "const"                 { CONST }
  | "continue"              { CONTINUE }
  | "default"               { DEFAULT }
  | "do"                    { DO }
  | "double"                { DOUBLE }
  | "else"                  { ELSE }
  | "enum"                  { ENUM }
  | "extern"                { EXTERN }
  | "float"                 { FLOAT }
  | "for"                   { FOR }
  | "goto"                  { GOTO }
  | "if"                    { IF }
  | "int"                   { INT }
  | "long"                  { LONG }
  | "register"              { REGISTER }
  | "return"                { RETURN }
  | "short"                 { SHORT }
  | "signed"                { SIGNED }
  | "sizeof"                { SIZEOF }
  | "static"                { STATIC }
  | "struct"                { STRUCT }
  | "switch"                { SWITCH }
  | "typedef"               { TYPEDEF }
  | "union"                 { UNION }
  | "unsigned"              { UNSIGNED }
  | "void"                  { VOID }
  | "volatile"              { VOLATILE }
  | "while"                 { WHILE }

  | rL (rL | rD)*           { IDENTIFIER (lexeme lexbuf) }

  | '0'['x''X'] rH+ rIS?    { CONSTANT (lexeme lexbuf)}
  | '0' rD+ rIS?            { CONSTANT (lexeme lexbuf) }
  | rD+ rIS?                { CONSTANT (lexeme lexbuf) }
  | 'L'? "'" (_|[^'\\''\''])+ "'"     { CONSTANT (lexeme lexbuf) }

  | rD+ rE rFS?             { CONSTANT (lexeme lexbuf) }
  | rD* "." rD+ (rE)? rFS?  { CONSTANT (lexeme lexbuf) }
  | rD+ "." rD* (rE)? rFS?  { CONSTANT (lexeme lexbuf) }

  | 'L'? '"' (_|[^'\\''"'])* '"'     { STRING_LITERAL (lexeme lexbuf) }

  | "..."                   { ELLIPSIS }
  | ">>="                   { RIGHT_ASSIGN }
  | "<<="                   { LEFT_ASSIGN }
  | "+="                    { ADD_ASSIGN }
  | "-="                    { SUB_ASSIGN }
  | "*="                    { MUL_ASSIGN }
  | "/="                    { DIV_ASSIGN }
  | "%="                    { MOD_ASSIGN }
  | "&="                    { AND_ASSIGN }
  | "^="                    { XOR_ASSIGN }
  | "|="                    { OR_ASSIGN }
  | ">>"                    { RIGHT_OP }
  | "<<"                    { LEFT_OP }
  | "++"                    { INC_OP }
  | "--"                    { DEC_OP }
  | "->"                    { PTR_OP }
  | "&&"                    { AND_OP }
  | "||"                    { OR_OP }
  | "<="                    { LE_OP }
  | ">="                    { GE_OP }
  | "=="                    { EQ_OP }
  | "!="                    { NE_OP }
  | ";"                     { SEMICOLON }
  | ("{"|"<%")              { LBRACE }
  | ("}"|"%>")              { RBRACE }
  | ","                     { COMMA }
  | ":"                     { COLON }
  | "="                     { EQUAL }
  | "("                     { LPAR }
  | ")"                     { RPAR }
  | ("["|"<:")              { RSQUARE }
  | ("]"|":>")              { RSQUARE }
  | "."                     { DOT }
  | "&"                     { AMP }
  | "!"                     { EXL }
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
  | '"' { lex_error lexbuf "Unterminated string" }
  | _   { lex_error lexbuf ("Illegal_character " ^ lexeme lexbuf) }

and comment = parse
  | "*/" { () }
  | _    { comment lexbuf }
  | eof  { lex_error lexbuf "Unterminated_comment" }

and annot = parse
  | "*/" { ANNOT (Buffer.contents buf) }
  | eof  { lex_error lexbuf "Unterminated annotation" }
  | _    { Buffer.add_char buf (lexeme_char lexbuf 0); annot lexbuf }

{

  let parse c =
    let lb = from_channel c in
    try
      Cparser.file token lb
    with Parsing.Parse_error as e ->
      raise (Stdpp.Exc_located (loc lb, e))
}
