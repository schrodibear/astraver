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

(*i $Id: clexer.mll,v 1.17 2004-09-23 08:40:27 filliatr Exp $ i*)

(* from http://www.lysator.liu.se/c/ANSI-C-grammar-l.html *)

{

  open Cast
  open Cparser
  open Lexing
  open Cerror

  let loc lexbuf = (lexeme_start lexbuf, lexeme_end lexbuf)

  let lex_error lexbuf s =
    Creport.raise_located (loc lexbuf) (AnyMessage ("lexical error: " ^ s))

  let annot_start_pos = ref 0
  let buf = Buffer.create 1024

  let make_annot s =
    let loc = !annot_start_pos in
    match Cllexer.annot (loc, s) with
      | Cast.Adecl d -> DECL (loc, d)
      | Cast.Aspec s -> SPEC (loc, s)
      | Cast.Acode_annot a -> CODE_ANNOT (loc, a)
      | Cast.Aloop_annot a -> LOOP_ANNOT (loc, a)
	 
}

let space = [' ' '\t' '\012' '\r']

let rD =	['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rFS	= ('f'|'F'|'l'|'L')
let rIS = ('u'|'U'|'l'|'L')*

rule token = parse
  | [' ' '\t' '\012' '\r' '\n']+        
                            { token lexbuf }
  | "/*"                    { comment lexbuf; token lexbuf }
  | "/*@"                   { annot_start_pos := lexeme_start lexbuf + 4;
			      Buffer.clear buf; annot lexbuf }
  | "//@" [^ '\n']* '\n'    { annot_start_pos := lexeme_start lexbuf + 4;
			      let s = lexeme lexbuf in
			      make_annot 
				(String.sub s 3 (String.length s - 4)) }
  | "//" [^ '\n']* '\n'     { token lexbuf }
  | "auto"                  { AUTO }
  | "break"                 { BREAK }
  | "case"                  { CASE }
  | "char"                  { CHAR }
  | "__const" | "const"     { CONST }
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

  (* preprocessor, compiler-dependent extensions, etc. *)
  | "__LINE__"              { let n = lexeme_start lexbuf in
			      let s = string_of_int (Loc.line n) in
			      CONSTANT (IntConstant s) }
  | "__FILE__"              { let f = Loc.get_file () in
			      STRING_LITERAL ("\"" ^ f ^ "\"") }
  | "__extension__"         { token lexbuf }
  | "__attribute__"         { ATTRIBUTE }
  | "__restrict"            { RESTRICT }
  (* we skip # line directives *)
  | '#' [^'\n']* '\n'       { token lexbuf }

  | rL (rL | rD)*       { let s = lexeme lexbuf in
			  if Ctypes.mem s then TYPE_NAME s else IDENTIFIER s }

  | '0'['x''X'] rH+ rIS?    { CONSTANT (IntConstant (lexeme lexbuf)) }
  | '0' rD+ rIS?            { CONSTANT (IntConstant (lexeme lexbuf)) }
  | rD+ rIS?                { CONSTANT (IntConstant (lexeme lexbuf)) }
  | 'L'? "'" [^ '\n' '\'']+ "'"     { CONSTANT (IntConstant (lexeme lexbuf)) }

  | rD+ rE rFS?             { CONSTANT (IntConstant (lexeme lexbuf)) }
  | rD* "." rD+ (rE)? rFS?  { CONSTANT (FloatConstant (lexeme lexbuf)) }
  | rD+ "." rD* (rE)? rFS?  { CONSTANT (FloatConstant (lexeme lexbuf)) }

  | 'L'? '"' [^ '"']* '"'     { STRING_LITERAL (lexeme lexbuf) }

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
  | ("["|"<:")              { LSQUARE }
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
  | eof  { lex_error lexbuf "Unterminated_comment" }
  | _    { comment lexbuf }

and annot = parse
  | "*/" { make_annot (Buffer.contents buf) }
  | eof  { lex_error lexbuf "Unterminated annotation" }
  | _    { Buffer.add_char buf (lexeme_char lexbuf 0); annot lexbuf }

{

  let parse c =
    let lb = from_channel c in
    try
      Cparser.file token lb
    with Parsing.Parse_error as e ->
      Creport.raise_located (loc lb) (AnyMessage "Syntax error")

}
