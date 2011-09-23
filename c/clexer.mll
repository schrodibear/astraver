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

(*i $Id: clexer.mll,v 1.29 2009-04-02 11:51:39 melquion Exp $ i*)

(* from http://www.lysator.liu.se/c/ANSI-C-grammar-l.html *)

{

  open Cast
  open Cparser
  open Lexing
  open Cerror
  open Clogic

  let loc lexbuf = (lexeme_start_p lexbuf, lexeme_end_p lexbuf)

  let lex_error lexbuf s =
    Creport.raise_located (loc lexbuf) (AnyMessage ("lexical error: " ^ s))

  let annot_start_pos = ref Lexing.dummy_pos
  let buf = Buffer.create 1024

  let make_annot s =
    let loc = !annot_start_pos in
    match Cllexer.annot (loc, s) with
      | Cast.Adecl d -> DECL d
      | Cast.Aspec s -> SPEC s
      | Cast.Acode_annot a -> CODE_ANNOT a
      | Cast.Aloop_annot a -> LOOP_ANNOT a
	 
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

}

let space = [' ' '\t' '\012' '\r']

let rD =	['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']
let rH = ['a'-'f' 'A'-'F' '0'-'9']
let rE = ['E''e']['+''-']? rD+
let rP = ['P''p']['+''-']? rD+
let rFS = ('f'|'F'|'l'|'L')
let rIS = ('u'|'U'|'l'|'L')*

rule token = parse
  | [' ' '\t' '\012' '\r']+ { token lexbuf }
  | '\n'                    { newline lexbuf; token lexbuf }
  | "/*"                    { comment lexbuf; token lexbuf }
  | "/*@"                   { annot_start_pos := lexeme_start_p lexbuf;
			      Buffer.clear buf; annot lexbuf }
  | "//@" [^ '\n']* '\n'    { annot_start_pos := lexeme_start_p lexbuf;
			      newline lexbuf;
			      let s = lexeme lexbuf in
			      make_annot 
				(String.sub s 3 (String.length s - 4)) }
  | "//" [^ '\n']* '\n'     { newline lexbuf; token lexbuf }
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
  | "__LINE__"              { let n = lexeme_start_p lexbuf in
			      let s = string_of_int n.pos_lnum in
			      CONSTANT (IntConstant s) }
  | "__FILE__"              { let f = (lexeme_start_p lexbuf).pos_fname in
			      STRING_LITERAL ("\"" ^ f ^ "\"") }
  | "__extension__"         { token lexbuf }
  | "__attribute__"         { ATTRIBUTE }
  | "__restrict"            { RESTRICT }
  | "#" [' ' '\t']* (['0'-'9']+ as num) [' ' '\t']*
        ("\"" ([^ '\010' '\013' '"' ] * as name) "\"")?
        [^ '\010' '\013'] * '\n'
      { update_loc lexbuf name (int_of_string num) true 0;
        token lexbuf }
  | '#' [^'\n']* '\n'       { newline lexbuf; token lexbuf }

  | rL (rL | rD)*       { let s = lexeme lexbuf in
			  if Ctypes.mem s then TYPE_NAME s else IDENTIFIER s }

  | '0'['x''X'] rH+ rIS?
  | '0' rD+ rIS?
  | rD+ rIS?
  | 'L'? "'" [^ '\n' '\'']+ "'"
    { CONSTANT (IntConstant (lexeme lexbuf)) }

  | rD+ rE rFS?
  | rD* '.' rD+ (rE)? rFS?
  | rD+ '.' rD* (rE)? rFS?
  | '0' ['x''X'] rH+ '.'? rH* rP rFS?
  | '0' ['x''X'] rH* '.' rH+ rP rFS?
    { CONSTANT (RealConstant (lexeme lexbuf)) }

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
  | '\n' { newline lexbuf; comment lexbuf }
  | _    { comment lexbuf }

and annot = parse
  | "*/" { make_annot (Buffer.contents buf) }
  | eof  { lex_error lexbuf "Unterminated annotation" }
  | '\n' { newline lexbuf; Buffer.add_char buf '\n'; annot lexbuf }
  | _    { Buffer.add_char buf (lexeme_char lexbuf 0); annot lexbuf }

{

  let parse c =
    let lb = from_channel c in
    try
      Cparser.file token lb
    with Parsing.Parse_error ->
      Creport.raise_located (loc lb) (AnyMessage "Syntax error")

}
