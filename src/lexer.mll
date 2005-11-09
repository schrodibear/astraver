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

(* $Id: lexer.mll,v 1.3 2005-11-09 07:27:41 filliatr Exp $ *)

{
  open Lexing
  open Parser

  let keywords = Hashtbl.create 97
  let () = 
    List.iter 
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "absurd", ABSURD;
	"and", AND;
        "array", ARRAY;
	"as", AS;
	"assert", ASSERT;
	"axiom", AXIOM;
	"begin", BEGIN;
        "bool", BOOL;
	"do", DO;
	"done", DONE;
        "else", ELSE;
	"end", END;
	"exception", EXCEPTION; 
	"exists", EXISTS;
	"external", EXTERNAL;
        "false", FALSE;
	"for", FOR;
	"forall", FORALL;
	"fun", FUN;
	"function", FUNCTION;
	"goal", GOAL;
	"if", IF;
	"in", IN;
	"int", INT;
	"invariant", INVARIANT;
	"label", LABEL;
	"let", LET;
	"logic", LOGIC;
	"not", NOT;
	"of", OF;
	"or", OR;
	"parameter", PARAMETER;
	"predicate", PREDICATE;
	"prop", PROP;
	"raise", RAISE;
	"raises", RAISES;
	"reads", READS;
	"real", REAL;
	"rec", REC;
	"ref", REF;
	"returns", RETURNS;
	"then", THEN;
	"true", TRUE;
	"try", TRY;
	"type", TYPE;
	"unit", UNIT;
	"variant", VARIANT;
	"void", VOID;
	"while", WHILE;
	"with", WITH;
        "writes", WRITES ]
	       
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- 
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_buf = Buffer.create 1024

  exception Lexical_error of string

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c
}

let newline = '\n'
let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z']
let letter = alpha | '_'
let digit = ['0'-'9']
let ident = letter (letter | digit | '\'')*
let float = digit+ '.' digit* | digit* '.' digit+

rule token = parse
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | ident as id  
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | digit+ as s
      { INTEGER s }
  | float as s
      { FLOAT s }
  | "(*"
      { comment lexbuf; token lexbuf }
  | "'"
      { QUOTE }
  | ","
      { COMMA }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | "!"
      { BANG }
  | ":"
      { COLON }
  | ";"
      { SEMICOLON }
  | ":="
      { COLONEQUAL }
  | "->"
      { ARROW }
  | "<->"
      { LRARROW }
  | "="
      { EQUAL }
  | "<"
      { LT }
  | "<="
      { LE }
  | ">"
      { GT }
  | ">="
      { GE }
  | "<>"
      { NOTEQ }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | "*"
      { TIMES }
  | "/"
      { SLASH }
  | "%"
      { PERCENT }
  | "@"
      { AT }
  | "."
      { DOT }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "{"
      { LEFTB }
  | "}"
      { RIGHTB }
  | "{{"
      { LEFTBLEFTB }
  | "}}"
      { RIGHTBRIGHTB }
  | "|"
      { BAR }
  | "||"
      { BARBAR }
  | "&&" 
      { AMPAMP }
  | "=>"
      { BIGARROW }
  | "\""
      { Buffer.clear string_buf; string lexbuf }
  | eof 
      { EOF }
  | _ as c
      { raise (Lexical_error ("illegal character: " ^ String.make 1 c)) }

and comment = parse
  | "*)" 
      { () }
  | "(*" 
      { comment lexbuf; comment lexbuf }
  | newline 
      { newline lexbuf; comment lexbuf }
  | eof
      { raise (Lexical_error "unterminated comment") }
  | _ 
      { comment lexbuf }

and string = parse
  | "\""
      { STRING (Buffer.contents string_buf) }
  | "\\" (_ as c)
      { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline 
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      { raise (Lexical_error "unterminated string") }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }



{

  let loc lb = (lexeme_start_p lb, lexeme_end_p lb)

  let with_location f lb =
    try f lb with e -> raise (Misc.Located (loc lb, e))

  let parse_lexpr = with_location (lexpr token)
  let parse_file = with_location (file token)

  let lexpr_of_string s = parse_lexpr (from_string s)
}
