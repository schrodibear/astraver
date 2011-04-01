(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
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

(* $Id: lexer.mll,v 1.24 2009-11-26 16:07:54 andrei Exp $ *)

{
  open Lexing
  open Logic
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
        "check", CHECK;
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
	"include", INCLUDE;
	"inductive", INDUCTIVE;
	"int", INT;
	"invariant", INVARIANT;
        "lemma", LEMMA;
	"let", LET;
	"logic", LOGIC;
	"match", MATCH;
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

  let update_loc lexbuf file line chars =
    let pos = lexbuf.lex_curr_p in
    let new_file = match file with None -> pos.pos_fname | Some s -> s in
    lexbuf.lex_curr_p <- 
      { pos with
	  pos_fname = new_file;
	  pos_lnum = int_of_string line;
	  pos_bol = pos.pos_cnum - int_of_string chars;
      }

  let remove_leading_plus s =
    let n = String.length s in 
    if n > 0 && s.[0] = '+' then String.sub s 1 (n-1) else s

  let option_app f = function None -> None | Some x -> Some (f x)

}

let newline = '\n'
let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z']
let letter = alpha | '_'
let digit = ['0'-'9']
let ident = letter (letter | digit | '\'')*
let hexadigit = ['0'-'9' 'a'-'f' 'A'-'F']
(*
let hexafloat = '0' ['x' 'X'] (hexadigit* '.' hexadigit+ | hexadigit+ '.' hexadigit* ) ['p' 'P'] ['-' '+']? digit+
  *)

rule token = parse
  | "#" space* ("\"" ([^ '\010' '\013' '"' ]* as file) "\"")?
    space* (digit+ as line) space* (digit+ as char) space* "#"
      { update_loc lexbuf file line char; token lexbuf }
  | newline 
      { newline lexbuf; token lexbuf }
  | space+  
      { token lexbuf }
  | ident as id  
      { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | digit+ as s
      { INTEGER s }
  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? digit+ as e)
  | (digit+ as i) '.' (digit* as f) (['e' 'E'] (['-' '+']? digit+ as e))?
  | (digit* as i) '.' (digit+ as f) (['e' 'E'] (['-' '+']? digit+ as e))?
      { FLOAT (RConstDecimal (i, f, option_app remove_leading_plus e)) }
  | '0' ['x' 'X'] ((hexadigit* as i) '.' (hexadigit+ as f) 
                  |(hexadigit+ as i) '.' (hexadigit* as f)
		  |(hexadigit+ as i) ("" as f))
    ['p' 'P'] (['-' '+']? digit+ as e)
      { FLOAT (RConstHexa (i, f, remove_leading_plus e)) }
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
    try f lb with e -> raise (Loc.Located (loc lb, e))

  let parse_lexpr = with_location (lexpr token)
  let parse_file = with_location (file token)

  let lexpr_of_string s = parse_lexpr (from_string s)
}

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/why.byte"
End: 
*)

