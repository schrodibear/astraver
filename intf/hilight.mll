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

(*i $Id: hilight.mll,v 1.3 2003-06-19 07:37:52 filliatr Exp $ i*)

{

  open Lexing

  type token = Code of string | Annotation of string
  exception Lex_error of string
}

rule next_code = parse
  | [^'{']* 
    { let c = Code (lexeme lexbuf) in 
      c :: next_code lexbuf }
  | '{'  
      { let a = Annotation ("{" ^ next_annotation lexbuf) in 
	a :: next_code lexbuf }
  | eof  
      { [] }
and next_annotation = parse
  | [^'}']*'}' 
      { lexeme lexbuf }
  | _ 
      { raise (Lex_error "Error in annotation") }
  | eof  
      { raise (Lex_error "No closing }") }

and next_code_c = parse
  | "/*"  
      { let a = Annotation ("/*" ^ next_annotation_c lexbuf) in 
	a :: next_code_c lexbuf }
  | [^'/']*
      { let c = Code (lexeme lexbuf) in c :: next_code_c lexbuf }
  | eof  
      { [] }
and next_annotation_c = parse
  | [^'/']* "*/"
      { lexeme lexbuf }
  | _ 
      { raise (Lex_error "Error in annotation") }
  | eof  
      { raise (Lex_error "No closing }") }

