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

{

  open Lexing

  exception Lexical_error of string
  exception Eof 

  type color = Predicate | Comment | Keyword

  let getcolor = function 
    | Predicate -> "darkgreen"
    | Comment -> "red"
    | Keyword -> "blue"

  let insert_text (tbuf:GText.buffer) ty s = 
    let it = tbuf#end_iter in
    let new_tag = tbuf#create_tag [`FOREGROUND (getcolor ty)] in
    tbuf#insert ~tags:[new_tag] ~iter:it s 

  let insert_string (tbuf:GText.buffer) s =
    let it = tbuf#end_iter in
    tbuf#insert ~iter:it s 

  let id_or_keyword =
    let h = Hashtbl.create 97 in
    List.iter 
      (fun s -> Hashtbl.add h s ())
      [ "for"; "if"; "else"; "while"; "and"; "do"; "not"; "real"; 
	"var"; "begin"; "or"; "to"; "end"; "int"; "true"; "false";
	"type"; "function"; "of"; "then"; "break"; "void"; "struct";
	"return"];
    fun tbuf s -> 
      if Hashtbl.mem h s then
	insert_text tbuf Keyword s
      else 
	insert_string tbuf s

  let comment = Buffer.create 1024

}

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = alpha (alpha | '_' | digit)*
let exponent = ('e' | 'E') ('+' | '-')? digit+
let float = digit+ '.' digit+ exponent?
  | digit+ exponent

rule token tbuf = parse
  | "/*@"
      { Buffer.add_string comment "/*@"; comment2 tbuf lexbuf; token tbuf lexbuf }
  | "/*"   
      { Buffer.add_string comment "/*"; comment1 tbuf lexbuf; token tbuf lexbuf }
  | ident  
      { id_or_keyword tbuf (lexeme lexbuf) }
  | digit+ 
  | float
  | _ as s 
      { insert_string tbuf s }
  | eof
      { raise Eof }

and comment1 tbuf = parse
  | "*/" { Buffer.add_string comment "*/";
	   let s = Buffer.contents comment in
	   insert_text tbuf Comment s; 
	   Buffer.clear comment }
  | _    { Buffer.add_string  comment (lexeme lexbuf); 
	   comment1 tbuf lexbuf }
  | eof  { raise (Lexical_error "unterminated comment") }

and comment2 tbuf = parse
  | "@*/" | "*/" as s 
	{ Buffer.add_string comment s;
	  let t = Buffer.contents comment in
	  insert_text tbuf Predicate t; 
	  Buffer.clear comment }
  | _   { Buffer.add_string  comment (lexeme lexbuf); 
	  comment2 tbuf lexbuf }
  | eof { raise (Lexical_error "unterminated comment") }
