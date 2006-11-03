(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
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

{

  open Lexing
  open Colors

  exception Lexical_error of string
  exception Eof 

  let insert_text (tbuf:GText.buffer) ty s = 
    let it = tbuf#end_iter in
    let (fc, bc) = get_color ty in
    let new_tag = tbuf#create_tag [`BACKGROUND bc; `FOREGROUND fc] in
    tbuf#insert ~tags:[new_tag] ~iter:it s 

  let insert_string (tbuf:GText.buffer) s =
    let it = tbuf#end_iter in
    tbuf#insert ~iter:it s 

  let id_or_keyword =
    let h = Hashtbl.create 97 in
    List.iter 
      (fun s -> Hashtbl.add h s ())
      [ "typedef" ; "for"; "if"; "else"; "while"; "and"; "do"; "not"; "real"; 
	"var"; "begin"; "or"; "to"; "end"; "int"; "true"; "false";
	"type"; "function"; "of"; "then"; "break"; "void"; "struct";
	"return"; "include"];
    fun tbuf s -> 
      if Hashtbl.mem h s then
	insert_text tbuf "keyword" s
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
  | "//@"
      { Buffer.add_string comment "//@"; comment3 tbuf lexbuf; token tbuf lexbuf }
  | "//"
      { Buffer.add_string comment "//"; comment4 tbuf lexbuf; token tbuf lexbuf }
  | "/*@"
      { Buffer.add_string comment "/*@"; comment2 tbuf lexbuf; token tbuf lexbuf }
  | "/*"   
      { Buffer.add_string comment "/*"; comment1 tbuf lexbuf; token tbuf lexbuf }
  | ident  
      { id_or_keyword tbuf (lexeme lexbuf) }
  | '\r' 
         { token tbuf lexbuf }
  | digit+ 
  | float
  | _ as s 
      { insert_string tbuf s }
  | eof
      { raise Eof }

and comment1 tbuf = parse
  | "*/" { Buffer.add_string comment "*/";
	   let s = Buffer.contents comment in
	   insert_text tbuf "comment" s; 
	   Buffer.clear comment }
  | '\r' 
         { comment1 tbuf lexbuf }
  | _    { Buffer.add_string  comment (lexeme lexbuf); 
	   comment1 tbuf lexbuf }
  | eof  { () }

and comment2 tbuf = parse
  | "@*/" | "*/" as s 
	{ Buffer.add_string comment s;
	  let t = Buffer.contents comment in
	  insert_text tbuf "predicate" t; 
	  Buffer.clear comment }
  | '\r' 
        { comment2 tbuf lexbuf }
  | _   { Buffer.add_string  comment (lexeme lexbuf); 
	  comment2 tbuf lexbuf }
  | eof { () }

and comment3 tbuf = parse 
  | "\n" { Buffer.add_string comment "\n";
	   let t = Buffer.contents comment in
	   insert_text tbuf "predicate" t; 
	   Buffer.clear comment }
  | '\r' 
         { comment3 tbuf lexbuf }
  | _    { Buffer.add_string  comment (lexeme lexbuf); 
	   comment3 tbuf lexbuf}
  | eof  { () }

and comment4 tbuf = parse 
  | "\n" { Buffer.add_string comment "\n";
	   let t = Buffer.contents comment in
	   insert_text tbuf "comment" t; 
	   Buffer.clear comment }
  | '\r' 
         { comment4 tbuf lexbuf }
  | _    { Buffer.add_string  comment (lexeme lexbuf); 
	   comment4 tbuf lexbuf}
  | eof  { () }
