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

(*i $Id: smtlib_split.mll,v 1.5 2006-11-03 12:49:07 marche Exp $ i*)

{

  open Printf
  open Lexing 

  let debug = ref true
  let callback = ref (fun f -> assert false : string -> unit)

  (* we put everything not a goal into [buf] *)
  let buf = Buffer.create 8192

  let outc = ref stdout
  let file = ref ""
  let level = ref 0 

  let print s = 
    output_string !outc s

(*  let start_file () =
    let f = Filename.temp_file "smtlib" ".smt" in
    outc := open_out f;
    f
*)
  let end_file file =
    close_out !outc;
    !callback file;
    if not !debug then Sys.remove file

}

let space = [' ' '\t' '\n' '\r']
let ident = ['a'-'z' 'A'-'Z' '0'-'9']+

rule split = parse
  | "(" space* "benchmark"
      { Buffer.add_string buf (lexeme lexbuf); 
	split lexbuf 
      }
  | ":" space* "status"  
      { 
	Buffer.add_string buf (lexeme lexbuf); 
	split lexbuf }
  | ":" space* ("extrasorts" | "extrafuns" | "assumption")
      { Buffer.add_string buf (lexeme lexbuf); 
	lisp_copy lexbuf; split lexbuf }
  | ident 
      { 
	Buffer.add_string buf (lexeme lexbuf);
	split lexbuf } 
  | ":" space* "formula"
      { 
	file := Filename.temp_file "smtlib" ".smt"; 
	(*printf "formula: ouverture du fichier %s \n" !file ;*)
	level := 0 ;
	outc := open_out !file;
	print (Buffer.contents buf);
	print (lexeme lexbuf); 
	query lexbuf;
	print ")" ; (* ends the benchmark bracket *)
	(*printf "formula: fermeture du fichier %s \n" !file ; *)
	end_file !file;
	split lexbuf}
  | eof 
      { () }
  | _ 
      { 
      Buffer.add_string buf (lexeme lexbuf); split lexbuf }




(* copies into [buf] until the end of the S-expression *)
and lisp_copy = parse
  | "(" { Buffer.add_char buf '('; lisp_copy lexbuf; }
  | ")" { Buffer.add_char buf ')' }
  | eof { () }
  | _   { Buffer.add_string buf (lexeme lexbuf); lisp_copy lexbuf }

(* prints up to the end of the S-expression *)
and query = parse
  | "(" { print "("; 
	  level := !level + 1 ; 
	  query lexbuf;}
  | ")" { print ")" ;
	  level := !level - 1 ;
	  (*printf ")%d" !level ; *)
	  if !level <> 0 then query lexbuf 
	}
  | _   { print (lexeme lexbuf); query lexbuf }

{

  let iter cb f =
    callback := cb;
    Buffer.reset buf;
    let c = open_in f in
    let lb = from_channel c in
    split lb;
    close_in c

}

