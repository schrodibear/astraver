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

(*i $Id: why2html.mll,v 1.5 2006-11-03 12:49:07 marche Exp $ i*)

{
  open Arg
  open Lexing

  let cout = ref stdout
  let print s = output_string !cout s
}

let decl = "external" | "parameter" | "logic"
let keyw = "let" | "in" | "begin" | "end" | "if" | "then" | "else" | 
           (* "ref" | "array" | *)
	   "while" | "do" | "done" | "assert" | "label" | "fun" | "rec"
let ident = ['a'-'z']+

rule scan = parse
  | "(*"  { print "<font color=\"990000\">(*"; 
	    comment lexbuf; 
	    print "</font>";
	    scan lexbuf }
  | "{"   { print "<font color=\"green\">{"; 
	    annotation lexbuf; 
	    print "</font>";
	    scan lexbuf }
  | keyw  { print "<font color=\"0033cc\">"; print (lexeme lexbuf); 
	    print "</font>"; scan lexbuf }
  | decl  { print "<font color=\"990099\">"; print (lexeme lexbuf); 
	    print "</font>"; scan lexbuf }
  | eof   { () }
  | ident { print (lexeme lexbuf); scan lexbuf }
  | _     { print (lexeme lexbuf); scan lexbuf }

and comment = parse
  | "(*" { print "(*"; comment lexbuf; comment lexbuf }
  | "*)" { print "*)" }
  | eof  { () }
  | _    { print (lexeme lexbuf); comment lexbuf }

and annotation = parse
  | "}"  { print "}" }
  | eof  { () }
  | _    { print (lexeme lexbuf); annotation lexbuf }

{

  let translate_channel title cin = 
    print "<html><head><title>"; print title; print "</title></head><body>\n";
    print "<pre>\n";
    let lb = from_channel cin in 
    scan lb;
    print "</pre>\n</body></html>\n"

  let title = ref None

  let make_title f = match !title with None -> f | Some t -> t

  let translate_file f =
    let fout = f ^ ".html" in
    let c = open_out fout in
    cout := c;
    let cin = open_in f in
    translate_channel (make_title f) cin;
    close_in cin;
    close_out c

  let _ =
    let files = ref [] in
    Arg.parse 
	[ "-title", String (fun s -> title := Some s), 
	  "<title>  specifies a title" ]
	(fun s -> files := s :: !files)
	"usage: why2html [options] files";
    match !files with
      | [] -> translate_channel "" stdin 
      | fl -> List.iter translate_file fl

}
