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

(*i $Id: why2html.mll,v 1.1 2003-09-15 08:40:40 filliatr Exp $ i*)

{
  open Lexing

  let cout = ref stdout
  let print s = output_string !cout s
}

rule scan = parse
  | "(*"  { print "<font color=\"red\">"; 
	    comment lexbuf; 
	    print "</font>";
	    scan lexbuf }
  | "{"   { print "<font color=\"green\">"; 
	    annotation lexbuf; 
	    print "</font>";
	    scan lexbuf }
  | eof   { () }
  | _     { print (lexeme lexbuf); scan lexbuf }

and comment = parse
  | "(*" { print "(*"; comment lexbuf; comment lexbuf }
  | "*)" { print "*)" }
  | eof  { () }
  | _    { print (lexeme lexbuf); comment lexbuf }

and annotation = parse
  | "}"  { print "}" }
  | eof  { () }
  | _    { print (lexeme lexbuf); comment lexbuf }

{

  let translate_channel title cin = 
    print "<html><head><title>"; print title; print "</title></head><body>\n";
    print "<pre>\n";
    let lb = from_channel cin in 
    scan lb;
    print "</pre>\n</body></html>\n"

  let translate_file f =
    let fout = f ^ ".html" in
    let c = open_out fout in
    cout := c;
    let cin = open_in f in
    translate_channel f cin;
    close_in cin;
    close_out c

  let _ =
    let argn = Array.length Sys.argv in
    if argn = 1 then 
      translate_channel "" stdin 
    else 
      for i = 1 to argn - 1 do translate_file Sys.argv.(i) done

}
