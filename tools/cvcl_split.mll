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

(*i $Id: cvcl_split.mll,v 1.4 2006-11-02 09:18:26 hubert Exp $ i*)

{

  open Printf
  open Lexing

  let debug = ref false
  let callback = ref (fun f -> assert false)

  (* we put everything not a goal into [buf] *)
  let buf = Buffer.create 8192

  let outc = ref stdout
  let print s = output_string !outc s

  let start_file () =
    let f = Filename.temp_file "cvcl" ".cvc" in
    outc := open_out f;
    print (Buffer.contents buf);
    f

  let end_file file =
    close_out !outc;
    !callback file;
    if not !debug then Sys.remove file

}

(* copy everything into [buf] until we find a query *)
rule split = parse
  | "QUERY" 
      { let file = start_file () in 
	print "QUERY"; query lexbuf; end_file file; split lexbuf }
  | "%" [^'\n']* '\n' 
      { Buffer.add_string buf (lexeme lexbuf); split lexbuf }
  | eof 
      { () }
  | _ 
      { Buffer.add_string buf (lexeme lexbuf); split lexbuf }

(* copy the query up to the semi-colon *)
and query = parse
  | ";" { print ";" }
  | "%" [^'\n']* '\n' 
        { print (lexeme lexbuf); query lexbuf }
  | eof { () }
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

