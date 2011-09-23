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

(*i $Id: zenon_split.mll,v 1.10 2009-12-27 16:46:36 bobot Exp $ i*)

{

  open Printf
  open Lexing 

  let no_remove = ref false
  let callback = ref (fun _ _ -> assert false)

  (* we put everything not a goal into [buf] *)
  let buf = Buffer.create 8192

  let outc = ref stdout
  let print s = output_string !outc s

  let start_file () =
    let f = Filename.temp_file "zenon" ".znn" in
    outc := open_out f;
    print (Buffer.contents buf);
    f

  let end_file file =
    close_out !outc;
    !callback file [];
    Lib.remove_file ~debug:!no_remove file

}

let space = [' ' '\t' '\n' '\r']
let idstart = ['A'-'Z' 'a'-'z' '_']
let idchar =  ['A'-'Z' 'a'-'z' '_' '0'-'9']
let ident = idstart idchar*

rule split = parse
  | ";" [^'\n']* '\n' 
        { Buffer.add_string buf (lexeme lexbuf); split lexbuf }
  | "(" 
      { Buffer.add_string buf (lexeme lexbuf); 
	lisp_copy lexbuf; split lexbuf }
  | "$goal" space
      { let file = start_file () in 
	print "$goal "; query lexbuf; end_file file; split lexbuf }
  | eof 
      { () }
  | _ 
      { Buffer.add_string buf (lexeme lexbuf); split lexbuf }

(* copies into [buf] until the end of the S-expression *)
and lisp_copy = parse
  | "(" { Buffer.add_char buf '('; lisp_copy lexbuf; lisp_copy lexbuf }
  | ")" { Buffer.add_char buf ')' }
  | ";" [^'\n']* '\n' 
        { Buffer.add_string buf (lexeme lexbuf); lisp_copy lexbuf }
  | eof { () }
  | _   { Buffer.add_string buf (lexeme lexbuf); lisp_copy lexbuf }

(* prints the next S-expression *)
and query = parse
  | ident { print (lexeme lexbuf) }
  | "(" { print "("; lisp_print lexbuf }
  | ";" [^'\n']* '\n' 
        { print (lexeme lexbuf); query lexbuf }
  | eof { () }
  | _   { print (lexeme lexbuf); query lexbuf }

(* prints until the end of the S-expression *)
and lisp_print = parse
  | "(" { print "("; lisp_print lexbuf; lisp_print lexbuf }
  | ")" { print ")" }
  | ";" [^'\n']* '\n' 
        { print (lexeme lexbuf); lisp_print lexbuf }
  | eof { () }
  | _   { print (lexeme lexbuf); lisp_print lexbuf }

{

  let iter ~debug cb f =
    callback := cb;
    no_remove := debug;
    Buffer.reset buf;
    let c = open_in f in
    let lb = from_channel c in
    split lb;
    close_in c

}

