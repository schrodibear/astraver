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

{

  open Printf
  open Lexing 

  let no_remove = ref false
  let callback = ref (fun _ _ -> assert false : string -> Buffer.t list -> unit)

  (* we put everything not a goal into [buf] *)
  let buf = Buffer.create 8192

  let outc = ref stdout
  let file = ref ""
  let level = ref 0 

  let print s = 
    output_string !outc s

  let end_file file =
    close_out !outc;
    !callback file [];
    Lib.remove_file ~debug:!no_remove file

}

let space = [' ' '\t' '\n' '\r']
let ident = ['a'-'z' 'A'-'Z' '0'-'9']+

rule split = parse
  | "(" space* "(theory" space* "(extends)"
      { 
	Buffer.add_string buf (lexeme lexbuf) ;
	split lexbuf 
      }
  | ";;" space*"Why axiom"  
      {
	Buffer.add_string buf ";;"  ;
	splitAxiom lexbuf;
	split lexbuf
      }

  | "))" space* ")" space*";;" space*  "END THEORY" 
      { 
	Buffer.add_string buf (lexeme lexbuf);
	split lexbuf 
      }
  | ";;" space* "Why obligation" 
      {
	file := Filename.temp_file "rv" ".rv"; 
	level := 0 ;
	outc := open_out !file;
	print (Buffer.contents buf);
	print (lexeme lexbuf); 
	query lexbuf;
	end_file !file;
	split lexbuf
      }
  | eof {()}
  |_ 
      {
	Buffer.add_string buf (lexeme lexbuf) ;
       split lexbuf}
      

and splitAxiom = parse
  | "(" { Buffer.add_char buf '('; 
	  level := !level + 1 ; 
	  splitAxiom lexbuf;
	}
  | ")" { Buffer.add_char buf ')'; 
	  level := !level - 1 ;
	  if !level <> 0 then splitAxiom lexbuf 
	}
  | _   { Buffer.add_string buf (lexeme lexbuf); 
	  splitAxiom lexbuf }

and query = parse
  | "(" { print "(";
	  level := !level + 1 ; 
	  query lexbuf;}
  | ")" { print ")" ;
	  level := !level - 1 ;
	  if !level <> 0 then query lexbuf 
	}
  | _   { print (lexeme lexbuf); query lexbuf }

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

