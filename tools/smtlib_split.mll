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

(*i $Id: smtlib_split.mll,v 1.14 2010-01-18 14:16:20 marche Exp $ i*)

{

  open Printf
  open Lexing 

  let debug = ref false
  let callback = ref (fun _ _ -> assert false : string -> Buffer.t list -> unit)

  (* we put everything not a goal into [buf] *)
  let buf = Buffer.create 8192
  let buf_goal = Buffer.create 512

  let print_hypo s = Buffer.add_string buf s
  let print_goal s = Buffer.add_string buf_goal s

  let start_file () =
    Buffer.reset buf_goal

  let end_file () =
    !callback "smtlib.smt" [buf;buf_goal]

  let level = ref 0 

}

let space = [' ' '\t' '\n' '\r']
let ident = ['a'-'z' 'A'-'Z' '0'-'9']+

rule split = parse
  | "(" space* "benchmark"
      { print_hypo (lexeme lexbuf); 
	split lexbuf 
      }
  | ":" space* "status"  
      { 
	print_hypo (lexeme lexbuf); 
	split lexbuf }
  | ":" space* ("extrasorts" | "extrafuns" | "assumption")
      { print_hypo (lexeme lexbuf); 
	lisp_copy lexbuf; split lexbuf }
  | ident 
      { 
	print_hypo (lexeme lexbuf);
	split lexbuf } 
  | ":" space* "formula"
      { 
	(*printf "formula: ouverture du fichier %s \n" !file ;*)
        start_file();
	level := 0 ;
        print_goal (lexeme lexbuf);
	query lexbuf;
	print_goal ")" ; (* ends the benchmark bracket *)
	(*printf "formula: fermeture du fichier %s \n" !file ; *)
	end_file ();
	split lexbuf}
  | eof 
      { () }
  | _ 
      { 
      print_hypo (lexeme lexbuf); split lexbuf }




(* copies into [buf] until the end of the S-expression *)
and lisp_copy = parse
  | "(" { Buffer.add_char buf '('; lisp_copy lexbuf; }
  | ")" { Buffer.add_char buf ')' }
  | eof { () }
  | _   { print_hypo (lexeme lexbuf); lisp_copy lexbuf }

(* prints up to the end of the S-expression *)
and query = parse
  | "(" { print_goal "("; 
	  level := !level + 1 ; 
	  query lexbuf;}
  | ")" { print_goal ")" ;
	  level := !level - 1 ;
	  (*printf ")%d" !level ; *)
	  if !level <> 0 then query lexbuf 
	}
  | _   { print_goal (lexeme lexbuf); query lexbuf }

{

  let iter cb c =
    callback := cb;
    Buffer.reset buf;
    let lb = from_channel c in
    split lb

}

