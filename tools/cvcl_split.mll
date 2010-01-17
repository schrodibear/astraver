(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: cvcl_split.mll,v 1.13 2010-01-17 16:07:14 bobot Exp $ i*)

{

  open Printf
  open Lexing

  let debug = ref false
  let callback = ref (fun _ _ -> assert false)

  (* we put everything not a goal into [buf] *)
  let buf = Buffer.create 8192
  let buf_goal = Buffer.create 512

  let print_hypo s = Buffer.add_string buf s
  let print_goal s = Buffer.add_string buf_goal s

  let start_file () =
    Buffer.reset buf_goal

  let end_file () =
    !callback "cvcl.cvc" [buf;buf_goal]

}

(* copy everything into [buf] until we find a query *)
rule split = parse
  | "QUERY" 
      { start_file ();
	print_goal "QUERY"; query lexbuf; end_file (); split lexbuf }
  | "%" [^'\n']* '\n' 
      { print_hypo (lexeme lexbuf); split lexbuf }
  | eof 
      { () }
  | _ 
      { print_hypo (lexeme lexbuf); split lexbuf }

(* copy the query up to the semi-colon *)
and query = parse
  | ";" { print_goal ";" }
  | "%" [^'\n']* '\n' 
        { print_goal (lexeme lexbuf); query lexbuf }
  | eof { () }
  | _   { print_goal (lexeme lexbuf); query lexbuf }

{

  let iter cb c =
    callback := cb;
    Buffer.reset buf;
    let lb = from_channel c in
    split lb

}

