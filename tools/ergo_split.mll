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

(*i $Id: ergo_split.mll,v 1.9 2009-12-27 16:46:36 bobot Exp $ i*)

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
    !callback "ergo.why" [buf;buf_goal]

}

let letters = ['a'-'z''A'-'Z''_''0'-'9']+

rule split = parse
  | "goal" 
      { start_file (); print_goal "goal"; goal lexbuf }
  | (letters | _) as s
      { print_hypo s; split lexbuf }
  | eof 
      { () }

(* copy the query up to the semi-colon *)
and goal = parse
  | "goal" 
      { end_file (); start_file ();
	print_goal "goal "; goal lexbuf }
  | ("\"" ([^ '\"'] | "\\" _)* "\"") as s
      { print_goal s; goal lexbuf }
  | ("type" | "logic" | "predicate" | "axiom") as k
      { end_file (); print_hypo k; split lexbuf }
  | (letters | _) as s
      { print_goal s; goal lexbuf }
  | eof { end_file () }

{

  let iter cb c =
    callback := cb;
    Buffer.reset buf;
    let lb = from_channel c in
    split lb

}
