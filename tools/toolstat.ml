(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
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

(*i $Id: toolstat.ml,v 1.1 2008-10-08 01:22:04 moy Exp $ i*)

(* Statistics on automatic provers results *)

open Format
open Toolstat_types

let spec = []
let usage = "tool-stat file"
let records = ref []

let rec explain_exception fmt = function
  | Parsing.Parse_error -> 
      fprintf fmt "Syntax error"
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Loc.Located (loc, e) ->
      fprintf fmt "%a%a" Loc.report_position loc explain_exception e
  | e ->
      fprintf fmt "Anomaly: %s" (Printexc.to_string e); raise e

let parse_file f =
  try
    let c = open_in f in
    let lb = Lexing.from_channel c in
    lb.Lexing.lex_curr_p <- { lb.Lexing.lex_curr_p with Lexing.pos_fname = f };
    records := Toolstat_lex.parse lb;
    close_in c
  with e -> 
    explain_exception err_formatter e;
    pp_print_newline err_formatter ();
    exit 1

let hadd single combine h k v =
  try
    let ls = Hashtbl.find h k in
    Hashtbl.replace h k (combine v ls)
  with Not_found ->
    Hashtbl.replace h k (single v)

let intadd h k v = hadd (fun x -> x) ( + ) h k v
let timeadd = 
  hadd (fun x -> x) 
    (fun (h1,m1,s1) (h2,m2,s2) -> 
       let h3 = h1 + h2 and m3 = m1 + m2 and s3 = s1 +. s2 in
       let carry = (int_of_float (floor s3)) / 60 in
       let m3 = m3 + carry and s3 = s3 -. (float_of_int (60 * carry)) in
       let carry = m3 / 60 in
       let h3 = h3 + carry and m3 = m3 - (60 * carry) in
       h3,m3,s3)

let hfind default h k =
  try Hashtbl.find h k with Not_found -> default

let valid_summary (n1,n2,n3,n4,n5) = n1
let notvalid_summary (n1,n2,n3,n4,n5) = n2 + n3 + n4 + n5

let valid_detail (s1,s2,s3,s4,s5) = s1
let notvalid_detail (s1,s2,s3,s4,s5) = s2 @ s3 @ s4 @ s5

let print_time fmt (h,m,s) =
  if h = 0 && m = 0 && s = 0. then 
    fprintf fmt "0. s"
  else
    fprintf fmt "%a%a%a"
      (fun fmt h -> if h = 0 then () else fprintf fmt "%d h " h) h
      (fun fmt m -> if m = 0 then () else fprintf fmt "%d m " m) m
      (fun fmt s -> if s = 0. then () else fprintf fmt "%.2f s " s) s

let () = 
  Arg.parse spec parse_file usage;
  let records : record list = !records in

  let provers : (prover, unit) Hashtbl.t = Hashtbl.create 5 in
  let tests_count : (test * int, int) Hashtbl.t = Hashtbl.create 5 in
  List.iter (fun (prover,test,summary,detail,time) ->
	       Hashtbl.replace provers prover ();
	       List.iter
		 (fun i -> intadd tests_count (test,i) 1) (valid_detail detail)
	    ) records;

  printf "@.Best individual provers:@.";
  let provers_valid : (prover, int) Hashtbl.t = Hashtbl.create 17 in
  let provers_notvalid : (prover, int) Hashtbl.t = Hashtbl.create 17 in
  let provers_time : (prover, time) Hashtbl.t = Hashtbl.create 17 in
  List.iter (fun (prover,test,summary,detail,time) ->
	       intadd provers_valid prover (valid_summary summary);
	       intadd provers_notvalid prover (notvalid_summary summary);
	       timeadd provers_time prover time
	    ) records;
  let provers_data = 
    Hashtbl.fold (fun p () acc ->
		    (p, 
		     hfind 0 provers_valid p, 
		     hfind 0 provers_notvalid p,
		     hfind (0,0,0.) provers_time p)
		    :: acc
		 ) provers [] 
  in
  let provers_ranking =
    List.sort (fun (p1,v1,n1,t1) (p2,v2,n2,t2) -> 
		 let c = compare v2 v1 in
		 if c = 0 then compare t1 t2 else c)
      provers_data
  in
  ignore (List.fold_left 
	    (fun i (p,v,n,t) ->
	       printf "%d: %s   \t%d valid \t%d not valid \tin %a@." 
		 i p v n print_time t;
	       i+1
	    ) 1 provers_ranking);
  
  printf "@.Best combination provers:@.";
  let provers_ahead = Hashtbl.create 17 in
  let provers_behind = Hashtbl.create 17 in
  List.iter (fun (prover,test,summary,detail,time) ->
	       List.iter
		 (fun i ->
		    assert (Hashtbl.mem tests_count (test,i));
		    if Hashtbl.find tests_count (test,i) = 1 then
		      intadd provers_ahead prover 1
		 ) (valid_detail detail);
	       List.iter
		 (fun i ->
		    if hfind 0 tests_count (test,i) > 0 then
		      intadd provers_behind prover 1
		 ) (notvalid_detail detail)
	    ) records;
  let provers_data =
    Hashtbl.fold (fun p () acc ->
		    (p,
		     hfind 0 provers_ahead p,
		     hfind 0 provers_behind p)
		    :: acc
		 ) provers []
  in
  let provers_ranking =
    List.sort (fun (p1,a1,b1) (p2,a2,b2) ->
		 let c = compare a2 a1 in
		 if c = 0 then compare b1 b2 else c)
      provers_data
  in
  ignore (List.fold_left
	    (fun i (p,a,b) ->
	       printf "%d: %s   \t%d alone \t%d by others@." i p a b;
	       i+1
	    ) 1 provers_ranking)
  
