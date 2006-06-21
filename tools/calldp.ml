(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: calldp.ml,v 1.11 2006-06-21 09:19:46 filliatr Exp $ i*)

open Printf

type prover_result = 
  | Valid | Invalid of string option | CannotDecide | Timeout | ProverFailure of string

let remove_file ?(debug=false) f =
  if not debug then try Sys.remove f with _ -> ()

let file_contents f =
  let buf = Buffer.create 1024 in
  try
    let c = open_in f in
    begin try 
      while true do 
	let s = input_line c in Buffer.add_string buf s; 
	Buffer.add_char buf '\n'
      done;
      assert false
    with End_of_file ->
      close_in c;
      Buffer.contents buf
    end
  with _ -> 
    sprintf "(cannot open %s)" f

let cvcl ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "timeout %d cvcl < %s > %s 2>&1" timeout f out in
  let c = Sys.command cmd in
  if c = 137 then 
    Timeout
  else if c <> 0 then (* e.g. timeout missing *)
    ProverFailure ("command failed: " ^ cmd)
  else if Sys.command (sprintf "grep -q -w -i Error %s" out) = 0 then
    ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let c = Sys.command (sprintf "grep -q -w Valid %s" out) in
    remove_file ?debug out;
    if c = 0 then Valid else Invalid None

let simplify ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "timeout %d Simplify %s > %s 2>&1" timeout f out in
  let c = Sys.command cmd in
  if c = 137 then 
    Timeout
  else if c <> 0 then (* e.g. timeout missing *)
    ProverFailure ("command failed: " ^ cmd)
  else if Sys.command (sprintf "grep -q -w ReadError %s" out) = 0 then
    ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let c = Sys.command (sprintf "grep -q -w Valid %s" out) in
    remove_file ?debug out;
    let r = if c = 0 then Valid else Invalid (Some (file_contents out)) in
    remove_file ?debug out;
    r

let zenon ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "timeout %d zenon %s > %s 2>&1" timeout f out in
  let c = Sys.command cmd in
  if c = 137 then 
    Timeout
  else if c <> 0 then (* e.g. timeout missing *)
    ProverFailure ("command failed: " ^ cmd)
  else if Sys.command (sprintf "grep -q -w Error %s" out) = 0 then
    ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let c = Sys.command (sprintf "grep -q PROOF-FOUND %s" out) in
    remove_file ?debug out;
    if c = 0 then Valid else Invalid None

let harvey ?debug ?(timeout=10) ?(eclauses=2000) ~filename:f () =
  let out = Sys.command (sprintf "rvc -e -t %s > /dev/null 2>&1" f) in
  if out = 0 then begin 
    let results = ref [] in
    let add r = results := r :: !results in
    let f = Filename.chop_suffix f ".rv" in
    let rec iter i =
      let fi = f ^ "-" ^ string_of_int i ^ ".baf" in
      if Sys.file_exists fi then begin
	let out = 
	  Sys.command (sprintf "timeout %d rv -d -e\"-T %d\" %s > out 2>&1" 
			 timeout eclauses fi) 
	in
	if out <> 0 then 
	  add Timeout
	else begin
	  let out = 
	    Sys.command 
	      "grep \"Proof obligation in\" out | grep -q \"is valid\"" 
	  in
	  add (if out = 0 then Valid else Invalid None)
	end;
	flush stdout;
	iter (i+1)
      end
    in
    iter 0;
    List.rev !results
  end else 
    [ProverFailure "rvc failed"]
