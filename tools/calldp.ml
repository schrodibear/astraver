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

(*i $Id: calldp.ml,v 1.1 2005-06-22 06:53:57 filliatr Exp $ i*)

open Printf

type prover_result = Valid | Invalid | CannotDecide | Timeout

type prover_caller = timeout:int -> filename:string -> prover_result

let debug = ref false

let call cmd =
  if !debug then begin eprintf "calling: %s\n" cmd; flush stderr end;
  let out = Sys.command cmd in
  if out = 0 then Valid
  else if out = 1 then Invalid
  else Timeout

let cvcl ?(timeout=10) ~filename:f () =
  call
    (sprintf "ulimit -t %d; cvcl < %s > out 2>&1 && grep -q -w Valid out" 
       timeout f)

let simplify ?(timeout=10) ~filename:f () =
  call
    (sprintf "ulimit -t %d; Simplify %s > out 2>&1 && grep -q -w Valid out" 
       timeout f)

let harvey ?(timeout=10) ?(eclauses=2000) ~filename:f () =
  let out = Sys.command (sprintf "rvc -e -t %s > /dev/null 2>&1" f) in
  if out = 0 then begin 
    let results = ref [] in
    let add r = results := r :: !results in
    let f = Filename.chop_suffix f ".rv" in
    let rec iter i =
      let fi = f ^ "-" ^ string_of_int i ^ ".baf" in
      if Sys.file_exists fi then begin
	let out = 
	  Sys.command (sprintf "timeout %d rv -e\"-T %d\" %s > out 2>&1" 
			 timeout eclauses fi) 
	in
	if out <> 0 then 
	  add Timeout
	else begin
	  let out = 
	    Sys.command 
	      "grep \"Proof obligation in\" out | grep -q \"is valid\"" 
	  in
	  add (if out = 0 then Valid else Invalid)
	end;
	flush stdout;
	iter (i+1)
      end
    in
    iter 0;
    List.rev !results
  end
  else failwith "rvc failed"
