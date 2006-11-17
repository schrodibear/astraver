(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
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

(*i $Id: calldp.ml,v 1.21 2006-11-17 12:24:12 couchot Exp $ i*)

open Printf

type prover_result = 
  | Valid of float
  | Invalid of float * string option 
  | CannotDecide of float 
  | Timeout of float
  | ProverFailure of string

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

let timed_sys_command cmd =
  let t0 = Unix.times () in
  let ret = Sys.command cmd in
  let t1 = Unix.times () in
  let cpu_time = t1.Unix.tms_cutime -. t0.Unix.tms_cutime in
  cpu_time,ret

let cvcl ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "cpulimit %d cvcl < %s > %s 2>&1" timeout f out in
  let t,c = timed_sys_command cmd in
  if c = 152 then 
    Timeout t
  else if c <> 0 then (* e.g. timeout missing *)
    ProverFailure ("command failed: " ^ cmd)
  else if Sys.command (sprintf "grep -q -w -i Error %s" out) = 0 then
    ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let c = Sys.command (sprintf "grep -q -w Valid %s" out) in
    if c = 0 then 
      begin
	remove_file ?debug out;
	Valid t
      end 
    else 
      let c = Sys.command (sprintf "grep -q -w Unknown %s" out)  in
      if c= 0 then 
	begin
	  remove_file ?debug out;
	  CannotDecide t 
	end
      else
	begin
	  remove_file ?debug out;
	  Invalid (t, None)
	end
let simplify ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "cpulimit %d Simplify %s > %s 2>&1" timeout f out in
  let t,c = timed_sys_command cmd in
  if c = 152 then 
    Timeout t
  else if c <> 0 then (* e.g. timeout missing *)
    ProverFailure ("command failed: " ^ cmd)
  else if Sys.command (sprintf "grep -q -w ReadError %s" out) = 0 then
    ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let c = Sys.command (sprintf "grep -q -w Valid %s" out) in
    let r = if c = 0 then Valid t else Invalid (t,Some (file_contents out)) in
    remove_file ?debug out;
    r

let rvsat ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  (*let cmd = sprintf "rv-sat %s > %s 2>&1" f out in*)
  let cmd = sprintf "cpulimit %d rv-sat %s > %s 2>&1" timeout f out in
  let t,c = timed_sys_command cmd in
  if c = 152 then 
    Timeout t
  else 
    let c = Sys.command (sprintf "grep -q -w error %s" out) in
    if c =  0 then  
      begin 
	remove_file ?debug out; 
	ProverFailure ("command failed: " ^ cmd)
      end
      (*
	else if Sys.command (sprintf "grep -q -w ReadError %s" out) = 0 then
	ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
      *)
    else
      let c = Sys.command (sprintf "grep -q -w unsat %s" out) in
      remove_file ?debug out;
      if c = 0 then Valid t else Invalid(t,None)

let yices ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "cpulimit %d yices -tc -smt < %s > %s 2>&1" timeout f out in
  let t,c = timed_sys_command cmd in
  if c = 152 then
    Timeout t
  else 
    let c =  Sys.command (sprintf "grep -q -w Unexpected %s" out) in
    if c = 0 then 
      begin
	remove_file ?debug out; 
	ProverFailure ("command failed: " ^ cmd)
      end 
    else begin
	let c = Sys.command (sprintf "grep -q -w unsat %s" out) in
	if c = 0 then 
	  begin
	    remove_file ?debug out;
	    Valid t
	  end
	else 
	  let c = (Sys.command (sprintf "grep -q -w unknown %s" out)) * 
	    (Sys.command (sprintf "grep -q -w supported  %s" out))  in
	  remove_file ?debug out;
	  if c= 0 then CannotDecide t else
	  Invalid (t, None)
    end
      
let ergo ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "cpulimit %d ergo %s > %s 2>&1" timeout f out in
  let t,c = timed_sys_command cmd in
  if c = 152 then
    Timeout t
  else 
    let c = Sys.command (sprintf "grep -q -w Error %s" out) in
    if c = 0 then begin 
      remove_file ?debug out; 
      ProverFailure ("command failed: " ^ cmd)
    end else begin
      let c = Sys.command (sprintf "grep -q -w Valid %s" out) in
      remove_file ?debug out;
      if c = 0 then Valid t else Invalid(t, None)
    end

let harvey ?debug ?(timeout=10) ?(eclauses=200000) ~filename:f () =
  let out = Sys.command (sprintf "rvc  %s > /dev/null 2>&1" f) in
  if out = 0 then begin 
    let results = ref [] in
    let add r = results := r :: !results in
    let f = Filename.chop_suffix f ".rv" in
    let rec iter i =
      let fi = f ^ "-" ^ string_of_int i ^ ".baf" in
      if Sys.file_exists fi then begin
	(* *)
	let out = Filename.temp_file "out" "" in
	let cmd = sprintf "timeout  %d rv --dpll   %s > %s 2>&1" timeout  fi out in
	let t,c = timed_sys_command cmd in
	if c = 152 then
	  add (Timeout t)
	else 
	  let c = Sys.command (sprintf 
				   "grep  -q -w \"is valid\" %s " out) in 
	  remove_file ?debug out;
	  add (if c = 0 then Valid t else Invalid(t, None))
      end	   	
    in
    iter 0;
    List.rev !results
  end else 
    [ProverFailure "rvc failed"]
      

let zenon ?debug ?(timeout=10) ~filename:f () =
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "cpulimit %d zenon %s > %s 2>&1" timeout f out in
  let t,c = timed_sys_command cmd in
  if c = 152 then 
    Timeout t
  else if c <> 0 then (* e.g. timeout missing *)
    ProverFailure ("command failed: " ^ cmd)
  else if Sys.command (sprintf "grep -q -w Error %s" out) = 0 then
    ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let c = Sys.command (sprintf "grep -q PROOF-FOUND %s" out) in
    remove_file ?debug out;
    if c = 0 then Valid t else Invalid(t, None)
