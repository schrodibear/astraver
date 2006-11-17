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

(*i $Id: calldp.ml,v 1.24 2006-11-17 16:16:15 marche Exp $ i*)

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

let timed_sys_command ~debug timeout cmd =
  let t0 = Unix.times () in
  if debug then Format.eprintf "command line: %s@." cmd;
  let out = Filename.temp_file "out" "" in
  let cmd = sprintf "cpulimit %d %s > %s 2>&1" timeout cmd out in
  let ret = Sys.command cmd in
  let t1 = Unix.times () in
  let cpu_time = t1.Unix.tms_cutime -. t0.Unix.tms_cutime in
  if debug then Format.eprintf "Output file %s:@.%s@." out (file_contents out);
  (cpu_time,ret,out)

let error c t cmd =
  if c = 152 then Timeout t 
  else ProverFailure ("command failed: " ^ cmd) 

let cvcl ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "cvcl < %s" f in
  let t,c,out = timed_sys_command debug timeout cmd in
  if c <> 0 then error c t cmd
  else if Sys.command (sprintf "grep -q -w -i Error %s" out) = 0 then
    ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let c = Sys.command (sprintf "grep -q -w Valid %s" out) in
    if c = 0 then 
      begin
	remove_file ~debug out;
	Valid t
      end 
    else 
      let c = Sys.command (sprintf "grep -q -w Unknown %s" out)  in
      if c= 0 then 
	begin
	  remove_file ~debug out;
	  CannotDecide t 
	end
      else
	begin
	  remove_file ~debug out;
	  Invalid (t, None)
	end

let simplify ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "Simplify %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then error c t cmd
  else 
    let r =
      if Sys.command (sprintf "grep -q -w Valid %s" out) = 0 then
	Valid t
      else
	if Sys.command (sprintf "grep -q -w Invalid %s" out) = 0 then
	  Invalid (t,Some (file_contents out)) 
	else
	  ProverFailure ("command failed: " ^ cmd ^ "\n" ^ file_contents out)
    in
    remove_file ~debug out;
    r

let rvsat ?(debug=false) ?(timeout=10) ~filename:f () =
  (*let cmd = sprintf "rv-sat %s" f in*)
  let cmd = sprintf "rv-sat %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then error c t cmd
  else 
    let r =
      if Sys.command (sprintf "grep -q -w unsat %s" out) = 0 then
	Valid t
      else
	ProverFailure ("command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r

let yices ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "yices -tc -smt < %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then error c t cmd
  else 
    let r = 
      if Sys.command (sprintf "grep -q -w unsat %s" out) = 0 then
	Valid t
      else
	if Sys.command (sprintf "grep -q -w unknown %s" out) = 0 then
	  CannotDecide t
	else
	  ProverFailure ("command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r

let ergo ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "ergo %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then error c t cmd
  else 
    let r =
      if Sys.command (sprintf "grep -q -w Valid %s" out) = 0 then
	Valid t
      else	
	ProverFailure ("command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r
    
let harvey ?(debug=false) ?(timeout=10) ?(eclauses=200000) ~filename:f () =
  if debug then Format.eprintf "Calling rvc@.";
  let cmd = sprintf "rvc %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if debug then Format.eprintf "rvc done@.";
  if c <> 0 then [error c t cmd]
  else
    let results = ref [] in
    let add r = results := r :: !results in
    let f = Filename.chop_suffix f ".rv" in
    let rec iter i =
      let fi = f ^ "-" ^ string_of_int i ^ ".baf" in
      if Sys.file_exists fi then begin
	(* *)
	let cmd = sprintf "rv --dpll %s" fi in
	let t,c,out = timed_sys_command ~debug timeout cmd in
	if c = 152 then 
	  add (Timeout t)
	else 
	  let r =
	    if Sys.command 
	      (sprintf "grep  -q -w \"is valid\" %s " out) = 0 then
		Valid t
	    else
	      if Sys.command 
		(sprintf "grep  -q -w \"Cannot decide\" %s " out) = 0 then
		  CannotDecide t
	      else
		ProverFailure ("command failed: " ^ cmd)
	  in
	  remove_file ~debug out;
	  add r
      end	   	
    in
    iter 0;
    List.rev !results
      

let zenon ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "zenon %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then error c t cmd
  else 
    let r =
      if Sys.command (sprintf "grep -q PROOF-FOUND %s" out) = 0 then
	Valid t
      else
	ProverFailure ("command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r
