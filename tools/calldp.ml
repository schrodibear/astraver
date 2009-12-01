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
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: calldp.ml,v 1.69 2009-12-01 11:51:36 marche Exp $ i*)

open Printf


type prover_result = 
  | Valid of float                         
  | Invalid of float * string option       
  | CannotDecide of float * string option  
  | Timeout of float                       
  | ProverFailure of float * string        

let cpulimit = ref "why-cpulimit"


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
  let cmd = sprintf "%s %d %s > %s 2>&1" !cpulimit timeout cmd out in
  let ret = Sys.command cmd in
  let t1 = Unix.times () in
  let cpu_time = t1.Unix.tms_cutime -. t0.Unix.tms_cutime in
  if debug then Format.eprintf "Output file %s:@.%s@." out (file_contents out);
  (cpu_time,ret,out)

let grep re str =
  let re =
    match re.DpConfig.cregexp with
      | None ->
          let r = Str.regexp re.DpConfig.regexp in
          re.DpConfig.cregexp <- Some r;
          r
      | Some r -> r
    in
  try
    let _ = Str.search_forward re str 0 in true
  with Not_found -> false

let gen_prover_call ?(debug=false) ?(timeout=10) ?(switch="") ~filename:f p =
  let cmd = 
    p.DpConfig.command ^ " " ^ p.DpConfig.command_switches ^ " " ^ 
      switch ^ " " ^ f 
  in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c = 152 (* 128 + SIGXCPU signal (i.e. 24, /usr/include/bits/signum.h) *) 
  then 
    (remove_file ~debug out; Timeout t)
  else
    let res = file_contents out in
    let r =
      let valid_result =
	match p.DpConfig.valid_regexp with
	  | None -> c == 0
	  | Some r -> grep r res
      in
      if valid_result then
        Valid t
      else if grep p.DpConfig.undecided_regexp res then
        CannotDecide(t, None)
      else
        ProverFailure(t,"prover command " ^ cmd ^ " produced unrecognized answer: " ^ out)
      in
    remove_file ~debug out;
    r

let gappa ?(debug=false) ?(timeout=10) ~filename:f () =
  gen_prover_call ~debug ~timeout ~filename:f DpConfig.gappa
(*
  let p = DpConfig.gappa in
  let cmd = 
    p.DpConfig.command ^ " " ^ p.DpConfig.command_switches ^ " " ^ f 
  in
  let t,c,out = timed_sys_command debug timeout cmd in
  let r =
    if c = 152 (* 128 + SIGXCPU signal (i.e. 24, /usr/include/bits/signum.h) *) 
    then Timeout t
    else
      let res = file_contents out in
      if c == 0 then
        Valid t
      else if c == 1 && grep p.DpConfig.undecided_regexp res then
        CannotDecide(t, Some res) 
      else
        ProverFailure(t, "command failed: " ^ cmd ^ "\n" ^ res)
  in
  remove_file ~debug out;
  r
*)

let ergo ?(debug=false) ?(timeout=10) ~select_hypotheses ~filename:f () =
  if select_hypotheses then
    gen_prover_call ~debug ~timeout ~switch:"-select 1" 
      ~filename:f DpConfig.alt_ergo
  else    
    gen_prover_call ~debug ~timeout 
      ~filename:f DpConfig.alt_ergo

let coq ?(debug=false) ?(timeout=10) ~filename:f () =
  gen_prover_call ~debug ~timeout ~filename:f DpConfig.coq
	        
let simplify ?(debug=false) ?(timeout=10) ~filename:f () =
  gen_prover_call ~debug ~timeout ~filename:f DpConfig.simplify

let z3 ?(debug=false) ?(timeout=10) ~filename:f () =
  gen_prover_call ~debug ~timeout ~filename:f DpConfig.z3

let yices ?(debug=false) ?(timeout=10) ~filename:f () =
  gen_prover_call ~debug ~timeout ~filename:f DpConfig.yices

let cvc3 ?(debug=false) ?(timeout=10) ~filename:f () =
  gen_prover_call ~debug ~timeout ~filename:f DpConfig.cvc3


let error c t cmd =
  if c = 152 then Timeout t 
  else ProverFailure (t,"command failed: " ^ cmd) 

let cvcl ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "cvcl < %s" f in
  let t,c,out = timed_sys_command debug timeout cmd in
  if c <> 0 then error c t cmd
  else if Sys.command (sprintf "grep -q -w -i Error %s" out) = 0 then
    ProverFailure(t,"command failed: " ^ cmd ^ "\n" ^ file_contents out)
  else
    let r=
      let c = Sys.command (sprintf "grep -q -w Valid %s" out) in
      if c = 0 then Valid t
      else 
	let c = Sys.command (sprintf "grep -q -w Unknown %s" out)  in
	if c = 0 then 
	  CannotDecide(t,Some (file_contents out)) 
	else
	  Invalid (t, Some (file_contents out))
    in
    remove_file ~debug out;
    r

(*
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
	  CannotDecide (t,Some (file_contents out)) 
	else
	  ProverFailure(t,"command failed: " ^ cmd ^ "\n" ^ file_contents out)
    in
    remove_file ~debug out;
    r
*)


(**
   Graph is an interface which aims at recursively calling 
   the hypotheses_filtering module if needed.
   
   @param timeout is the global timeout for the proof
   @param f : is the name of the input file which contains the proof obligation

   For the moment, the proof obligation is stored as a why file. 
   
   The first part try to check whether the formula f is valid by 
   discharging it into simplify in a timeout set to timeout/4.
   The function exits when the result is valid, unknown or not valid.

   Otherwise, the function enters in a second step.
   The hypotheses_filtering module is  
   called with with a depth that increases, provided 
   the result returned by the prover is not_valid or unknown.
   Face to a timeout result, the prover is called again with the same PO but 
   with a longer timeout.
**)
let generic_hypotheses_selection  ?(debug=false) ?(timeout=10) ~filename:f p () =
  let pruning_hyp = 3 in 
  let last_dot_index = String.rindex f '.' in 
  let option, prover, file_for_prover = 
    match p with
      | DpConfig.Simplify ->
	  "simplify", DpConfig.simplify, (String.sub f  0 last_dot_index) ^ "_why.sx" 
      | DpConfig.Gappa ->
	  "gappa", DpConfig.gappa, (String.sub f  0 last_dot_index) ^ "_why_po_1.gappa" 
      | _ -> assert false (* TODO *)
  in 
  let cmd = sprintf "why --%s --no-pervasives %s " option f in
  let t'= 
    (float_of_int timeout) /. (float_of_int (pruning_hyp +1)) in
  let t'',_c,_out = timed_sys_command ~debug (int_of_float t') cmd in
(*
  let cmd = sprintf "Simplify %s"  f_for_simplify in
  let t'',c,out = timed_sys_command ~debug (int_of_float (t' -. t'')) cmd in
  let result_sort t'' out  = 
    if Sys.command (sprintf "grep -q -w Valid %s" out) = 0 then
      Valid t''
    else
      if Sys.command (sprintf "grep -q -w Invalid %s" out) = 0 then
	CannotDecide (t'',Some (file_contents out))
      else
	ProverFailure
	  (t'',"command failed: " ^ cmd ^ "\n" ^ file_contents out) in
*)
  let r =
    gen_prover_call ~debug ~timeout:(int_of_float (t' -. t''))
      ~filename:file_for_prover prover
  in
(*
  if c == 0 then 
    let r = result_sort t'' out in
    remove_file ~debug out;
    r
  else 
*)
  match r with 
    | Valid _ -> r
    | _ ->
    let t = ref 0.0 in 
    let c = ref 0 in 
    let vb = ref 0 in
    let pb = ref 1 in
    let explicitRes = ref true in
    let r = ref (Valid 0.0) in 
    while ( !c == 0 && !explicitRes  &&  !t < float_of_int timeout) 
    
    (**** UPDATE THIS WITH A LOOP OVER PB AS DONE IN THE ARTICLE CouchotHubert07**)

    do
      (* compute the new proof obligation *)
      let cmd = sprintf "why --%s --no-pervasives --prune-hyp %d %d %s " option !pb !vb f  in
      let t'',_c',_out = timed_sys_command ~debug (int_of_float t') cmd in
    
(*
      let cmd = sprintf "Simplify %s"  f_for_simplify in
      let t'',c',out = timed_sys_command ~debug (int_of_float (t' -. t'')) cmd in
*)
      r :=
	gen_prover_call ~debug ~timeout:(int_of_float (t' -. t''))
	  ~filename:file_for_prover prover  ;
(*
      t :=  !t +. t'';
      c := c';
      r := result_sort t'' out ;
      vb := !vb+1 ;
*)
      explicitRes := match !r with 
	| Valid _ | Timeout _ | ProverFailure _  -> false 
	| Invalid (t'',_) | CannotDecide ( t'',_) ->
	    t :=  !t +. t'';
	    vb := !vb+1 ;
(*
  c := c';
  r := result_sort t'' out ;
*)    
	    true ;
	 
    done;
    
(*
    let res  = 
      if !t >= float_of_int timeout then 
	error !c (float_of_int timeout) cmd
      else 
	if !c != 0 then 
	  error !c (float_of_int timeout) cmd
	else
	  !r in
    res
*)
      !r
	  
      
    


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
	if Sys.command (sprintf "grep -q -w sat %s" out) = 0 then
	  Invalid (t, None)
	else
	  ProverFailure(t,"command failed: " ^ cmd)
    in
    (*remove_file ~debug out;*)
    r

(*
let yices ?(debug=false) ?(timeout=30) ~filename:f () =
  let cmd = sprintf "yices  -pc 0 -smt < %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then 
    if c==1 && 
      Sys.command (sprintf "grep -q -w 'feature not supported' %s" out) = 0 then
	ProverFailure(t,"command failed: " ^ cmd)
    else	
      error c t cmd
  else 
    let r = 
      if Sys.command (sprintf "grep -q -w unsat %s" out) = 0 then
	Valid t
      else
	if Sys.command (sprintf "grep -q -w unknown %s" out) = 0 then
	CannotDecide (t, None)
      else
	ProverFailure(t,"command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r
*)

(*
let cvc3 ?(debug=false) ?(timeout=30) ~filename:f () =
  let cmd = 
    sprintf "cvc3 -lang smt < %s" f 
  in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then 
    if c==1 && 
      Sys.command (sprintf "grep -q -w 'feature not supported' %s" out) = 0 then
	ProverFailure(t,"command failed: " ^ cmd)
    else	
      error c t cmd
  else 
    let r = 
      if Sys.command (sprintf "grep -q -w unsat %s" out) = 0 then
	Valid t
      else if Sys.command (sprintf "grep -q -w sat %s" out) = 0 then
	CannotDecide (t, None)
      else if Sys.command (sprintf "grep -q -w unknown %s" out) = 0 then
	CannotDecide (t, None)
      else
	ProverFailure(t,"command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r
*)

(*
let z3 ?(debug=false) ?(timeout=30) ~filename:f () =
  let cmd = sprintf "z3 -smt %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
(*
  if c <> 0 then 
    if c==1 && 
      Sys.command (sprintf "grep -q -w 'feature not supported' %s" out) = 0 then
	ProverFailure(t,"command failed: " ^ cmd)
    else	
      error c t cmd
  else 
*)
    let r = 
      if Sys.command (sprintf "grep -q -w unsat %s" out) = 0 then
	Valid t
      else
	if Sys.command (sprintf "grep -q -w unknown %s" out) = 0 then
	CannotDecide (t, None)
      else
	ProverFailure(t,"command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r
*)

let harvey ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "rvc %s" f in
  let t,c,_out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then (error c t cmd)
  else begin
    let f = Filename.chop_suffix f ".rv" in
    let fi = f ^ "-0"  ^ ".baf" in
    let cmd = sprintf "rv   %s" fi in
    let t,c,out = timed_sys_command ~debug timeout cmd in
    if c <> 0 then (error c t cmd)
    else
      let r =
	if Sys.command 
	  (sprintf "grep  -q -w \"is valid\" %s " out) = 0 then
	    Valid t
	else
	  if Sys.command 
	    (sprintf "grep  -q -w \"cannot be decided\" %s " out) = 0 
	  then
	    CannotDecide (t, None)
	  else
	    ProverFailure(t,"command failed: " ^ cmd)
      in
      remove_file ~debug out;
      r
  end
 




 
	      
	

let zenon ?(debug=false) ?(timeout=10) ~filename:f () =
  let cmd = sprintf "zenon %s" f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> 0 then error c t cmd
  else 
    let r =
      if Sys.command (sprintf "grep -q PROOF-FOUND %s" out) = 0 then
	Valid t
      else
	ProverFailure(t,"command failed: " ^ cmd)
    in
    remove_file ~debug out;
    r
