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



open Printf


type prover_result =
  | Valid of float
  | Invalid of float * string option
  | CannotDecide of float * string option
  | Timeout of float
  | ProverFailure of float * string

type prover = ?debug:bool ->  ?switch:string -> ?timeout:int -> 
    ?filename:string -> ?buffers:(Buffer.t list) -> unit -> prover_result

let cpulimit = ref "why-cpulimit"

(* Cygwin is nearly a true unix os but it can't use why-cpulimit.c
(setrlimit(RLIMIT_CPU) isn't implemented) and why-cpulimit-win.c
doesn't take care of stdin *)

let is_true_unix_os = Sys.os_type = "Unix"

let is_true_cygwin = Sys.os_type = "Cygwin"

let timed_sys_command ?(stdin=[]) ~debug timeout cmd =
  if debug then Format.eprintf "command line: %s@." cmd;
  if is_true_unix_os then
    begin
      let t0 = Unix.times () in
      let cmd = if timeout = 0
      then sprintf "%s 2>&1" cmd
      else sprintf "%s %d %s 2>&1" !cpulimit timeout cmd in
      let (cin,cout) as p = Unix.open_process cmd in
      List.iter (Buffer.output_buffer cout) stdin;
      close_out cout;
      let out = Lib.channel_contents cin in
      let ret = Unix.close_process p in
      let t1 = Unix.times () in
      let cpu_time = t1.Unix.tms_cutime -. t0.Unix.tms_cutime in
      if debug then Format.eprintf "Calldp : Command output : %s@." out;
      (cpu_time,ret,out)
    end
  else
    begin
      assert (stdin=[]);
      let t0 = Unix.gettimeofday () in
      let out = Filename.temp_file "out" "" in
      let cmd = if timeout = 0
      then sprintf "%s > %s 2>&1" cmd out
      else sprintf "%s %d %s > %s 2>&1" !cpulimit timeout cmd out in
      let ret = Sys.command cmd in
      let t1 = Unix.gettimeofday () in
      let cpu_time = t1 -. t0 in
      let out_content = Lib.file_contents out in
      if debug then
	Format.eprintf "Output file %s:@.%s@." out out_content
      else Lib.remove_file ~debug out;
      (cpu_time,Unix.WEXITED ret,out_content)
    end


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

let gen_prover_call ?(debug=false) ?(timeout=10) ?(switch="")
    ?filename ?buffers p =
  let cmd,(t,c,res) =
    match buffers,p.DpConfig.stdin_switch,filename with
      | None,_, Some f ->
          let cmd = sprintf "%s %s %s %s"
            p.DpConfig.command p.DpConfig.command_switches switch f
          in
          cmd,timed_sys_command ~debug timeout cmd
      | Some buffers, Some stdin_s, _ when is_true_unix_os ->
          let cmd = sprintf "%s %s %s %s"
            p.DpConfig.command p.DpConfig.command_switches switch stdin_s
          in
          cmd,timed_sys_command ~stdin:buffers ~debug timeout cmd
      | Some buffers, _, Some f ->
          let f = Filename.temp_file "" f in
          let f_in =
	    if is_true_cygwin then
	      let cin =
		Unix.open_process_in (sprintf "cygpath -am \"%s\"" f)
	      in
              let f = input_line cin in
              close_in cin;
	      f
            else f
	  in
          let cout = open_out f_in in
          List.iter (Buffer.output_buffer cout) buffers;
          close_out cout;
          let cmd = sprintf "%s %s %s %s"
            p.DpConfig.command p.DpConfig.command_switches switch f_in
          in
          let res = timed_sys_command ~debug timeout cmd in
	  Lib.remove_file ~debug f_in;
	  cmd,res
      | _ -> invalid_arg
          "Calldp.gen_prover_call : filename must be given if the prover can't use stdin"
  in
  match c with
    | Unix.WSTOPPED 24 | Unix.WSIGNALED 24 | Unix.WEXITED 124
    | Unix.WEXITED 152 ->
        (* (*128 +*) SIGXCPU signal (i.e. 24, /usr/include/bits/signum.h) *)
        if timeout = 0 then
          (* Do not handle timeout if user did not give one; give the signal 152
             to the parent process *)
          exit 152
        else Timeout t
    | Unix.WSTOPPED _ | Unix.WSIGNALED _ ->
        ProverFailure(t,"prover command " ^ cmd ^
                        " stopped abnormally with output: " ^ res)
    | Unix.WEXITED c ->
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
          ProverFailure(t,"prover command " ^ cmd ^
                          " produced unrecognized answer: " ^ res)

let gappa ?(debug=false) ?(switch="") ?(timeout=10) ~filename () =
  gen_prover_call ~debug ~switch ~timeout ~filename DpConfig.gappa

let ergo ~select_hypotheses ?(debug=false) ?(switch="") 
        ?(timeout=10) ?filename ?buffers () =
  if select_hypotheses then
    gen_prover_call ~debug ~timeout ~switch:("-select 1 " ^ switch)
      ?filename ?buffers DpConfig.alt_ergo
  else
    gen_prover_call ~debug ~timeout ~switch
      ?filename ?buffers DpConfig.alt_ergo

let coq ?(debug=false) ?(switch="") ?(timeout=10) ~filename () =
  gen_prover_call ~debug ~switch ~timeout ~filename DpConfig.coq

let pvs ?(debug=false) ?(switch="") ?(timeout=10) ~filename () =
  gen_prover_call ~debug ~switch ~timeout ~filename DpConfig.pvs

let simplify ?(debug=false) ?(switch="") ?(timeout=10) ~filename () =
  gen_prover_call ~debug ~switch ~timeout ~filename DpConfig.simplify

let vampire ?(debug=false) ?(switch="") ?(timeout=10) ~filename () =
  gen_prover_call ~debug ~switch ~timeout ~filename DpConfig.vampire

let z3 ?(debug=false) ?(switch="") ?(timeout=10) ?filename ?buffers () =
  gen_prover_call ~debug ~switch ~timeout ?filename ?buffers DpConfig.z3

let yices ?(debug=false) ?(switch="") ?(timeout=10) ?filename ?buffers () =
  gen_prover_call ~debug ~switch ~timeout ?filename ?buffers DpConfig.yices

let cvc3 ?(debug=false) ?(switch="") ?(timeout=10) ?filename ?buffers () =
  gen_prover_call ~debug ~switch ~timeout ?filename ?buffers DpConfig.cvc3


let cvcl ?(debug=false) ?(switch="") ?(timeout=10) ?filename ?buffers () =
  gen_prover_call ~debug ~switch ~timeout ?filename ?buffers DpConfig.cvcl

let verit ?(debug=false) ?(switch="") ?(timeout=10) ?filename ?buffers () =
  gen_prover_call ~debug ~switch ~timeout ?filename ?buffers DpConfig.verit

let error c t cmd =
  match c with
    | Unix.WSTOPPED 24 | Unix.WSIGNALED 24 -> Timeout t
    | _ -> ProverFailure (t,"command failed: " ^ cmd)


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
let generic_hypotheses_selection 
    ?(debug=false) ?(switch="") ?(timeout=10) ~filename:f p () =
  let pruning_hyp = 3 in
  let last_dot_index = String.rindex f '.' in
  let option, prover, file_for_prover =
    match p with
      | DpConfig.Simplify ->
	  "simplify", DpConfig.simplify, (String.sub f  0 last_dot_index) ^ "_why.sx"
      | DpConfig.Vampire ->
        "vampire", DpConfig.vampire, (String.sub f 0 last_dot_index) ^ "_why.vp"
      | DpConfig.Gappa ->
	  "gappa", DpConfig.gappa, (String.sub f  0 last_dot_index) ^ "_why_po_1.gappa"
      | _ -> assert false (* TODO *)
  in
  let cmd = sprintf "why --%s --no-pervasives %s " option f in
  let t'=
    (float_of_int timeout) /. (float_of_int (pruning_hyp +1)) in
  let t'',_c,_out = timed_sys_command ~debug (int_of_float t') cmd in
  let r =
    gen_prover_call ~debug ~switch ~timeout:(int_of_float (t' -. t''))
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
	gen_prover_call ~debug ~switch ~timeout:(int_of_float (t' -. t''))
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





let rvsat ?(debug=false) ?(switch="") ?(timeout=10) ~filename:f () =
  (*let cmd = sprintf "rv-sat %s" f in*)
  let cmd = sprintf "rv-sat %s %s" switch f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> Unix.WEXITED 0 then error c t cmd
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
    Lib.remove_file ~debug out;
    r

let harvey ?(debug=false) ?(switch="") ?(timeout=10) ~filename:f () =
  let cmd = sprintf "rvc %s %s" switch f in
  let t,c,_out = timed_sys_command ~debug timeout cmd in
  if c <> Unix.WEXITED 0 then (error c t cmd)
  else begin
    let f = Filename.chop_suffix f ".rv" in
    let fi = f ^ "-0"  ^ ".baf" in
    let cmd = sprintf "rv   %s" fi in
    let t,c,out = timed_sys_command ~debug timeout cmd in
    if c <> Unix.WEXITED 0 then (error c t cmd)
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
      Lib.remove_file ~debug out;
      r
  end









let zenon ?(debug=false) ?(switch="") ?(timeout=10) ~filename:f () =
  let cmd = sprintf "zenon %s %s" switch f in
  let t,c,out = timed_sys_command ~debug timeout cmd in
  if c <> Unix.WEXITED 0 then error c t cmd
  else
    let r =
      if Sys.command (sprintf "grep -q PROOF-FOUND %s" out) = 0 then
	Valid t
      else
	ProverFailure(t,"command failed: " ^ cmd)
    in
    Lib.remove_file ~debug out;
    r
