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



(* script to call automatic provers *)

open Format
open Calldp

let timeout = ref 10
let eclauses = ref 2000 (* E prover max nb of clauses *)
let debug = ref false
let batch = ref false
let simple = ref false
let split = ref false
let timings = ref true (* print timings *)
let basename = ref false
let listing = ref false
let select_hypotheses = ref false
let files = Queue.create ()
let prover = ref None
let extra_switch = ref ""

type smt_solver = Yices | CVC3 | Z3 | VeriT
let smt_solver = ref Z3
let set_smt_solver = function
  | "yices" -> smt_solver := Yices
  | "cvc3" -> smt_solver := CVC3
  | "z3" -> smt_solver := Z3
  | "verit" -> smt_solver:= VeriT
  | s -> eprintf "unknown SMT solver %s@." s; exit 1

let spec =
  [ "-timeout", Arg.Int ((:=) timeout), "<int>  set the timeout (in seconds) (0 no timeout)";
    "-eclauses", Arg.Int ((:=) eclauses),
    "<int>  set the max nb of clauses for the E prover";
    "-debug", Arg.Set debug, "set the debug flag";
    "-batch", Arg.Set batch, "run in batch mode";
    "-no-timings", Arg.Clear timings, "do not display timings";
    "-smt-solver", Arg.String set_smt_solver,
      "<solver id> (yices, cvc3, z3 or verit)";
    "-basename", Arg.Set basename, "prints only file basenames";
    "-listing", Arg.Set listing, "argument file only lists real argument files";
    "-select", Arg.Set select_hypotheses,
    "applies some selection of hypotheses (only Alt-Ergo)";
    "-extra-switch", Arg.Set_string extra_switch,
    "adds additional switches to selected prover";
    "-simple", Arg.Set simple, "Print only Valid, I don't know, Invalid, Fail, Timeout";
    "-split", Arg.Set split, "Create a directory wich contains all the goal split in different file";
    "-prover", Arg.Symbol (
      ["Alt-Ergo";"CVC3";"CVCL";"Z3";"Yices";"Simplify";"Vampire"; "VeriT"],(fun s -> prover := Some s)), "Select the prover to use"
  ]

let () =
  let d = Filename.dirname Sys.argv.(0) in
  if not (Filename.is_relative d) then
    Calldp.cpulimit := Filename.concat d "why-cpulimit"

let usage = "usage: why-dp [options] [files.{why,rv,znn,cvc,cvc.all,sx,sx.all,smt,smt.all,vp,vp.all}]"
let () =
  Arg.parse spec
    (fun s ->
       if !listing then
	 let c = open_in s in
	 let rec push_file () =
	   let line = input_line c in
	   let flist = Str.split (Str.regexp "[ \t]+") line in
	   List.iter (fun f -> Queue.push f files) flist;
	   push_file ()
	 in
	 (try push_file () with End_of_file -> ());
	 close_in c
       else
	 Queue.push s files) usage

let () = if !split then simple := true

let switch = !extra_switch

(* stats *)

let nvalid = ref 0
let tvalid = ref 0.0
let tmaxvalid = ref 0.0

let ninvalid = ref 0
let tinvalid = ref 0.0
let tmaxinvalid = ref 0.0

let nunknown = ref 0
let tunknown = ref 0.0
let tmaxunknown = ref 0.0

let ntimeout = ref 0
let ttimeout = ref 0.0

let nfailure = ref 0
let tfailure = ref 0.0

let is_valid t =
  printf ".@?"; incr nvalid;
  tvalid := !tvalid +. t;
  tmaxvalid := max !tmaxvalid t

let is_invalid t =
  printf "*@?"; incr ninvalid;
  tinvalid := !tinvalid +. t;
  tmaxinvalid := max !tmaxinvalid t

let is_unknown t =
  printf "?@?"; incr nunknown;
  tunknown := !tunknown +. t;
  tmaxunknown := max !tmaxunknown t

let is_timeout t =
  printf "#@?"; incr ntimeout;
  ttimeout := !ttimeout +. t

let is_failure t =
  printf "!@?"; incr nfailure;
  tfailure := !tfailure +. t


let wrapper_complete r =
  begin match r with
    | Valid t -> is_valid t
    | Invalid(t,_) -> is_invalid t
    | CannotDecide (t,_) -> is_unknown t
    | Timeout t -> is_timeout t
    | ProverFailure(t,_) -> is_failure t
  end;
  flush stdout

let wrapper_batch r =
  begin match r with
    | Valid _t -> exit 0
    | Invalid(_t,_) -> exit 2
    | CannotDecide (_t,_) -> exit 3
    | Timeout _t -> exit 4
    | ProverFailure(_t,_) -> exit 5
  end

let wrapper_simple r =
  begin match r with
    | Valid t -> printf "Valid %f@." t
    | Invalid(t,_) -> printf "Invalid %f@." t
    | CannotDecide (t,_) -> printf "I don't know %f@." t
    | Timeout t -> printf "Timeout %f@." t
    | ProverFailure(t,s) -> printf "Fail %f@." t; eprintf "%s@." s
  end;
  flush stdout

let wrapper =
  if !batch then wrapper_batch
  else if !simple then wrapper_simple
  else wrapper_complete

let debug = !debug

let call_ergo f b =
  wrapper (Calldp.ergo ~debug ~switch ~timeout:!timeout
	     ~select_hypotheses:!select_hypotheses ~filename:f ~buffers:b ())
let call_cvcl f b =
  wrapper (Calldp.cvcl ~debug ~switch 
             ~timeout:!timeout ~filename:f ~buffers:b ())
let call_simplify f _ =
  wrapper (Calldp.simplify ~debug ~switch ~timeout:!timeout ~filename:f ())
let call_vampire f _ =
  wrapper (Calldp.vampire ~debug ~switch ~timeout:!timeout ~filename:f ())
let call_yices f b =
  wrapper (Calldp.yices ~debug ~switch 
             ~timeout:!timeout ~filename:f ~buffers:b ())
let call_cvc3 f b =
  wrapper (Calldp.cvc3 ~debug ~switch 
             ~timeout:!timeout ~filename:f ~buffers:b ())
let call_z3 f b =
  wrapper (Calldp.z3 ~debug ~switch 
             ~timeout:!timeout ~filename:f ~buffers:b ())
let call_rvsat f _ =
  wrapper (Calldp.rvsat ~debug ~switch ~timeout:!timeout ~filename:f ())
let call_zenon f _ =
  wrapper (Calldp.zenon ~debug ~switch ~timeout:!timeout ~filename:f ())
let call_harvey f _ =
  wrapper (Calldp.harvey ~debug ~switch ~timeout:!timeout ~filename:f ())
let call_verit f b =
  wrapper (Calldp.verit ~debug ~switch 
             ~timeout:!timeout ~filename:f ~buffers:b ())

let new_num =
  let c = ref (-1) in
  (fun () -> incr c;!c)

let dir_name f = (Filename.chop_extension f)^".split"

let call_split callback dir_name suffixe =
  if !split then (fun f b ->
                    let dest = (sprintf "%s/goal%i%s" dir_name (new_num ()) suffixe) in
                    match b with
                      | [] -> Lib.file_copy f dest
                      | buffers ->
                          let cout = open_out dest in
                          List.iter (Buffer.output_buffer cout) buffers;
                          close_out cout;
                 )
  else callback


let call_smt_solver = match !smt_solver with
  | Yices -> call_yices
  | CVC3 -> call_cvc3
  | Z3 -> call_z3
  | VeriT -> call_verit

let dispatch_prover_by_name cin = function
  | "Alt-Ergo" -> Ergo_split.iter call_ergo cin
  | "CVC3" -> Smtlib_split.iter call_cvc3 cin
  | "CVCL" -> Cvcl_split.iter call_cvcl cin
  | "Z3" -> Smtlib_split.iter call_z3 cin
  | "Yices" -> Smtlib_split.iter call_yices cin
  | "Simplify" -> Simplify_split.iter ~debug call_simplify cin
    (* Vampire uses Simplify's syntax. *)
  | "Vampire" -> Simplify_split.iter ~debug call_vampire cin
  | "VeriT" -> Smtlib_split.iter call_verit cin
  | _ -> assert false


let dispatch_prover_by_extension dir_name f =
  let cin = open_in f in
  if Filename.check_suffix f ".smt"  || Filename.check_suffix f ".smt.all" then
    begin
      Smtlib_split.iter (call_split call_smt_solver dir_name ".smt") cin
    end
  else
  if Filename.check_suffix f ".why" then
    begin
      Ergo_split.iter (call_split call_ergo dir_name ".why") cin
    end
  else
  if Filename.check_suffix f ".cvc"  || Filename.check_suffix f ".cvc.all" then
    Cvcl_split.iter (call_split call_cvcl dir_name ".cvc") cin
  else
  if Filename.check_suffix f ".sx" ||
     Filename.check_suffix f ".sx.all" ||
     Filename.check_suffix f ".simplify"
  then
    Simplify_split.iter ~debug (call_split call_simplify dir_name ".sx") cin
  else
  if Filename.check_suffix f ".vp" ||
     Filename.check_suffix f ".vp.all"
  then
    Simplify_split.iter ~debug (call_split call_vampire dir_name ".vp") cin
  else
  if Filename.check_suffix f ".znn" || Filename.check_suffix f ".znn.all" then
    Zenon_split.iter ~debug (call_split call_zenon dir_name ".znn") f (* TODO: Zenon_split *)
  else
  if Filename.check_suffix f ".rv" then
    begin
      Rv_split.iter ~debug (call_split call_harvey dir_name ".rv") f
    end
  else
    begin Arg.usage spec usage; exit 1 end;
  close_in cin


let split f =
  let dir_name = dir_name f in
  if !split && not (Sys.file_exists dir_name) then Unix.mkdir dir_name 0o740;
  if not !batch && not !simple then printf "%-30s: "
    (if !basename then Filename.basename f else f);
  let oldv = !nvalid in
  let oldi = !ninvalid in
  let oldt = !ntimeout in
  let oldu = !nunknown in
  let oldf = !nfailure in
  (match !prover with
    | None -> dispatch_prover_by_extension dir_name f;
    | Some p -> let cin = open_in f in
      dispatch_prover_by_name cin p;
      close_in cin);
  if not !simple then
    printf
      " (%d/%d/%d/%d/%d)@." (!nvalid - oldv) (!ninvalid - oldi) (!nunknown - oldu) (!ntimeout - oldt) (!nfailure - oldf)

let print_time fmt f =
  if f < 60.0 then fprintf fmt "%.2f sec" f else
    let t = int_of_float f in
    let m = t / 60 in
    let s = t mod 60 in
    if f < 3600.0 then fprintf fmt "%d m %02d sec" m s else
      let h = m / 60 in
      let m = m mod 60 in
      fprintf fmt "%d h %02d m %02d sec" h m s


let main () =
  begin
    try
      DpConfig.load_rc_file ()
    with Not_found ->
      print_endline "Why config file not found, please run why-config first.";
      exit 1
  end;
  let wctime0 = Unix.gettimeofday() in
  if not !batch && not !simple then printf "(. = valid * = invalid ? = unknown # = timeout ! = failure)@.";
  if Queue.is_empty files then
    match !prover with
      | None -> eprintf "Can't use stdin without the option -prover@.";
          Arg.usage spec usage;exit 1
      | Some p -> dispatch_prover_by_name stdin p
  else Queue.iter split files;
  let wctime = Unix.gettimeofday() -. wctime0 in
  let n = !nvalid + !ninvalid + !ntimeout + !nunknown + !nfailure in
  if n = 0 then exit 0;
  let pvalid = 100. *. float !nvalid /. float n in
  let pinvalid = 100. *. float !ninvalid /. float n in
  let ptimeout = 100. *. float !ntimeout /. float n in
  let punknown = 100. *. float !nunknown /. float n in
  let pfailure = 100. *. float !nfailure /. float n in
  printf
"total   : %3d
valid   : %3d (%3.0f%%)
invalid : %3d (%3.0f%%)
unknown : %3d (%3.0f%%)
timeout : %3d (%3.0f%%)
failure : %3d (%3.0f%%)\n" n
    !nvalid pvalid !ninvalid pinvalid !nunknown punknown
    !ntimeout ptimeout !nfailure pfailure;
  if !timings then printf
"total wallclock time : %a
total CPU time       : %a
valid VCs:
    average CPU time : %.2f
    max CPU time     : %.2f
invalid VCs:
    average CPU time : %.2f
    max CPU time     : %.2f
unknown VCs:
    average CPU time : %.2f
    max CPU time     : %.2f\n"
    print_time wctime
    print_time  (!tvalid +. !tinvalid +. !tunknown +. !ttimeout +. !tfailure)
    (!tvalid /. float !nvalid)
    !tmaxvalid
    (!tinvalid /. float !ninvalid)
    !tmaxinvalid
      (!tunknown /. float !nunknown)
    !tmaxunknown

let () = Printexc.catch main ()
