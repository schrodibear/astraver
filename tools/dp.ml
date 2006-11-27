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

(*i $Id: dp.ml,v 1.31 2006-11-27 14:59:26 marche Exp $ i*)

(* script to call automatic provers *)

open Format
open Calldp

let timeout = ref 10
let eclauses = ref 2000 (* E prover max nb of clauses *)
let debug = ref false
let files = Queue.create ()

let spec = 
  [ "-timeout", Arg.Int ((:=) timeout), "<int>  set the timeout (in seconds)";
    "-eclauses", Arg.Int ((:=) eclauses), 
    "<int>  set the max nb of clauses for the E prover";
    "-debug", Arg.Set debug, "set the debug flag" ]
let usage = "usage: dp [options] files.{why,rv,znn,cvc,cvc.all,sx,sx.all,smt,smt.all}"
let () = Arg.parse spec (fun s -> Queue.push s files) usage 

let () = 
  Cvcl_split.debug := !debug; 
  Simplify_split.debug := !debug;
  Zenon_split.debug := !debug

(* stats *)
let nvalid = ref 0
let tvalid = ref 0.0
let tmaxvalid = ref 0.0
let ninvalid = ref 0
let tinvalid = ref 0.0
let tmaxinvalid = ref 0.0
let tmaxunknown = ref 0.0
let ntimeout = ref 0
let nunknown = ref 0
let tunknown = ref 0.0
let ttimeout = ref 0.0

let is_valid t = 
  printf "."; incr nvalid; 
  tvalid := !tvalid +. t;
  tmaxvalid := max !tmaxvalid t

let is_invalid t = 
  printf "*"; incr ninvalid; 
  tinvalid := !tinvalid +. t;
  tmaxinvalid := max !tmaxinvalid t

let is_unknown t = 
  printf "?"; incr nunknown; 
  tunknown := !tunknown +. t;
  tmaxunknown := max !tmaxunknown t

let is_timeout t = 
  printf "#"; incr ntimeout;
  ttimeout := !ttimeout +. t


let wrapper r = 
  begin match r with
    | Valid t -> is_valid t
    | Invalid(t,_) -> is_invalid t
    | CannotDecide t -> is_unknown t
    | Timeout t -> is_timeout t
    | ProverFailure _ -> printf "!"
  end;
  flush stdout

let call_ergo f = 
  wrapper (Calldp.ergo ~debug:!debug ~timeout:!timeout ~filename:f ())
let call_cvcl f = 
  wrapper (Calldp.cvcl ~debug:!debug ~timeout:!timeout ~filename:f ())
let call_simplify f = 
  wrapper (Calldp.simplify ~debug:!debug ~timeout:!timeout ~filename:f ())
let call_yices f = 
  wrapper (Calldp.yices ~debug:!debug ~timeout:!timeout ~filename:f ())
let call_rvsat f = 
  wrapper (Calldp.rvsat ~debug:!debug ~timeout:!timeout ~filename:f ())
let call_zenon f = 
  wrapper (Calldp.zenon ~debug:!debug ~timeout:!timeout ~filename:f ())
let call_harvey f = 
  List.iter wrapper 
    (Calldp.harvey ~debug:!debug ~timeout:!timeout 
       ~eclauses:!eclauses ~filename:f ())


let split f =
  printf "%-30s: " f; flush stdout;
  let oldv = !nvalid in
  let oldi = !ninvalid in
  let oldt = !ntimeout in
  let oldu = !nunknown in
  if Filename.check_suffix f ".smt"  || Filename.check_suffix f ".smt.all" then
    begin
      Smtlib_split.iter call_yices f 
    end 
  else
  if Filename.check_suffix f ".why" then
    begin
      Ergo_split.iter call_ergo f 
    end
  else 
  if Filename.check_suffix f ".cvc"  || Filename.check_suffix f ".cvc.all" then
    Cvcl_split.iter call_cvcl f 
  else 
  if Filename.check_suffix f ".sx" || 
     Filename.check_suffix f ".sx.all" ||
     Filename.check_suffix f ".simplify"
  then
    Simplify_split.iter call_simplify f 
  else 
  if Filename.check_suffix f ".znn" || Filename.check_suffix f ".znn.all" then
    Zenon_split.iter call_zenon f (* TODO: Zenon_split *)
  else 
  if Filename.check_suffix f ".rv" then
    call_harvey f 
  else 
    begin Arg.usage spec usage; exit 1 end;
  printf 
    " (%d/%d/%d/%d)@." (!nvalid - oldv) (!ninvalid - oldi) (!nunknown - oldu) (!ntimeout - oldt)
    
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
  if Queue.is_empty files then begin Arg.usage spec usage; exit 1 end;
  let wctime0 = Unix.gettimeofday() in
  printf "(. = valid * = invalid ? = unknown # = timeout ! = failure)@."; 
  Queue.iter split files;
  let wctime = Unix.gettimeofday() -. wctime0 in
  let n = !nvalid + !ninvalid + !ntimeout + !nunknown in
  if n = 0 then exit 0;
  let pvalid = 100. *. float !nvalid /. float n in
  let pinvalid = 100. *. float !ninvalid /. float n in
  let ptimeout = 100. *. float !ntimeout /. float n in
  let punknown = 100. *. float !nunknown /. float n in
  printf 
"total           : %3d
valid           : %3d (%3.0f%%)
invalid         : %3d (%3.0f%%)
unknown         : %3d (%3.0f%%)
timeout/failure : %3d (%3.0f%%)\n" 
    (!nvalid + !ninvalid + !nunknown + !ntimeout)
    !nvalid pvalid !ninvalid pinvalid !nunknown punknown !ntimeout ptimeout;
  printf
"total wallclock time : %a
total CPU time       : %a
valid VCs:
    max CPU time     : %.2f
    average CPU time : %.2f
invalid VCs:
    average CPU time : %.2f
    max CPU time     : %.2f
unknown VCs:
    average CPU time : %.2f
    max CPU time     : %.2f\n"
    print_time wctime
    print_time  (!tvalid +. !tinvalid +. !ttimeout)
    (!tvalid /. float !nvalid)
    !tmaxvalid
    (!tinvalid /. float !ninvalid)
    !tmaxinvalid
      (!tunknown /. float !nunknown)
    !tmaxunknown;


  try Sys.remove "out" with _ -> ()

let () = Printexc.catch main ()
