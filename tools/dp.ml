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

(*i $Id: dp.ml,v 1.14 2005-06-23 12:52:04 filliatr Exp $ i*)

(* script to call Simplify and CVC Lite *)

open Printf
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
let usage = "usage: dp [options] files.{cvc,cvc.all,sx,sx.all}"
let () = Arg.parse spec (fun s -> Queue.push s files) usage 

let () = 
  Cvcl_split.debug := !debug; 
  Simplify_split.debug := !debug;
  Calldp.debug := !debug

(* stats *)
let nvalid = ref 0
let ninvalid = ref 0
let ntimeout = ref 0

let is_valid () = printf "."; incr nvalid
let is_invalid () = printf "*"; incr ninvalid
let is_timeout () = printf "#"; incr ntimeout

let wrapper r = 
  begin match r with
    | Valid -> is_valid ()
    | Invalid | CannotDecide -> is_invalid ()
    | Timeout -> is_timeout ()
    | ProverFailure _ -> printf "!"
  end;
  flush stdout

let call_cvcl f = 
  wrapper (Calldp.cvcl ~timeout:!timeout ~filename:f ())
let call_simplify f = 
  wrapper (Calldp.simplify ~timeout:!timeout ~filename:f ())
let call_harvey f = 
  List.iter wrapper 
    (Calldp.harvey ~timeout:!timeout ~eclauses:!eclauses ~filename:f ())

let split f =
  printf "%s: " f; flush stdout;
  let oldv = !nvalid in
  let oldi = !ninvalid in
  let oldt = !ntimeout in
  if Filename.check_suffix f ".cvc"  || Filename.check_suffix f ".cvc.all" then
    Cvcl_split.iter call_cvcl f 
  else 
  if Filename.check_suffix f ".sx" || Filename.check_suffix f ".sx.all" then
    Simplify_split.iter call_simplify f 
  else 
  if Filename.check_suffix f ".rv" then
    call_harvey f 
  else 
    begin Arg.usage spec usage; exit 1 end;
  printf 
    " (%d/%d/%d)\n" (!nvalid - oldv) (!ninvalid - oldi) (!ntimeout - oldt);
  flush stdout

let main () = 
  if Queue.is_empty files then begin Arg.usage spec usage; exit 1 end;
  printf "(. = valid * = invalid # = timeout/failure)\n"; flush stdout;
  Queue.iter split files;
  let n = !nvalid + !ninvalid + !ntimeout in
  if n = 0 then exit 0;
  let pvalid = 100. *. float !nvalid /. float n in
  let pinvalid = 100. *. float !ninvalid /. float n in
  let ptimeout = 100. *. float !ntimeout /. float n in
  printf 
"total           : %3d
valid           : %3d (%3.0f%%)
invalid         : %3d (%3.0f%%)
timeout/failure : %3d (%3.0f%%)\n" 
    (!nvalid + !ninvalid + !ntimeout)
    !nvalid pvalid !ninvalid pinvalid !ntimeout ptimeout;
  try Sys.remove "out" with _ -> ()

let () = Printexc.catch main ()
