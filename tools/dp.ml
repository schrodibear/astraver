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

(*i $Id: dp.ml,v 1.10 2005-05-25 13:03:53 filliatr Exp $ i*)

(* script to call Simplify and CVC Lite *)

open Printf

let timeout = ref 10
let debug = ref false
let files = Queue.create ()

let spec = 
  [ "-timeout", Arg.Int ((:=) timeout), "<int>  set the timeout (in seconds)";
    "-debug", Arg.Set debug, "set the debug flag" ]
let usage = "usage: dp [options] files.{cvc,cvc.all,sx,sx.all}"
let () = Arg.parse spec (fun s -> Queue.push s files) usage 

let () = Cvcl_split.debug := !debug; Simplify_split.debug := !debug

(* stats *)
let nvalid = ref 0
let ninvalid = ref 0
let ntimeout = ref 0

let is_valid () = printf "."; incr nvalid
let is_invalid () = printf "*"; incr ninvalid
let is_timeout () = printf "#"; incr ntimeout

let call cmd =
  if !debug then begin eprintf "calling: %s\n" cmd; flush stderr end;
  let out = Sys.command cmd in
  if out = 0 then is_valid ()
  else if out = 1 then is_invalid ()
  else is_timeout ();
  flush stdout

let call_cvcl f =
  call
    (sprintf "ulimit -t %d; cvcl < %s > out 2>&1 && grep -q -w Valid out" 
       !timeout f)

let call_simplify f =
  call
    (sprintf "ulimit -t %d; Simplify %s > out 2>&1 && grep -q -w Valid out" 
       !timeout f)

let call_harvey f =
  let out = Sys.command (sprintf "rvc %s > /dev/null 2>&1" f) in
  if out = 0 then begin 
    let f = Filename.chop_suffix f ".rv" in
    let rec iter i =
      let fi = f ^ "-" ^ string_of_int i ^ ".baf" in
      if Sys.file_exists fi then begin
	let out = 
	  Sys.command (sprintf "timeout %d rv %s > out 2>&1" !timeout fi) 
	in
	if out <> 0 then 
	  is_timeout ()
	else begin
	  let out = 
	    Sys.command 
	      "grep \"Proof obligation in\" out | grep -q \"is valid\"" 
	  in
	  if out = 0 then is_valid () else is_invalid ()
	end;
	flush stdout;
	iter (i+1)
      end
    in
    iter 0
  end
  else begin eprintf "rvc failed!" end

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
