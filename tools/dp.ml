(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: dp.ml,v 1.4 2004-07-15 15:09:24 filliatr Exp $ i*)

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

(* stats *)
let nvalid = ref 0
let ninvalid = ref 0
let ntimeout = ref 0

let call cmd =
  if !debug then begin eprintf "calling: %s\n" cmd; flush stderr end;
  let out = Sys.command cmd in
  if out = 0 then begin printf "valid\n"; incr nvalid end
  else if out = 1 then begin printf "invalid\n"; incr ninvalid end
  else begin printf "timeout\n"; incr ntimeout end;
  flush stdout

let call_cvcl f =
  call
    (sprintf "ulimit -t %d; cvcl < %s > out && grep -q Valid out" !timeout f)

let call_simplify f =
  call
    (sprintf "ulimit -t %d; Simplify %s > out && grep -q Valid out" !timeout f)

let split f =
  if Filename.check_suffix f ".cvc"  || Filename.check_suffix f ".cvc.all" then
    Cvcl_split.iter call_cvcl f 
  else 
  if Filename.check_suffix f ".sx" || Filename.check_suffix f ".sx.all" then
    Simplify_split.iter call_simplify f 
  else 
    begin Arg.usage spec usage; exit 1 end

let main () = 
  if Queue.is_empty files then begin Arg.usage spec usage; exit 1 end;
  Queue.iter split files;
  printf "valid = %d \t invalid = %d \t timeout = %d\n" 
    !nvalid !ninvalid !ntimeout

let () = Printexc.catch main ()
