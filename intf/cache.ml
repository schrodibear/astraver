(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
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

open Options
open Marshal
open Digest

let flags = []
let max_size = ref 5000 (* maximum cache size *)
let cache = ref (Hashtbl.create 97)
let source_file = ref "/tmp/gwhy.cache"
let active = ref true
let ok = ref true

let enable () = active := true
let disable () = active := false
let is_enabled () = !active

let exists p o = 
  try 
    Queue.iter 
      (fun pr -> if p = pr then raise Exit) 
      (Hashtbl.find !cache o); 
    false
  with Exit -> true

let read_cache () = 
  try
    let in_channel = open_in !source_file in
    cache := from_channel in_channel
  with 
    | Sys_error s -> 
	print_endline ("     [...] Sys_error : "^s); 
	flush stdout
    | End_of_file -> 
	print_endline ("     [...] cache empty !"); 
	flush stdout
    | _ -> 
	print_endline ("     [...] error while loading cache !"); 
	flush stdout
	  
let fool () = Hashtbl.length !cache > !max_size 
  (* i mean fool ... cache doesn't want to do his job *)
let is_full = ref false

let load_cache source =
  source_file := source;
  if not (Sys.file_exists !source_file) then
    begin
      let xc = Sys.command ("touch " ^ source) in
      if xc <> 0 then
	begin
	  ok := false;
	  print_endline ("     [...] Error : cannot create cache file "^source^" !"); 
	  flush stdout;
	end
    end;
  if !ok then read_cache ();
  is_full := fool ()
    
let save_cache () = 
  let out_channel = open_out !source_file in
  to_channel out_channel !cache flags;
  close_out out_channel

let clear_cache () = 
  Hashtbl.clear !cache;
  save_cache ()

let remove x = Hashtbl.remove !cache x
let in_cache x = Hashtbl.mem !cache x
let find x = Hashtbl.find !cache x
let is_empty () = Hashtbl.length !cache = 0
let o_in_cache o = 
  let (_,_,seq) = o in
  in_cache seq

let add (seq:Cc.sequent) (prover:string) = 
  let o = Astprinter.clean seq in
  if not !is_full then begin
    if in_cache o then
      begin 
	if not (exists prover o) then
	  Queue.add prover (Hashtbl.find !cache o) 
      end
    else
      begin 
	let q = Queue.create () in
	let _ = Queue.add prover q in
	Hashtbl.add !cache o q;
	is_full := fool ()
      end
  end;
  save_cache () (* actually, must be done when exiting gui *)
