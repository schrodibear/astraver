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

(* open Options *) (* for ref debug *)
open Marshal
open Digest

let flags = []
let size = 5000 (* maximum cache size *)
let extention = ".cache"
let cache = ref (Hashtbl.create 97)
let source_file = ref "/tmp/gwhy.cache"
let debug = ref true

let exists p o = 
  try 
    Queue.iter 
      (fun pr -> if p = pr then raise Exit) 
      (Hashtbl.find !cache o); 
    false
  with Exit -> true

let change_debug () = 
  debug := not !debug;
  !debug

let cache_source source_file = 
  source_file ^ extention

let load_cache source =
  source_file := source;
  if not (Sys.file_exists !source_file) then
    begin
      let xc = Sys.command ("touch " ^ source) in
      if xc <> 0 then
	begin
	  debug := false;
	  print_endline ("     [...] Error : cannot create cache file "^source^" !"); 
	  flush stdout;
	end
    end;
  if !debug then
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

let clear_cache () = 
  Hashtbl.clear !cache

let save_cache () = 
  let out_channel = open_out !source_file in
  to_channel out_channel !cache flags;
  close_out out_channel

let remove = Hashtbl.remove !cache

let in_cache x = Hashtbl.mem !cache x
let find x = Hashtbl.find !cache x
let is_empty () = Hashtbl.length !cache = 0

let add (seq:Cc.sequent) (prover:string) = 
  let o = Astprinter.clean seq in
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
    end;
  save_cache () (* actually, must be done when exiting gui *)

let listing () = 
  let l = Hashtbl.length !cache in
  print_endline (string_of_int l);
  flush stdout
