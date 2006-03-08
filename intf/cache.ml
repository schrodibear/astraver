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

open Marshal
open Digest
open Astprinter

let flags = []
let size = "5000" (* maximum cache size  *)
let extention = ".cache"
let cache = ref (Hashtbl.create 97)
let source_file = ref "/tmp/gwhy.cache"
let debug = ref true

module MySet = struct

  let add set s = 
    if not (Hashtbl.mem set s) then
      Hashtbl.add set s 0

  let remove set = Hashtbl.remove set 

  let empty set = Hashtbl.length set = 0

  let create (p:string) = 
    let set = Hashtbl.create 97
    in Hashtbl.add set p 0;
    set

  let singleton set = 
    Hashtbl.length set = 1

end

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
      | Sys_error s -> print_endline ("     [...] Sys_error : "^s); flush stdout
      | _ -> ()

let in_cache = Hashtbl.mem !cache

let clear_cache () = 
  Hashtbl.clear !cache

let save_cache () = 
  let out_channel = open_out !source_file in
  to_channel out_channel !cache flags 

let remove = Hashtbl.remove !cache

let in_cache = Hashtbl.mem !cache

let is_empty () = Hashtbl.length !cache = 0

let add oblig prover = 
  let o = clean oblig in
  if Hashtbl.mem !cache oblig then
    let set = Hashtbl.find !cache oblig in
    MySet.add set prover;
    Hashtbl.replace !cache oblig set
  else 
    Hashtbl.add !cache oblig (MySet.create prover);
  save_cache () (* actually, must be addded when exiting gui *)
