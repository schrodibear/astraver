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

(*i $Id: cmain.ml,v 1.19 2004-03-17 10:36:18 marche Exp $ i*)

open Format
open Coptions
open Cerror
open Creport

let interp_file f =
  let ppf = Cpp.cpp f in
  let c = open_in ppf in
  let p = Clexer.parse c in
  close_in c;
  if parse_only then raise Exit;
  let p = Ctyping.type_file p in
  if type_only then raise Exit;
  Ceffect.file p;
  let (why,prover) = Cinterp.interp p in
  let f = Filename.chop_extension f in
  let ch = open_out (f ^ ".why") in
  Output.fprintf_why_decls (formatter_of_out_channel ch) why;
  close_out ch

let file_copy src dest =
  let cin = open_in src
  and cout = open_out dest
  and buff = String.make 1024 ' ' 
  and n = ref 0 
  in
  while n:= input cin buff 0 1024; !n <> 0 do 
    output cout buff 0 !n
  done;
  close_in cin; close_out cout

let main () = 
  if not (parse_only || type_only || cpp_dump) then begin
    let theory = "caduceus.why" in
    let theorysrc = Filename.concat Coptions.libdir theory in
    if not (Sys.file_exists theory) ||
      Digest.file theory <> Digest.file theorysrc
    then file_copy theorysrc theory
  end;
  Queue.iter (fun f -> try interp_file f with Exit -> ()) files
  (* engendrer les spec why *)

let rec explain_exception fmt = function
  | Parsing.Parse_error -> 
      fprintf fmt "Syntax error"
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Error (Some loc, e) | Stdpp.Exc_located (_, Error (Some loc, e)) ->
      fprintf fmt "%a%a" Loc.report loc report e
  | Stdpp.Exc_located (loc, e) ->
      fprintf fmt "%a%a" Loc.report loc explain_exception e
  | Error (_, e) ->
      report fmt e
  | e ->
      fprintf fmt "Anomaly: %s" (Printexc.to_string e)

let () =
  try
    main ()
  with e ->
    eprintf "%a@." explain_exception e;
    exit 1
