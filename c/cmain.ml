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

(*i $Id: cmain.ml,v 1.21 2004-03-19 11:16:07 filliatr Exp $ i*)

open Format
open Coptions
open Cerror
open Creport
open Output

let parse_file f =
  let ppf = Cpp.cpp f in
  let c = open_in ppf in
  let p = Clexer.parse c in
  close_in c;
  f, p

let type_file (f,p) = 
  (f, Ctyping.type_file p)

let interp_file (f,p) =
  let (why,prover) = Cinterp.interp p in
  let f = Filename.chop_extension f in
  let file = Lib.file "why" (f ^ ".why") in
  Pp.print_in_file (fun fmt -> Output.fprintf_why_decls fmt why) file

let file_copy src dest =
  let cin = open_in src
  and cout = open_out dest
  and buff = String.make 1024 ' ' 
  and n = ref 0 
  in
  while n := input cin buff 0 1024; !n <> 0 do 
    output cout buff 0 !n
  done;
  close_in cin; close_out cout

let main () = 
  if not (parse_only || type_only || cpp_dump) then begin
    let theory = Lib.file "why" "caduceus.why" in
    let theorysrc = Filename.concat Coptions.libdir "caduceus.why" in
    if not (Sys.file_exists theory) ||
      Digest.file theory <> Digest.file theorysrc
    then file_copy theorysrc theory
  end;
  (* parsing *)
  let pfiles = List.map parse_file (files ()) in
  if parse_only then exit 0;
  (* typing *)
  let tfiles = List.map type_file pfiles in
  if type_only then exit 0;
  (* effects *)
  List.iter (fun (_,p) -> Ceffect.file p) tfiles;
  while (not (List.for_all (fun (_,p) -> Ceffect.functions p) tfiles)) do 
    () 
  done;
  (* Why specs *)
  let file = Lib.file "why" "caduceus_spec.why" in
  Pp.print_in_file (fun fmt -> Cinterp.output_specs fmt tfiles) file;
  (* Why interpretation *)
  List.iter interp_file tfiles


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
