(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
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

(*i $Id: jc_options.ml,v 1.10 2007-09-24 12:04:53 romain Exp $ i*)

open Format

(*s The log file *)

let c = ref stdout

let log =
  c := open_out "jessie.log";
  Format.formatter_of_out_channel !c

let lprintf s = Format.fprintf log s

let close_log () =
  lprintf "End of log.@.";
  close_out !c;
  c := stdout

(*s environment variables *)

let libdir = 
  try
    let v = Sys.getenv "JESSIELIB" in
    lprintf "JESSIELIB is set to %s@." v;
    v
  with Not_found -> 
    let p = Jc_version.libdir in
    lprintf "JESSIELIB is not set, using %s as default@." p;
    p

let libfile = "jessie.why"

(*s command-line options *)

let parse_only = ref false
let type_only = ref false
let print_graph = ref false
let debug = ref false
let verbose = ref false
let werror = ref false
let why_opt = ref ""

type inv_sem = InvNone | InvOwnership | InvArguments
let inv_sem = ref InvOwnership

let add_why_opt s = why_opt := !why_opt ^ " " ^ s

let annot_infer = ref false
let ai_domain = ref ""
let main = ref ""

let files_ = ref []
let add_file f = files_ := f :: !files_
let files () = List.rev !files_

let version () = 
  Printf.printf "This is Jessie version %s, compiled on %s
Copyright (c) 2006 - Claude March�
This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)
" Jc_version.version Jc_version.date;
  exit 0

let usage = "jessie [options] files"

let _ = 
  Arg.parse 
      [ "-parse-only", Arg.Set parse_only, 
	  "  stops after parsing";
        "-type-only", Arg.Set type_only, 
	  "  stops after typing";
        "-print-call-graph", Arg.Set print_graph, 
	  "  stops after call graph and print call graph";
        "-d", Arg.Set debug,
          "  debugging mode";
        "-why-opt", Arg.String add_why_opt,
	  "  <why options>  passes options to Why";
	"-v", Arg.Set verbose,
          "  verbose mode";
	"-q", Arg.Clear verbose,
          "  quiet mode (default)";
	"-ai", Arg.Tuple [
	  Arg.String (fun s -> ai_domain := s); 
	  Arg.Set annot_infer],
          "  <box,oct,pol,wp,boxwp,octwp,polwp> performs annotation inference"
          ^ " with abstract interpretation using the Box, Octagon"
          ^ " or Polyhedron domain, or with weakest preconditions or with both";
	"-main", Arg.Set_string(main),
	  "  main function";
	"--werror", Arg.Set werror,
          "  treats warnings as errors";
	"--version", Arg.Unit version,
          "  prints version and exit";
	"-inv-sem", Arg.String
	  (function
	     | "none" -> inv_sem := InvNone
	     | "ownership" -> inv_sem := InvOwnership
	     | "arguments" -> inv_sem := InvArguments
	     | s -> raise (Arg.Bad ("Unknown mode: "^s))),
	  "  <kind>  sets the semantics of invariants (available modes: none, ownership, arguments)";
      ]
      add_file usage

let usage () =
  eprintf "usage: %s@." usage;
  exit 2

let parse_only = !parse_only
let type_only = !type_only
let print_graph = !print_graph
let debug = !debug
let verbose = !verbose
let werror = !werror
let why_opt = !why_opt
let inv_sem = !inv_sem

let annot_infer = !annot_infer
let ai_domain = !ai_domain
let main = !main

(*s error handling *)

exception Jc_error of Loc.position * string

let parsing_error l f = 
  Format.ksprintf 
    (fun s -> 
       let s = if s="" then s else " ("^s^")" in
       raise (Jc_error(l, "syntax error" ^ s))) f


(*
Local Variables: 
compile-command: "unset LANG; make -C .. bin/jessie.byte"
End: 
*)
