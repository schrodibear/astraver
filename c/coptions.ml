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

(*i $Id: coptions.ml,v 1.18 2005-03-08 10:24:53 filliatr Exp $ i*)

(*s The log file *)

let c = ref stdout

let log =
  c := open_out "caduceus.log";
  Format.formatter_of_out_channel !c

let lprintf s = Format.fprintf log s

let close_log () =
  Format.fprintf log "End of log.@.";
  close_out !c;
  c := stdout

(*s environment variables *)

let libdir = 
  try
    let v = Sys.getenv "CADUCEUSLIB" in
    Format.fprintf log "CADUCEUSLIB is set to %s@." v;
    v
  with Not_found -> 
    let p = Cversion.libdir in
    Format.fprintf log 
      "CADUCEUSLIB is not set, using %s as default@." p;
    p

let whylib =
  try
    Sys.getenv "WHYLIB"
  with Not_found -> 
    Version.libdir

(*s command-line options *)

let parse_only = ref false
let type_only = ref false
let print_norm = ref false
let cpp_command = ref "gcc -E -C"
let cpp_dump = ref false
let with_cpp = ref true
let debug = ref false
let verbose = ref false
let werror = ref false
let why_opt = ref ""
let coq_tactic = ref "intuition"
let separate = ref false
let closed_program = ref false

let files_ = ref []
let add_file f = files_ := f :: !files_
let files () = List.rev !files_

let version () = 
  Printf.printf "This is Caduceus version %s, compiled on %s
Copyright (c) 2003-2005 - Jean-Christophe Filliâtre, Thierry Hubert and Claude Marché
This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)
" Cversion.version Cversion.date;
  exit 0

type verification = All | Verify | Assume
let verification = ref All

let comma = Str.regexp "[ \t]*,[ \t]*"
let split = Str.split comma

let functions = Hashtbl.create 97

let verify s =
  separate := true;
  if !verification = Assume then begin
    Printf.eprintf "you cannot use both -verify and -assume\n"; exit 1
  end;
  verification := Verify;
  List.iter (fun f -> Hashtbl.add functions f ()) (split s)

let assume s =
  if !verification = Verify then begin
    Printf.eprintf "you cannot use both -verify and -assume\n"; exit 1
  end;
  verification := Assume;
  List.iter (fun f -> Hashtbl.add functions f ()) (split s)

let _ = 
  Arg.parse 
      [ "-parse-only", Arg.Set parse_only, 
	  "  stops after parsing";
        "-type-only", Arg.Set type_only, 
	  "  stops after typing";
        "-print-norm", Arg.Set print_norm, 
	  "  stops after normalization and print C tree";
        "-no-cpp", Arg.Clear with_cpp, 
	  "  no C preprocessor";
        "-ccp", Arg.String ((:=) cpp_command), 
	  " <cmd>  sets the C preprocessor";
	"-E", Arg.Set cpp_dump,
	  "  stops after pre-processing and dump pre-processed file";
	"-d", Arg.Set debug,
          "  debugging mode";
        "-why-opt", Arg.String ((:=) why_opt),
	  " <why options>  passes options to Why";
	"-coq-tactic", Arg.String ((:=) coq_tactic),
	  " <coq tactic>  Coq tactic for new goals";
	"-v", Arg.Set verbose,
          "  verbose mode";
	"-q", Arg.Clear verbose,
          "  quiet mode (default)";
	"--werror", Arg.Set werror,
          "  treats warnings as errors";
	"--version", Arg.Unit version,
          "  prints version and exit";
	"-s", Arg.Set separate,
	  "  a separate file for each function";
	"-verify", Arg.String verify,
	  " <f,g,h...>  specifies the functions to verify; implies -s";
	"-assume", Arg.String assume,
	  " <f,g,h...>  specifies functions not to be verified (i.e. assumed)";
	"-closed", Arg.Set closed_program,
	  "  assumes a closed program";
      ]
      add_file "caduceus [options] file..."

let parse_only = !parse_only
let type_only = !type_only
let print_norm = !print_norm
let debug = !debug
let verbose = !verbose
let werror = !werror
let with_cpp = !with_cpp
let cpp_command = !cpp_command
let cpp_dump = !cpp_dump
let why_opt = !why_opt
let coq_tactic = !coq_tactic
let separate = !separate
let closed_program = !closed_program

let verify f = match !verification with
  | All -> true
  | Verify -> Hashtbl.mem functions f
  | Assume -> not (Hashtbl.mem functions f)

