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

(*i $Id: coptions.ml,v 1.8 2004-03-02 13:42:28 filliatr Exp $ i*)

(*s The log file *)

let c = ref stdout

let log =
  c := open_out "caduceus.log";
  Format.formatter_of_out_channel !c

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
    let p = Filename.concat Cversion.libdir "why" in
    Format.fprintf log 
      "CADUCEUSLIB is not set, using %s as default@." p;
    p

(*s command-line options *)

let parse_only = ref false
let type_only = ref false
let cpp_command = ref "gcc -E -C"
let cpp_dump = ref false
let with_cpp = ref true
let debug = ref false
let verbose = ref false
let werror = ref false

let files = Queue.create ()
let add_file f = Queue.add f files

let _ = 
  Arg.parse 
      [ "-parse-only", Arg.Set parse_only, 
	  "  stops after parsing";
        "-type-only", Arg.Set type_only, 
	  "  stops after typing";
        "-no-cpp", Arg.Clear with_cpp, 
	  "  no C preprocessor";
        "-ccp", Arg.String ((:=) cpp_command), 
	  " <cmd>  sets the C preprocessor";
	"-E", Arg.Set cpp_dump,
	  "  stops after pre-processing and dump pre-processed file";
	"-d", Arg.Set debug,
          "  debugging mode";
	"-v", Arg.Set verbose,
          "  verbose mode";
	"--werror", Arg.Set werror,
          "  treats warnings as errors";
      ]
      add_file "caduceus [options] file..."

let parse_only = !parse_only
let type_only = !type_only
let debug = !debug
let verbose = !verbose
let werror = !werror
let with_cpp = !with_cpp
let cpp_command = !cpp_command
let cpp_dump = !cpp_dump

