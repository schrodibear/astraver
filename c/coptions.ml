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

(*i $Id: coptions.ml,v 1.6 2004-01-30 16:58:37 marche Exp $ i*)

let parse_only = ref false
let type_only = ref false
let cpp_command = ref "gcc -E -C"
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

let c = ref stdout;;
let log =
  c := open_out "caduceus.log";
  Format.formatter_of_out_channel !c
;;
let close_log () =
  Format.fprintf log "End of log.@.";
  close_out !c;
  c := stdout
;;
