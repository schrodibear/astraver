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

(*i $Id: coptions.ml,v 1.4 2003-12-23 15:11:00 filliatr Exp $ i*)

let parse_only = ref false
let type_only = ref false
let cpp_command = ref "gcc -E -C"
let with_cpp = ref true
let debug = ref false
let verbose = ref false

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
          "  verbose mode" ]
      add_file "caduceus [options] file..."

let parse_only = !parse_only
let type_only = !type_only
let debug = !debug
let verbose = !verbose
let with_cpp = !with_cpp
let cpp_command = !cpp_command
