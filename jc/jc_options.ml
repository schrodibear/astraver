(*i $Id: jc_options.ml,v 1.1 2006-10-31 08:25:16 marche Exp $ i*)

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

(*s command-line options *)

let parse_only = ref false
let type_only = ref false
let print_graph = ref false
let debug = ref false
let verbose = ref false
let werror = ref false
let why_opt = ref ""

let add_why_opt s = why_opt := !why_opt ^ " " ^ s

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
	  " <why options>  passes options to Why";
	"-v", Arg.Set verbose,
          "  verbose mode";
	"-q", Arg.Clear verbose,
          "  quiet mode (default)";
	"--werror", Arg.Set werror,
          "  treats warnings as errors";
	"--version", Arg.Unit version,
          "  prints version and exit";
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
