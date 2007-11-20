(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
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

(*i $Id: java_options.ml,v 1.8 2007-11-20 14:34:50 filliatr Exp $ i*)

open Format

(*s The log file *)

let c = ref stdout

let log =
  c := open_out "krakatoa.log";
  Format.formatter_of_out_channel !c

let lprintf s = Format.fprintf log s

let close_log () =
  lprintf "End of log.@.";
  close_out !c;
  c := stdout

(*s environment variables *)

let libdir = 
  try
    let v = Sys.getenv "KRAKATOALIB" in
    lprintf "KRAKATOALIB is set to %s@." v;
    v
  with Not_found -> 
    let p = Java_version.libdir in
    lprintf "KRAKATOALIB is not set, using %s as default@." p;
    p

let rec split ch s =
  try
    let i = String.index s ch in
    let h = String.sub s 0 i
    and t = String.sub s (i+1) (String.length s - i - 1)
    in
    h::(split ch t)
  with
    Not_found -> [s]
     

let libfile = "krakatoa.why"

let classpath = 
  let p =
    try
      let v = Sys.getenv "KRAKATOACLASSPATH" in
      lprintf "KRAKATOACLASSPATH is set to %s@." v;
      split ':' v
    with Not_found -> 
      let p = Filename.concat libdir "java_api" in
      lprintf "KRAKATOACLASSPATH is not set, using %s as default@." p;
      [p]
  in
  "." :: p 


(*s command-line options *)

let parse_only = ref false
let type_only = ref false
let print_graph = ref false
let debug = ref false
let verbose = ref false
let werror = ref false
let why_opt = ref ""
let ignore_overflow = ref false
let non_null = ref false

let add_why_opt s = why_opt := !why_opt ^ " " ^ s

let files_ = ref []
let add_file f = files_ := f :: !files_
let files () = List.rev !files_

let version () = 
  Printf.printf "This is Krakatoa version %s, compiled on %s
Copyright (c) 2006-2007 - ProVal INRIA project 
This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)
" Java_version.version Java_version.date;
  exit 0

let usage = "krakatoa [options] files"

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
	"-werror", Arg.Set werror,
          "  treats warnings as errors";
	"-version", Arg.Unit version,
          "  prints version and exit";
	"-ignore-overflow", Arg.Set ignore_overflow,
	  "  ignore arithmetic overflow threats" ;
	"-non-null", Arg.Set non_null,
	  "  non-null by default" ;
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
let ignore_overflow = !ignore_overflow
let non_null = !non_null

(*s error handling *)

exception Java_error of Loc.position * string

let parsing_error l f = 
  Format.ksprintf 
    (fun s -> 
       let s = if s="" then s else " ("^s^")" in
       raise (Java_error(l, "syntax error" ^ s))) f


(*
Local Variables: 
compile-command: "make -j -C .. bin/krakatoa.byte"
End: 
*)

