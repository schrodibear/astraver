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

(*i $Id: coptions.ml,v 1.27 2006-07-05 14:51:43 filliatr Exp $ i*)

open Format

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

let zones = ref false
let parse_only = ref false
let type_only = ref false
let print_norm = ref false
let print_graph = ref false
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
let typing_predicates = ref false
let floats = ref true

type fp_rounding_mode = 
  | RM_nearest_even | RM_to_zero | RM_up | RM_down | RM_nearest_away 
  | RM_dynamic
let fp_rounding_mode = ref RM_nearest_even
let set_fp_rounding_mode = function
  | "nearest_even" -> fp_rounding_mode := RM_nearest_even
  | "to_zero" -> fp_rounding_mode := RM_to_zero
  | "up" -> fp_rounding_mode := RM_up
  | "down" -> fp_rounding_mode := RM_down
  | "nearest_away" -> fp_rounding_mode := RM_nearest_away
  | _ -> 
      Printf.eprintf "rounding mode should be nearest_even, to_zero, up, down, or nearest_away"; exit 1
let fp_overflow_check = ref false

let int_overflow_check = ref false

let char_size_ = ref 8
let short_size_ = ref 16
let int_size_ = ref 32
let long_size_ = ref 32
let long_long_size_ = ref 64

let min_signed_char_ = ref "-128"
let max_signed_char_ = ref "127"
let max_unsigned_char_ = ref "255"
let min_signed_short_ = ref "-32768"
let max_signed_short_ = ref "32767"
let max_unsigned_short_ = ref "65535"
let min_signed_int_ = ref "-2147483648"
let max_signed_int_ = ref "2147483647"
let max_unsigned_int_ = ref "4294967295"
let min_signed_long_ = ref "-2147483648"
let max_signed_long_ = ref "2147483647"
let max_unsigned_long_ = ref "4294967295"
let min_signed_longlong_ = ref "-9223372036854775808"
let max_signed_longlong_ = ref "9223372036854775807"
let max_unsigned_longlong_ = ref "18446744073709551615"

let set_integer_size r s = 
  if s < 1 || s > 64 then begin
    eprintf "invalid integer size: %d (should be with 1..64)@." s; exit 1
  end;
  r := s

let add_why_opt s = why_opt := !why_opt ^ " " ^ s

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
        "-print-call-graph", Arg.Set print_graph, 
	  "  stops after call graph and print call graph";
        "-no-cpp", Arg.Clear with_cpp, 
	  "  no C preprocessor";
        "-ccp", Arg.String ((:=) cpp_command), 
	  " <cmd>  sets the C preprocessor";
	"-E", Arg.Set cpp_dump,
	  "  stops after pre-processing and dump pre-processed file";
	"-d", Arg.Set debug,
          "  debugging mode";
        "-why-opt", Arg.String add_why_opt,
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
	"-separation", 
	  Arg.Unit(fun () -> zones := true; closed_program := true),
	  "  separates pointers into several zones (implies -closed)";
	"--no-fp", Arg.Clear floats,
	  "  do not use floating-point arithmetic";
	"--fp-rounding-mode", Arg.String set_fp_rounding_mode,
	  "  set the default FP rounding mode";
	"--fp-overflow", Arg.Set fp_overflow_check,
	  "  check for FP overflows";
	"--int-overflow", Arg.Set int_overflow_check,
	  "  check for integer overflows";
	"--char_size", Arg.Int (set_integer_size char_size_),
	  "  set the size of type `char' (default is 8)";
	"--short_size", Arg.Int (set_integer_size short_size_),
	  "  set the size of type `short' (default is 16)";
	"--int_size", Arg.Int (set_integer_size int_size_),
	  "  set the size of type `int' (default is 32)";
	"--long_size", Arg.Int (set_integer_size long_size_),
	  "  set the size of type `long' (default is 32)";
	"--long_long_size", Arg.Int (set_integer_size long_long_size_),
	  "  set the size of type `long long' (default is 64)";
	"--typing-predicates", Arg.Set typing_predicates,
	  "  use typing predicates (experimental)";
      ]
      add_file "caduceus [options] file..."

let zones = !zones
let parse_only = !parse_only
let type_only = !type_only
let print_norm = !print_norm
let print_graph = !print_graph
let debug = !debug
let verbose = !verbose
let werror = !werror
let with_cpp = !with_cpp
let cpp_command = !cpp_command
let cpp_dump = !cpp_dump
let coq_tactic = !coq_tactic
let separate = !separate
let closed_program = !closed_program
let typing_predicates = !typing_predicates

let floats = !floats
let fp_overflow_check = !fp_overflow_check
let dft_fp_rounding_mode = !fp_rounding_mode

let char_size = !char_size_
let short_size = !short_size_
let int_size = !int_size_
let long_size = !long_size_
let long_long_size = !long_long_size_

let int_overflow_check = !int_overflow_check
let min_signed_char = !min_signed_char_
let max_signed_char = !max_signed_char_
let max_unsigned_char = !max_unsigned_char_
let min_signed_short = !min_signed_short_
let max_signed_short = !max_signed_short_
let max_unsigned_short = !max_unsigned_short_
let min_signed_int = !min_signed_int_
let max_signed_int = !max_signed_int_
let max_unsigned_int = !max_unsigned_int_
let min_signed_long = !min_signed_long_
let max_signed_long = !max_signed_long_
let max_unsigned_long = !max_unsigned_long_
let min_signed_longlong = !min_signed_longlong_
let max_signed_longlong = !max_signed_longlong_
let max_unsigned_longlong = !max_unsigned_longlong_

let use_floats = ref false

let why_opt () = 
  let o = !why_opt in
  (*let o = if int_overflow_check then o ^ " --lib-file marith.why" else o in*)
  if floats && !use_floats then o ^ " --fp" else o

let verify f = match !verification with
  | All -> true
  | Verify -> Hashtbl.mem functions f
  | Assume -> not (Hashtbl.mem functions f)

