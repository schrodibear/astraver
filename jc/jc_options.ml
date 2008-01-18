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

(*i $Id: jc_options.ml,v 1.19 2008-01-18 17:06:38 moy Exp $ i*)

open Format
open Jc_env
open Jc_common_options

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
let user_annot_only = ref false
let print_graph = ref false
let why_opt = ref ""

let verify = ref []

let add_why_opt s = why_opt := !why_opt ^ " " ^ s

let annot_infer = ref false
let ai_domain = ref ""
let interprocedural = ref false
let main = ref ""

let files_ = ref []
let add_file f = files_ := f :: !files_
let files () = List.rev !files_

let locs_files = ref []
let locs_table = Hashtbl.create 97

let version () = 
  Printf.printf "This is Jessie version %s, compiled on %s
Copyright (c) 2006-2007 - Romain Bardou, Claude March�, Yannick Moy, Nicolas Rousset
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
        "-user-annot-only", Arg.Set user_annot_only, 
	  "  check only user-defined annotations (i.e. safety is assumed)";
        "-print-call-graph", Arg.Set print_graph, 
	  "  stops after call graph and print call graph";
        "-d", Arg.Set debug,
          "  debugging mode";
	"-locs", Arg.String (fun f -> locs_files := f :: !locs_files),
	  "  <f> reads source locations from file f" ;

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
	"-main", Arg.Tuple [Arg.Set annot_infer; Arg.Set interprocedural; Arg.Set_string main],
	  "  main function for interprocedural abstract interpretation (needs -ai <domain>)";
	"--werror", Arg.Set werror,
          "  treats warnings as errors";
	"--version", Arg.Unit version,
          "  prints version and exit";
(*
	"-inv-sem", Arg.String
	  (function
	     | "none" -> inv_sem := InvNone
	     | "ownership" -> inv_sem := InvOwnership
	     | "arguments" -> inv_sem := InvArguments
	     | s -> raise (Arg.Bad ("Unknown mode: "^s))),
	  "  <kind>  sets the semantics of invariants (available modes: none, ownership, arguments)";
*)
	"-verify", Arg.String (function s -> verify := s::!verify), 
	  "verify only these functions";
      ]
      add_file usage

let usage () =
  eprintf "usage: %s@." usage;
  exit 2

let parse_only = !parse_only
let type_only = !type_only
let user_annot_only = !user_annot_only
let print_graph = !print_graph
let debug = !debug
let verbose = !verbose
let werror = !werror
let why_opt = !why_opt
let inv_sem = inv_sem
let separation_sem = separation_sem

let verify = !verify
let annot_infer = !annot_infer
let ai_domain = !ai_domain
let interprocedural = !interprocedural
let main = !main

(*s error handling *)

exception Jc_error of Loc.position * string

let parsing_error l f = 
  Format.ksprintf 
    (fun s -> 
       let s = if s="" then s else " ("^s^")" in
       raise (Jc_error(l, "syntax error" ^ s))) f

(*s locs table *)

let () =
  List.iter
    (fun f -> 
       let l = Rc.from_file f in
       List.iter
	 (fun (id,fs) ->
	    let (f,l,b,e,o) =
	      List.fold_left
		(fun (f,l,b,e,o) v ->
		   match v with
		     | "file", Rc.RCstring f -> (f,l,b,e,o)
		     | "line", Rc.RCint l -> (f,l,b,e,o)
		     | "begin", Rc.RCint b -> (f,l,b,e,o)
		     | "end", Rc.RCint e -> (f,l,b,e,o)
		     | _ -> (f,l,b,e,v::o))
		("",0,0,0,[]) fs
	    in
	    Hashtbl.add locs_table id (f,l,b,e,o))
	 l)
    !locs_files


(*
Local Variables: 
compile-command: "unset LANG; make -C .. bin/jessie.byte"
End: 
*)
