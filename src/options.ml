(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
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

(*i $Id: options.ml,v 1.26 2003-09-22 21:46:11 filliatr Exp $ i*)

open Format

(*s Local refs to set the options *)

let verbose_ = ref false
let debug_ = ref false
let parse_only_ = ref false
let type_only_ = ref false
let wp_only_ = ref false
let valid_ = ref false
let coq_tactic_ = ref None
let coq_preamble_ = ref "Require Why."
let mizar_preamble_ = ref None
let werror_ = ref false

let ocaml_ = ref false
let ocaml_annot_ = ref false
let ocaml_externals_ = ref false
let output_ = ref None
let wol_ = ref false

let c_file = ref false

type coq_version = V7 | V8
type prover = Coq of coq_version | Pvs | HolLight | Mizar | Harvey | Simplify
let prover_ = ref (Coq V7)

(*s Parsing the command-line *)

let copying () =
  eprintf "\
This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License version 2, as
published by the Free Software Foundation.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

See the GNU General Public License version 2 for more details
(enclosed in the file GPL).
";
  flush stderr

let banner () =
  eprintf "\
This is why version %s, compiled on %s
Copyright (c) 2002 Jean-Christophe Filliâtre
This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)
" Version.version Version.date;
  flush stderr
  
let usage () =
  eprintf "\
Usage: why [options] [files...]

If no file is given, the source is read on standard input and
output is written in file `WhyOutput'

Generic Options:
  -h, --help     prints this message
  -V, --verbose  verbose mode
  -q, --quiet    quiet mode (default)
  -d, --debug    debugging mode (implies verbose mode)
  --werror       treat warnings as errors
  -v, --version  prints version and exits
  --warranty     prints license and exits

Typing/Annotations options:
  -p,  --parse-only  exits after parsing
  -tc, --type-only   exits after type-checking
  -wp, --wp-only     exits after annotation

Prover selection:
  --coq       selects COQ prover (default)
  --pvs       selects PVS prover
  --hol-light selects HOL Light prover
  --mizar     selects Mizar prover
  --harvey    selects haRVey prover
  --simplify  selects Simplify prover

Coq-specific options:
  --valid, 
  --no-valid  set/unset the functional validation (default is no)
  --coq-tactic <tactic> 
              gives a default tactic for new proof obligations
  --coq-preamble <text>
              gives some Coq preamble to be substituted to \"Require Why\"

Mizar-specific options:
  --mizar-preamble <text>
              gives some Mizar preamble to be inserted in the `environ' segment

Misc options:
  --ocaml        Ocaml code output
  --ocaml-annot  Show all annotations in ocaml code
  --ocaml-ext    Consider \"external\"s as parameters in ocaml code
  --output f     Redirect output to file f
";
  flush stderr

let files =
  let filesq = ref [] in
  let rec parse = function
    | [] -> List.rev !filesq
    | ("-h" | "-help" | "--help") :: _ -> usage (); exit 0
    | ("-pvs" | "--pvs") :: args -> prover_ := Pvs; parse args
    | ("-coq" | "--coq" | "-coq-v7" | "--coq-v7") :: args -> 
	prover_ := Coq V7; parse args
    | ("-coq-v8" | "--coq-v8") :: args -> prover_ := Coq V8; parse args
    | ("-hol-light" | "--hol-light") :: args -> prover_ := HolLight; parse args
    | ("-mizar" | "--mizar") :: args -> prover_ := Mizar; parse args
    | ("-harvey" | "--harvey") :: args -> prover_ := Harvey; parse args
    | ("-simplify" | "--simplify") :: args -> prover_ := Simplify; parse args
    | ("-d"|"--debug") :: args -> verbose_ := true; debug_ := true; parse args
    | ("-p" | "--parse-only") :: args -> parse_only_ := true; parse args
    | ("-tc" | "--type-only") :: args -> type_only_ := true; parse args
    | ("-wp" | "--wp-only") :: args -> wp_only_ := true; parse args
    | ("-q" | "--quiet") :: args -> verbose_ := false; parse args
    | ("-v" | "-version" | "--version") :: _ -> banner (); exit 0
    | ("-warranty" | "--warranty") :: _ -> copying (); exit 0
    | ("-V" | "--verbose") :: args -> verbose_ := true; parse args
    | ("-valid" | "--valid") :: args -> valid_ := true; parse args
    | ("-novalid" | "--no-valid") :: args -> valid_ := false; parse args
    | ("-coqtactic" | "--coqtactic" | "-coq-tactic" | "--coq-tactic") 
      :: s :: args -> coq_tactic_ := Some s; parse args
    | ("-coqtactic" | "--coqtactic" | "-coq-tactic" | "--coq-tactic") :: [] ->
	usage (); exit 1
    | ("-coqpreamble" | "--coqpreamble" | "-coq-preamble" | "--coq-preamble") 
      :: s :: args -> coq_preamble_ := s; parse args
    | ("-coqpreamble"|"--coqpreamble"|"-coq-preamble"|"--coq-preamble")::[] ->
	usage (); exit 1
    | ("-mizarpreamble" | "--mizarpreamble" | 
       "-mizar-preamble" | "--mizar-preamble") 
      :: s :: args -> mizar_preamble_ := Some s; parse args
    | ("-mizarpreamble" | "--mizarpreamble" | 
       "-mizar-preamble"|"--mizar-preamble") :: [] ->
	usage (); exit 1
    | ("--ocaml" | "-ocaml") :: args -> ocaml_ := true; parse args
    | ("--ocaml-annot" | "-ocaml-annot") :: args -> 
	ocaml_annot_ := true; parse args
    | ("--ocaml-ext" | "-ocaml-ext") :: args -> 
	ocaml_externals_ := true; parse args
    | ("-o" | "-output" | "--output") :: f :: args -> 
	output_ := Some f; parse args
    | ("-o" | "-output" | "--output") :: [] -> 
	usage (); exit 1
    | ("--wol") :: args ->
	wol_ := true; parse args
    | ("-werror" | "--werror") :: args ->
	werror_ := true; parse args
    | f :: args -> filesq := f :: !filesq; parse args
  in
  parse (List.tl (Array.to_list Sys.argv))

(*s Finally, we dereference all the refs *)

let verbose = !verbose_
let debug = !debug_
let parse_only = !parse_only_
let type_only = !type_only_
let wp_only = !wp_only_
let prover = !prover_
let valid = !valid_
let coq_tactic = !coq_tactic_
let coq_preamble = !coq_preamble_
let mizar_preamble = !mizar_preamble_
let wol = !wol_
let werror = !werror_

let ocaml = !ocaml_
let ocaml_annot = !ocaml_annot_
let ocaml_externals = !ocaml_externals_

let output o = match !output_ with
  | None -> 
      o Format.std_formatter
  | Some f -> 
      let cout = open_out f in
      let fmt = Format.formatter_of_out_channel cout in
      o fmt;
      Format.pp_print_flush fmt ();
      close_out cout

let if_verbose f x = if verbose then f x
let if_verbose_2 f x y = if verbose then f x y
let if_verbose_3 f x y z = if verbose then f x y z

let if_debug f x = if debug then f x
let if_debug_2 f x y = if debug then f x y
let if_debug_3 f x y z = if debug then f x y z

(* GUI *)

let gui = ref false
