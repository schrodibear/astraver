(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: options.ml,v 1.8 2002-07-18 14:45:06 filliatr Exp $ i*)

open Format

(*s Local refs to set the options *)

let verbose_ = ref false
let debug_ = ref false
let parse_only_ = ref false
let type_only_ = ref false
let wp_only_ = ref false
let valid_ = ref false
let coq_tactic_ = ref None

type prover = Coq | Pvs
let prover_ = ref Coq

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
  -v, --version  prints version and exits
  --warranty     prints license and exits

Typing/Annotations options:
  -p,  --parse-only  exits after parsing
  -tc, --type-only   exits after type-checking
  -wp, --wp-only     exits after annotation

Prover options:
  --coq       selects COQ prover (default)
  --pvs       selects PVS prover
  --valid, 
  --no-valid  set/unset the functional validation (Coq only; default is no)
  --coq-tactic <tactic> 
              gives a default tactic for new proof obligations
";
  flush stderr

let files =
  let filesq = ref [] in
  let rec parse = function
    | [] -> List.rev !filesq
    | ("-h" | "-help" | "--help") :: _ -> usage (); exit 0
    | ("-pvs" | "--pvs") :: args -> prover_ := Pvs; parse args
    | ("-coq" | "--coq") :: args -> prover_ := Coq; parse args
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

let if_verbose f x = if verbose then f x
let if_verbose_2 f x y = if verbose then f x y
let if_verbose_3 f x y z = if verbose then f x y z

let if_debug f x = if debug then f x
let if_debug_2 f x y = if debug then f x y
let if_debug_3 f x y z = if debug then f x y z

