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

(*i $Id: options.ml,v 1.55 2006-02-03 15:35:49 filliatr Exp $ i*)

open Format

(*s Local refs to set the options *)

let verbose_ = ref false
let debug_ = ref false
let parse_only_ = ref false
let type_only_ = ref false
let wp_only_ = ref false
let valid_ = ref false
let coq_tactic_ = ref None
let coq_preamble_ = ref None
let pvs_preamble_ = ref None
let mizar_environ_ = ref None
let isabelle_base_theory_ = ref "Main"
let no_simplify_prelude_ = ref false
let no_cvcl_prelude_ = ref false
let simplify_typing_ = ref false
let no_harvey_prelude_ = ref false
let werror_ = ref false
let fpi_ = ref false
let dir_ = ref ""
let white_ = ref false
let black_ = ref true
let wbb_ = ref false
let lvlmax_ = ref max_int
let all_vc_ = ref false
let prelude_ = ref true
let gappa_rnd_ = ref "float < ieee_64, ne >"

type termination = UseVariant | Partial | Total
let termination_ = ref UseVariant

let ocaml_ = ref false
let ocaml_annot_ = ref false
let ocaml_externals_ = ref false
let output_ = ref None
let wol_ = ref false

let c_file = ref false

type coq_version = V7 | V8
let coq_version = match Version.coqversion with "v8" -> V8 | _ -> V7

type prover = 
  | Coq of coq_version | Pvs | HolLight | Mizar | Harvey | Simplify | CVCLite
  | SmtLib | Isabelle | Hol4 | Gappa | Dispatcher

let prover_ = ref (Coq coq_version)

(*s extracting the Mizar environ from a file *)

let environ_re = Str.regexp "[ ]*environ\\([ \t]\\|$\\)"
let begin_re = Str.regexp "[ ]*begin[ \n]"
let mizar_environ_from f =
  let buf = Buffer.create 1024 in
  let c = open_in f in
  let rec look_for_environ () =
    let s = input_line c in
    if Str.string_match environ_re s 0 then 
      read_environ () 
    else 
      look_for_environ ()
  and read_environ () =
    let s = input_line c in
    if Str.string_match begin_re s 0 then raise Exit;
    Buffer.add_string buf s;
    Buffer.add_char buf '\n';
    read_environ ()
  in
  try
    look_for_environ ()
  with End_of_file | Exit ->
    close_in c;
    Buffer.contents buf

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
Copyright (c) 2002 Jean-Christophe Filli�tre
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
  --where        prints library path and exits

Typing/Annotations/VCG options:
  -p,  --parse-only  exits after parsing
  -tc, --type-only   exits after type-checking
  -wp, --wp-only     exits after annotation
  --white            white boxes: WP calculus enters pure expressions
  --black            black boxes: WP calculus does not enter pure expressions
  --wbb              while loops as black boxes (careful: incomplete WP)
  --split n          split conditions into several pieces up to n levels
  --all-vc           outputs all verification conditions (no auto discharge)
  --partial          partial correctness
  --total            total correctness

Prover selection:
  --coq       selects COQ prover (default)
  --pvs       selects PVS prover
  --hol-light selects HOL Light prover
  --mizar     selects Mizar prover
  --harvey    selects haRVey prover
  --isabelle  selects Isabelle prover
  --hol4      selects HOL4 prover
  --simplify  selects Simplify prover
  --cvcl      selects CVC Lite prover
  --smtlib    selects the SMT-LIB format
  --gappa     selects the Gappa prover

Coq-specific options:
  --valid, 
  --no-valid  set/unset the functional validation (default is no)
  --coq-tactic <tactic> 
              gives a default tactic for new proof obligations
  --coq-preamble <text>
              gives some Coq preamble to be substituted to \"Require Why\"

PVS-specific options:
  --pvs-preamble <text>
              gives some PVS preamble to be substituted to \"importing why@@why\"

Simplify-specific options:
  --no-simplify-prelude
              suppress the Simplify prelude (BG_PUSHs for Why's symbols)
  --simplify-typing
              add typing constraints for each abstract type

Mizar-specific options:
  --mizar-environ <text>
              sets the Mizar `environ'
  --mizar-environ-from <file>
              gets Mizar `environ' from <file>

Isabelle/HOL-specific options:
  --isabelle-base-theory <theory>
              sets the Isabelle/HOL base theory

Gappa options:
  --gappa-rnd <mode>
              sets the Gappa rounding mode (e.g. float<ieee_64,ne>)

Misc options:
  --ocaml        Ocaml code output
  --ocaml-annot  Show all annotations in ocaml code
  --ocaml-ext    Consider \"external\"s as parameters in ocaml code
  --output f     Redirect output to file f
  --dir d        Output files in directory d
";
  flush stderr

let files =
  let filesq = ref [] in
  let rec parse = function
    | [] -> List.rev !filesq
    | ("-h" | "-help" | "--help") :: _ -> usage (); exit 0
    | ("-pvs" | "--pvs") :: args -> prover_ := Pvs; parse args
    | ("-coq-v7" | "--coq-v7") :: args -> prover_ := Coq V7; parse args
    | ("-coq-v8" | "--coq-v8") :: args -> prover_ := Coq V8; parse args
    | ("-coq" | "--coq") :: args -> prover_ := Coq coq_version; parse args
    | ("-hol-light" | "--hol-light") :: args -> prover_ := HolLight; parse args
    | ("-mizar" | "--mizar") :: args -> prover_ := Mizar; parse args
    | ("-harvey" | "--harvey") :: args -> prover_ := Harvey; parse args
    | ("-simplify" | "--simplify") :: args -> prover_ := Simplify; parse args
    | ("-isabelle" | "--isabelle") :: args -> prover_ := Isabelle; parse args
    | ("-hol4" | "--hol4") :: args -> prover_ := Hol4; parse args
    | ("-cvcl" | "--cvcl") :: args -> prover_ := CVCLite; parse args
    | ("-smtlib" | "--smtlib") :: args -> prover_ := SmtLib; parse args
    | ("-fpi" | "--fpi") :: args -> fpi_ := true; parse args
    | ("-gappa" | "--gappa") :: args -> prover_ := Gappa; parse args
    | ("-d"|"--debug") :: args -> verbose_ := true; debug_ := true; parse args
    | ("-p" | "--parse-only") :: args -> parse_only_ := true; parse args
    | ("-tc" | "--type-only") :: args -> type_only_ := true; parse args
    | ("-wp" | "--wp-only") :: args -> wp_only_ := true; parse args
    | ("-q" | "--quiet") :: args -> verbose_ := false; parse args
    | ("-v" | "-version" | "--version") :: _ -> banner (); exit 0
    | ("-warranty" | "--warranty") :: _ -> copying (); exit 0
    | ("-where" | "--where") :: _ -> printf "%s\n" Version.libdir; exit 0
    | ("-V" | "--verbose") :: args -> verbose_ := true; parse args
    | ("-valid" | "--valid") :: args -> valid_ := true; parse args
    | ("-novalid" | "--no-valid") :: args -> valid_ := false; parse args
    | ("-coqtactic" | "--coqtactic" | "-coq-tactic" | "--coq-tactic") 
      :: s :: args -> coq_tactic_ := Some s; parse args
    | ("-coqtactic" | "--coqtactic" | "-coq-tactic" | "--coq-tactic") :: [] ->
	usage (); exit 1
    | ("-coqpreamble" | "--coqpreamble" | "-coq-preamble" | "--coq-preamble") 
      :: s :: args -> coq_preamble_ := Some s; parse args
    | ("-coqpreamble"|"--coqpreamble"|"-coq-preamble"|"--coq-preamble")::[] ->
	usage (); exit 1
    | ("-pvspreamble" | "--pvspreamble" | "-pvs-preamble" | "--pvs-preamble") 
      :: s :: args -> pvs_preamble_ := Some s; parse args
    | ("-pvspreamble"|"--pvspreamble"|"-pvs-preamble"|"--pvs-preamble")::[] ->
	usage (); exit 1
    | ("-mizarenviron" | "--mizarenviron" | 
       "-mizar-environ" | "--mizar-environ") 
      :: s :: args -> mizar_environ_ := Some s; parse args
    | ("-mizarenviron" | "--mizarenviron" | 
       "-mizar-environ"|"--mizar-environ") :: [] ->
	usage (); exit 1
    | ("-mizarenvironfrom" | "--mizarenvironfrom" | 
       "-mizar-environ-from" | "--mizar-environ-from") 
      :: f :: args -> mizar_environ_ := Some (mizar_environ_from f); parse args
    | ("-mizarenvironfrom" | "--mizarenvironfrom" | 
       "-mizar-environ-from"|"--mizar-environ-from") :: [] ->
	usage (); exit 1
    | ("-isabelle-base-theory" | "--isabelle-base-theory") 
      :: s :: args -> isabelle_base_theory_ := s; parse args
    | ("-isabelle-base-theory" | "--isabelle-base-theory")::[] ->
	usage (); exit 1
    | ("--no-simplify-prelude" | "-no-simplify-prelude") :: args ->
	no_simplify_prelude_ := true; parse args
    | ("--simplify-typing" | "-simplify-typing") :: args ->
	simplify_typing_ := true; parse args
    | ("--no-cvcl-prelude" | "-no-cvcl-prelude") :: args ->
	no_cvcl_prelude_ := true; parse args
    | ("--no-harvey-prelude" | "-no-harvey-prelude") :: args ->
	no_harvey_prelude_ := true; parse args
    | ("--ocaml" | "-ocaml") :: args -> ocaml_ := true; parse args
    | ("--ocaml-annot" | "-ocaml-annot") :: args -> 
	ocaml_annot_ := true; parse args
    | ("--ocaml-ext" | "-ocaml-ext") :: args -> 
	ocaml_externals_ := true; parse args
    | ("-gappa-rnd" | "--gappa-rnd") :: s :: args -> 
	gappa_rnd_ := s; parse args
    | ("-gappa-rnd" | "--gappa-rnd") :: [] -> 
	usage (); exit 1
    | ("-o" | "-output" | "--output") :: f :: args -> 
	output_ := Some f; parse args
    | ("-o" | "-output" | "--output") :: [] -> 
	usage (); exit 1
    | ("--wol") :: args ->
	wol_ := true; parse args
    | ("-werror" | "--werror") :: args ->
	werror_ := true; parse args
    | ("-dir" | "--dir") :: d :: args ->
	dir_ := d; parse args
    | ("-dir" | "--dir") :: [] ->
	usage (); exit 1
    | ("-white" | "--white") :: args ->
	white_ := true; black_ := false; parse args
    | ("-black" | "--black") :: args ->
	black_ := true; white_ := false; parse args
    | ("-wbb" | "--wbb") :: args ->
        wbb_ := true; parse args
    | ("-split" | "--split") :: n :: args ->
	begin try lvlmax_ := int_of_string n with _ -> usage (); exit 1 end; 
	parse args
    | ("-split" | "--split") :: [] ->
	usage (); exit 1
    | ("-all-vc" | "--all-vc" | "--allvc") :: args ->
	all_vc_ := true; parse args
    | ("-no-prelude" | "--no-prelude") :: args ->
	prelude_ := false; parse args
    | ("-partial" | "--partial") :: args ->
	termination_ := Partial; parse args
    | ("-total" | "--total") :: args ->
	termination_ := Total; parse args
    | f :: args -> 
	filesq := f :: !filesq; parse args
  in
  parse (List.tl (Array.to_list Sys.argv))

(* Are we the GUI? (set in intf/stat.ml) *)

let gui = ref false

(*s Finally, we dereference all the refs *)

let verbose = !verbose_
let debug = !debug_
let parse_only = !parse_only_
let type_only = !type_only_
let wp_only = !wp_only_
let prover () = if !gui then Dispatcher else !prover_
let valid = !valid_
let coq_tactic = !coq_tactic_
let coq_preamble = match !coq_preamble_ with
  | None when prover () = Coq V7 -> "Require Why."
  | None -> "Require Import Why."
  | Some s -> s
let pvs_preamble = match !pvs_preamble_ with
  | None -> "importing why@why"
  | Some s -> s

let mizar_environ = !mizar_environ_
let isabelle_base_theory = !isabelle_base_theory_
let no_simplify_prelude = !no_simplify_prelude_
let no_cvcl_prelude = !no_cvcl_prelude_
let simplify_typing = !simplify_typing_
let no_harvey_prelude = !no_harvey_prelude_
let wol = !wol_
let werror = !werror_
let fpi = !fpi_
let dir = !dir_
let white = !white_
let black = !black_
let wbb = !wbb_
let lvlmax = !lvlmax_
let all_vc = !all_vc_
let termination = !termination_
let gappa_rnd = !gappa_rnd_

let file f = if dir = "" then f else Lib.file ~dir ~file:f

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

(* compatibility checks *)
let () = if fpi && valid then begin
  Printf.eprintf "options -valid and -fpi are not compatible\n";
  exit 1
end
let () = if white && black then begin
  Printf.eprintf "options -white and -black are not compatible\n";
  exit 1
end

(* prelude *)

let prelude = !prelude_

let prelude_file =
  try
    Filename.concat (Sys.getenv "WHYLIB") "prelude.why"
  with Not_found ->
    Filename.concat Version.libdir "prelude.why"

let () = 
  if prelude && not (Sys.file_exists prelude_file) then begin
    Printf.eprintf "cannot find prelude file %s\n" prelude_file;
    exit 1
  end
