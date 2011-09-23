(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



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
let coq_use_dp = ref true
let pvs_preamble_ = ref None
let mizar_environ_ = ref None
let isabelle_base_theory_ = ref "Main"
let no_simplify_prelude_ = ref false
let simplify_triggers_ = ref false
let no_cvcl_prelude_ = ref false
let no_harvey_prelude_ = ref false
let no_zenon_prelude_ = ref false
let werror_ = ref false
let dir_ = ref ""
let fast_wp_ = ref false
let white_ = ref false
let black_ = ref true
let wbb_ = ref false
let split_user_conj_ = ref false
let split_bool_op_ = ref false
let lvlmax_ = ref max_int
let all_vc_ = ref false
let eval_goals_ = ref false
let pruning_ = ref false
let pruning_hyp_v_ = {contents = -1}
let pruning_hyp_p_ = {contents = -1}
(* Heuristiques en test *)
let pruning_hyp_CompInGraph_ = ref false
let pruning_hyp_CompInFiltering_ = ref false
let pruning_hyp_LinkVarsQuantif_ = ref false
let pruning_hyp_keep_single_comparison_representation_ = ref false
let pruning_hyp_comparison_eqOnly_ = ref false
let pruning_hyp_suffixed_comparison_ = ref false
let pruning_hyp_equalities_linked_ = ref false
let pruning_hyp_arithmetic_tactic_ = ref false
let pruning_hyp_var_tactic_ = ref 0
let pruning_hyp_polarized_preds_ = ref false
let prune_context_ = ref false
let prune_coarse_pred_comp_ = ref false
let prune_get_depths_ = ref false
let pruning_hyp_considere_arith_comparison_as_special_predicate_ = ref true
(* FIN de Heuristiques en test *)
(*
let modulo_ = ref false
*)

let phantom_types = Hashtbl.create 17

let lib_files_to_load_ = ref []
let no_pervasives = ref false
let files_to_load_ = ref []
let show_time_ = ref false
let locs_files = ref []
let default_locs = ref false
let delete_old_vcs = ref false
let explain_vc = ref false
let locs_table = Hashtbl.create 97

type encoding =
  | NoEncoding | Predicates | Stratified | Recursive | Monomorph
  | SortedStratified | MonoInst

type expanding = All | Goal | NoExpanding


let types_encoding_ = ref NoEncoding (* ne pas changer svp! *)
(* let types_encoding_ = ref Stratified *)

type monoinstWorldGen =
  | MonoinstSorted
  | MonoinstBuiltin
  | MonoinstGoal
  | MonoinstPremises

let monoinstworldgen = ref MonoinstGoal
let monoinstoutput_world = ref false
let monoinstonlymem = ref false
let monoinstnounit = ref false
let monoinstonlyconst = ref false

let defExpanding_ = ref NoExpanding

type termination = UseVariant | Partial | Total
let termination_ = ref UseVariant

let ocaml_ = ref false
let ocaml_annot_ = ref false
let ocaml_externals_ = ref false
let output_ = ref None
let wol_ = ref false

let c_file = ref false

type coq_version = V7 | V8 | V81
let coq_version =
  match Version.coqversion with "v8" -> V8 | "v8.1" -> V81 | _ -> V7

type prover =
  | Coq of coq_version | Pvs | HolLight | Mizar | Harvey | Simplify | CVCLite
  | SmtLib | Isabelle | Hol4 | Gappa | Zenon | Z3 | Vampire
  | Ergo | Why | MultiWhy | MultiAltergo | Why3 | Dispatcher | WhyProject

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

(*s GUI settings *)

(* Are we the GUI? (set in intf/stat.ml) *)
let gui = ref false

(* GUI project (set in src/main.ml) *)
let gui_project = ref None


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
Copyright (c) 2002-2011 CNRS/INRIA/Univ Paris 11, team ProVal
This is free software with ABSOLUTELY NO WARRANTY (use option -warranty)
" Version.version Version.date;
  flush stderr

let usage () =
  eprintf "\
Usage: why [options] [files...]

If no file is given, the source is read on standard input and
output is written in file `out...'

Generic Options:
  -h, --help     prints this message
  -V, --verbose  verbose mode
  -q, --quiet    quiet mode (default)
  -d, --debug    debugging mode (implies verbose mode)
  --werror       treat warnings as errors
  -v, --version  prints version and exits
  --warranty     prints license and exits
  --where        prints library path and exits
  --show-time    prints execution time

Typing/Annotations/VCG options:
  -p,  --parse-only  exits after parsing
  -tc, --type-only   exits after type-checking
  -wp, --wp-only     exits after annotation
  --fast-wp          use WP quadratic algorithm
  --white            white boxes: WP calculus enters pure expressions
  --black            black boxes: WP calculus does not enter pure expressions
  --wbb              while loops as black boxes (careful: incomplete WP)
  --split-user-conj  splits also user conjunctions in goals
  --split-bool-op    splits VCs for boolean operations &&, || and not
  --split n          splits conditions into several pieces up to n levels
  --partial          partial correctness
  --total            total correctness
  --explain          outputs explanations for VCs in file.xpl
  --locs f           reads source locations from file f
  --default-locs     reads source locations from file basename.loc
  --delete-old-vcs   delete files that originate from a previous call to Why on
                     the same file; active only when option --multi-why or
                     --multi-altergo is given
  --phantom <name>   declare <name> as a phantom type

VC transformation options:
  --all-vc           outputs all verification conditions (no auto discharge)
  --eval-goals       evaluate constant expressions in goals
  --prune-theory     prunes the theory
  --prune-hyp P V    prunes the hypotheses according to the depths P and V
  --exp all          expands the predicate definitions in both theory and goal
  --exp goal         expands the predicate definitions only in goal

Heuristics UNDER TEST of pruning (needs --prun-hyp to be used) :
  --prune-with-comp            uses comparisons as predicates
  --prune-without-arith        does not considere as particular predicates
  --prune-with-comp-filter     as previous and uses also comparisons as filters
  --prune-keep-local-links     insert quantified variables in variables graph
  --prune-comp-single-encoding do not inverse negative comparisons
  --prune-eq-only              consider only equality comparison as a predicate
  --prune-suffixed-comp        suffixes comparison predicates
  --prune-link-eqs             link each suffixed equalitie to the unsuffixed
  --prune-arith-tactic         statically link arithmetic operators (=, < & <=)
  --prune-vars-filter T        T in {All, One-var, One-branch, Split-hyps, CNF}
  --prune-polarized-preds      Consider polarity on predicates
  --prune-context              Filter axioms with Pred depth
  --prune-coarse-pred-comp     abstract weights in predicate predecessors
  --prune-get-depths           get minimum depths to reach reachable vars/preds

Prelude files:
  --lib-file f   load file f from the library

Encoding for types in untyped logic:
  --encoding none    does not encode types into terms for untyped provers
  --encoding pred    encodes types with predicates
  --encoding strat   encodes types into terms
  --encoding rec     encodes types with typing axioms
  --encoding mono    encodes types using monomorphisation
  --encoding sstrat  encodes types using some types  + strat
  --encoding monoinst  encodes types using some types  + monomorphisation

Prover selection:
  --alt-ergo  selects Alt-Ergo prover
  --coq       selects COQ prover (default)
  --cvcl      selects CVC Lite prover
  --gappa     selects the Gappa prover
  --harvey    selects haRVey prover
  --hol-light selects HOL Light prover
  --hol4      selects HOL4 prover
  --isabelle  selects Isabelle prover
  --mizar     selects Mizar prover
  --pvs       selects PVS prover
  --simplify  selects Simplify prover
  --smtlib    selects the SMT-LIB format
  --z3        selects the Z3 prover (native syntax)
  --zenon     selects the Zenon prover
 or generic Why outputs formats:
  --why       selects the Why pretty-printer
  --why3       selects the Why3 pretty-printer
  --multi-why selects the Why pretty-printer, with one file per goal
  --multi-altergo selects the Alt-Ergo pretty-printer, with one file per goal
  --project   selects the Why project format, with one file per goal

Coq-specific options:
  --valid,
  --no-valid  set/unset the functional validation (default is no)
  --coq-tactic <tactic>
              gives a default tactic for new proof obligations
  --coq-preamble <text>
              gives some Coq preamble to be substituted to \"Require Why\"
  --coq-fp-model <Module>
              sets the Coq model for floating-point arithmetic
  --coq-use-dp
  --no-coq-use-dp
              tells Coq to generate or not Dp_hint annotations to use external
              provers. Doesn't have any effect for Coq version < 8.1 (no 
              external provers support). Default is yes.

Monoinst-specific options
  --monoinstworldgen <builtin|complete|goal|premises>

PVS-specific options:
  --pvs-preamble <text>
              gives some PVS preamble to be substituted to \"importing why@@why\"

Simplify-specific options:
  --no-simplify-prelude
              suppress the Simplify prelude (BG_PUSHs for Why's symbols)
  --simplify-triggers
	      pass user-defined triggers when writing Simplify output

Zenon-specific options:
  --no-zenon-prelude
              suppress the Zenon prelude

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
  --output f     Redirect output to file f ( - for stdout)
  --dir d        Output files in directory d
  --int-is-ident
                 Consider `int' as a normal identifier, and use
                 built-in name `integer' instead for integers
";
  flush stderr

(*

SMT-lib-specific options:
  --modulo           uses %% in SMT-lib output (instead of uninterpreted symb)
*)


let files =
  let filesq = ref [] in
  let rec parse = function
    | [] -> List.rev !filesq
    | ("-h" | "-help" | "--help") :: _ -> usage (); exit 0
    | ("-alt-ergo" | "--alt-ergo") :: args -> prover_ := Ergo; parse args
    | ("-pvs" | "--pvs") :: args -> prover_ := Pvs; parse args
    | ("-coq-v7" | "--coq-v7") :: args -> prover_ := Coq V7; parse args
    | ("-coq-v8" | "--coq-v8") :: args -> prover_ := Coq V8; parse args
    | ("-coq-v81" | "--coq-v81" | "--coq-v8.1") :: args -> prover_ := Coq V81; parse args
    | ("-coq" | "--coq") :: args -> prover_ := Coq coq_version; parse args
    | ("-hol-light" | "--hol-light") :: args -> prover_ := HolLight; parse args
    | ("-mizar" | "--mizar") :: args -> prover_ := Mizar; parse args
    | ("-harvey" | "--harvey") :: args -> prover_ := Harvey; parse args
    | ("-simplify" | "--simplify") :: args -> prover_ := Simplify; parse args
    | ("-vampire" | "--vampire") :: args -> prover_ := Vampire; parse args
    | ("-isabelle" | "--isabelle") :: args -> prover_ := Isabelle; parse args
    | ("-hol4" | "--hol4") :: args -> prover_ := Hol4; parse args
    | ("-cvcl" | "--cvcl") :: args -> prover_ := CVCLite; parse args
    | ("-smtlib" | "--smtlib") :: args -> prover_ := SmtLib; parse args
    | ("-z3" | "--z3") :: args -> prover_ := Z3; parse args
    | ("-zenon" | "--zenon") :: args -> prover_ := Zenon; parse args
    | ("-why" | "--why") :: args -> prover_ := Why; parse args
    | ("-why3" | "--why3") :: args -> prover_ := Why3; parse args
    | ("-multi-why" | "--multi-why") :: args -> prover_ := MultiWhy; parse args
    | ("-multi-altergo" | "--multi-altergo") :: args ->
          prover_ := MultiAltergo; parse args
    | ("-project" | "--project") :: args -> prover_ := WhyProject; parse args
    | ("-gappa" | "--gappa") :: args -> prover_ := Gappa; parse args
    | ("-show-time" | "--show-time") :: args -> show_time_ := true; parse args
    | ("-no-prelude" | "--no-prelude" | "-no-arrays" | "--no-arrays"
      | "-fp" | "--fp" as o) :: _ ->
	Printf.eprintf "%s: deprecated\n" o; exit 1
    | "--no-pervasives" :: args ->
	no_pervasives := true; parse args
    | ("-lib-file" | "--lib-file") :: f :: args ->
	lib_files_to_load_ := f :: !lib_files_to_load_; parse args
    | ("-lib-file" | "--lib-file") :: [] -> usage (); exit 1
    | ("-load-file" | "--load-file") :: f :: args ->
	files_to_load_ := f :: !files_to_load_; parse args
    | ("-load-file" | "--load-file") :: [] -> usage (); exit 1
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
    | ("-coq-use-dp" | "--coq-use-dp") :: args -> coq_use_dp := true; parse args
    | ("-no-coq-use-dp" | "--no-coq-use-dp") :: args -> 
      coq_use_dp := false; parse args
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
    | ("--simplify-triggers" | "-simplify-triggers") :: args ->
	simplify_triggers_ := true; parse args
    | ("--no-cvcl-prelude" | "-no-cvcl-prelude") :: args ->
	no_cvcl_prelude_ := true; parse args
    | ("--no-harvey-prelude" | "-no-harvey-prelude") :: args ->
	no_harvey_prelude_ := true; parse args
    | ("--no-zenon-prelude" | "-no-zenon-prelude") :: args ->
	no_zenon_prelude_ := true; parse args
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
    | ("-dir" | "--dir") :: d :: args ->
	dir_ := d; parse args
    | ("-dir" | "--dir") :: [] ->
	usage (); exit 1
    | ("-fast-wp" | "--fast-wp") :: args ->
	fast_wp_ := true; parse args
    | ("-white" | "--white") :: args ->
	white_ := true; black_ := false; parse args
    | ("-black" | "--black") :: args ->
	black_ := true; white_ := false; parse args
    | ("-wbb" | "--wbb") :: args ->
        wbb_ := true; parse args
    | ("-split-user-conj" | "--split-user-conj") :: args ->
	split_user_conj_ := true; parse args
    | ("-split-bool-op" | "--split-bool-op") :: args ->
	split_bool_op_ := true; parse args
    | ("-split" | "--split") :: n :: args ->
	begin try lvlmax_ := int_of_string n with _ -> usage (); exit 1 end;
	parse args
    | ("-split" | "--split") :: [] ->
	usage (); exit 1
    | ("-all-vc" | "--all-vc" | "--allvc") :: args ->
	all_vc_ := true; parse args
    | ("-partial" | "--partial") :: args ->
	termination_ := Partial; parse args
    | ("-total" | "--total") :: args ->
	termination_ := Total; parse args
    | ("--eval-goals" | "-eval-goals") :: args ->
	 eval_goals_ := true ; parse args
    | ("--prune-theory" | "-prune-theory") :: args ->
	 pruning_ := true ; parse args
    | ("--prune-hyp" | "-prune-hyp"):: tp :: tv :: args ->
	pruning_hyp_p_ := int_of_string tp ;
	pruning_hyp_v_ := int_of_string tv ;
	parse args
(* Heuristiques en test *)
    | ("--prune-with-comp" | "-prune-with-comp"):: args ->
	pruning_hyp_CompInGraph_ := true ;
	parse args
    | ("--prune-with-comp-filter" | "-prune-with-comp-filter"):: args ->
	pruning_hyp_CompInGraph_ := true ;
	pruning_hyp_CompInFiltering_ := true ;
	parse args
    | ("--prune-keep-local-links" | "-prune-keep-local-links"):: args ->
	pruning_hyp_LinkVarsQuantif_ := true ;
	parse args
    | ("--prune-comp-single-encoding" | "-prune-comp-single-encoding"):: args ->
	pruning_hyp_keep_single_comparison_representation_ := true ;
	parse args
    | ("--prune-eq-only" | "-prune-eq-only"):: args ->
	pruning_hyp_CompInGraph_ := true ;
	pruning_hyp_comparison_eqOnly_ := true ;
	parse args
    | ("--prune-suffixed-comp" | "-prune-suffixed-comp"):: args ->
	pruning_hyp_CompInGraph_ := true ;
	pruning_hyp_suffixed_comparison_ := true ;
	parse args
    | ("--prune-link-eqs" | "-prune-link-eqs"):: args ->
	pruning_hyp_CompInGraph_ := true ;
	pruning_hyp_suffixed_comparison_ := true ;
	pruning_hyp_equalities_linked_ := true ;
	parse args
    | ("--prune-arith-tactic" | "-prune-arith-tactic"):: args ->
	pruning_hyp_CompInGraph_ := true ;
	pruning_hyp_arithmetic_tactic_ := true ;
	parse args

    | ("--prune-vars-filter" | "-prune-vars-filter"):: t :: args ->
	(match t with
	  "All" -> pruning_hyp_var_tactic_:=0; parse args
	| "One-var" -> pruning_hyp_var_tactic_:=1; parse args
	| "One-branch" -> pruning_hyp_var_tactic_:=2; parse args
	| "Split-hyps" -> pruning_hyp_var_tactic_:=3; parse args
	| "CNF" ->  pruning_hyp_var_tactic_:=4; parse args
	| _ -> usage (); exit 1);

    | ("--prune-polarized-preds" | "-prune-polarized-preds"):: args ->
	pruning_hyp_polarized_preds_ := true ; parse args

    | ("--prune-context" | "-prune-context") :: args ->
	prune_context_ := true ; parse args
    | ("--prune-coarse-pred-comp" | "-prune-coarse-pred-comp") :: args ->
	prune_coarse_pred_comp_ := true ; parse args

    | ("--prune-get-depths" | "-prune-get-depths") :: args ->
	prune_get_depths_ := true ; parse args

    | ("--prune-without-arith" | "-prune-without-arith") :: args ->
	pruning_hyp_considere_arith_comparison_as_special_predicate_ := false ; parse args
(* FIN de Heuristiques en test *)

(*
    | ("-modulo" | "--modulo") :: args ->
	 modulo_ := true ; parse args
*)
    | ("-exp" | "--exp") :: s :: args ->
	(match s with
	     "goal" -> defExpanding_ := Goal
	   | "all"  -> defExpanding_:= All
	   | _ -> usage (); exit 1);
	parse args
    | ("-encoding" | "--encoding") :: s :: args ->
	(match s with
	  "none" -> types_encoding_ := NoEncoding
	| "pred" -> types_encoding_ := Predicates
	| "strat" -> types_encoding_ := Stratified
	| "rec" -> types_encoding_ := Recursive
	| "mono" -> types_encoding_ := Monomorph
	| "sstrat" -> types_encoding_ := SortedStratified
	| "monoinst" -> types_encoding_ := MonoInst
	| _ -> usage (); exit 1);
	parse args
    | ("-monoinstworldgen" | "--monoinstworldgen") :: s :: args ->
	(match s with
	  "sorted" -> monoinstworldgen := MonoinstSorted
	| "builtin" -> monoinstworldgen := MonoinstBuiltin
	| "goal" -> monoinstworldgen := MonoinstGoal
        | "premises" -> monoinstworldgen := MonoinstPremises
	| _ -> usage (); exit 1);
        types_encoding_ := MonoInst;
	parse args
    | ("-monoinstoutput_world" | "--monoinstoutput_world")::args ->
        monoinstoutput_world := true;
        types_encoding_ := MonoInst;
        parse args
    | ("-monoinstonlymem" | "--monoinstonlymem")::args ->
        monoinstonlymem := true;
        monoinstonlyconst := false;
        parse args
    | ("-monoinstnounit" | "--monoinstnounit")::args ->
        (*monoinstnounit := true;*)
        parse args
    | ("-monoinstonlyconst" | "--monoinstonlyconst")::args ->
        monoinstonlyconst := true;
        monoinstonlymem := false;
        parse args
    | ("-explain" | "--explain") :: args ->
	explain_vc := true; parse args
    | ("-locs" | "--locs") :: s :: args ->
	locs_files := s :: !locs_files;
	parse args
    | ("-default-locs" | "--default-locs" ) :: args ->
          default_locs := true;
          parse args
    | ("-delete-old-vcs" | "--delete-old-vcs" ) :: args ->
          delete_old_vcs := true;
          parse args
    | ("-phantom" | "--phantom") :: s :: args ->
	Hashtbl.add phantom_types s ();
	parse args
    | f :: args ->
	filesq := f :: !filesq; parse args
  in
  parse (List.tl (Array.to_list Sys.argv))

(*s Finally, we dereference all the refs *)

let verbose = !verbose_
let debug = !debug_
let parse_only = !parse_only_
let type_only = !type_only_
let wp_only = !wp_only_
let prover (* ?(ignore_gui=false) *) () =
  if (* not ignore_gui &&*) !gui then Dispatcher else !prover_
let delete_old_vcs =
   !delete_old_vcs && (let p = prover () in p = MultiWhy || p = MultiAltergo)
let valid = !valid_
let coq_tactic = !coq_tactic_
let coq_preamble = match !coq_preamble_ with
  | None when prover () = Coq V7 -> "Require Why."
  | None -> "Require Export Why."
  | Some s -> s
let coq_use_dp = !coq_use_dp

let pvs_preamble = match !pvs_preamble_ with
  | None -> "IMPORTING why@why"
  | Some s -> s

let mizar_environ = !mizar_environ_
let isabelle_base_theory = !isabelle_base_theory_
let no_simplify_prelude = !no_simplify_prelude_
let simplify_triggers = !simplify_triggers_
let no_cvcl_prelude = !no_cvcl_prelude_
let no_harvey_prelude = !no_harvey_prelude_
let no_zenon_prelude = !no_zenon_prelude_
let wol = !wol_
let werror = !werror_
let dir = !dir_
let fast_wp = !fast_wp_
let white = !white_
let black = !black_
let wbb = !wbb_
let split_user_conj = !split_user_conj_
let split_bool_op = !split_bool_op_
let lvlmax = !lvlmax_
let all_vc = !all_vc_
let termination = !termination_
let eval_goals = !eval_goals_
let pruning = !pruning_
let pruning_hyp_p = !pruning_hyp_p_
let pruning_hyp_v = !pruning_hyp_v_
(* Heuristiques en test *)
let pruning_hyp_CompInGraph = !pruning_hyp_CompInGraph_
let pruning_hyp_CompInFiltering = !pruning_hyp_CompInFiltering_
let pruning_hyp_LinkVarsQuantif = !pruning_hyp_LinkVarsQuantif_
let pruning_hyp_keep_single_comparison_representation = !pruning_hyp_keep_single_comparison_representation_
let pruning_hyp_comparison_eqOnly = !pruning_hyp_comparison_eqOnly_
let pruning_hyp_suffixed_comparison = !pruning_hyp_suffixed_comparison_
let pruning_hyp_equalities_linked = !pruning_hyp_equalities_linked_
let pruning_hyp_arithmetic_tactic = !pruning_hyp_arithmetic_tactic_
let pruning_hyp_var_tactic = !pruning_hyp_var_tactic_
let pruning_hyp_polarized_preds = !pruning_hyp_polarized_preds_
let prune_context = !prune_context_
let prune_coarse_pred_comp = !prune_coarse_pred_comp_
let prune_get_depths = !prune_get_depths_
let pruning_hyp_considere_arith_comparison_as_special_predicate= !pruning_hyp_considere_arith_comparison_as_special_predicate_
(* FIN de Heuristiques en test *)
(*
let modulo = !modulo_
*)

let defExpanding = !defExpanding_
let explain_vc = !explain_vc

(* encoding checks *)
let () =
  if (prover () = SmtLib || prover () = CVCLite || prover () = Z3) &&
     !types_encoding_ = NoEncoding
  then
    types_encoding_ := SortedStratified

let get_types_encoding () = !types_encoding_
let set_types_encoding ec = types_encoding_ := ec

let monoinstworldgen = !monoinstworldgen
let monoinstoutput_world = !monoinstoutput_world
let monoinstonlymem = !monoinstonlymem
let monoinstnounit = !monoinstnounit
let monoinstonlyconst = !monoinstonlyconst

let get_type_expanding () = !defExpanding_

let show_time = !show_time_

let file f =
  (*Format.printf "Options.file: dir = %s, f = %s@." dir f;*)
  if dir = "" then f else Lib.file ~dir ~file:f

let ocaml = !ocaml_
let ocaml_annot = !ocaml_annot_
let ocaml_externals = !ocaml_externals_

let out_file f = match !output_ with
  | None -> file f
  | Some "-" -> invalid_arg "I can't use stdout for that output";
  | Some f -> f

let open_out_file f = match !output_ with
  | Some "-" -> stdout
  | _ -> open_out (out_file f)
let close_out_file cout = match !output_ with
  | Some "-" -> ()
  | _ -> close_out cout
let out_file_exists f =
  match !output_ with
    | Some "-" -> false
    | _ -> Sys.file_exists (out_file f)

let if_verbose f x = if verbose then f x
let if_verbose_2 f x y = if verbose then f x y
let if_verbose_3 f x y z = if verbose then f x y z

let if_debug f x = if debug then f x
let if_debug_2 f x y = if debug then f x y
let if_debug_3 f x y z = if debug then f x y z

let () =
  if !default_locs then
    locs_files :=
       (List.map (fun s ->
          Filename.chop_extension s ^ ".loc" ) files) @ !locs_files;

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

(* compatibility checks *)
let () = if prover () = Gappa && valid then begin
  Printf.eprintf "options -gappa and -valid are not compatible\n";
  exit 1
end
let () = if white && black then begin
  Printf.eprintf "options -white and -black are not compatible\n";
  exit 1
end

(* prelude *)

let lib_dir =
  try Sys.getenv "WHYLIB"
  with Not_found -> Version.libdir

let lib_file f = Filename.concat lib_dir (Filename.concat "why" f)

let prelude_file = lib_file "prelude.why"

let lib_files_to_load =
  (if !no_pervasives then [] else [prelude_file]) @
  List.rev_map lib_file !lib_files_to_load_ @
  List.rev !files_to_load_

let floats = List.mem "floats.why" !lib_files_to_load_

let () =
  if not (Sys.file_exists prelude_file) then begin
    Printf.eprintf "cannot find prelude file %s\n" prelude_file;
    begin
      try
	let s = Sys.getenv "WHYLIB" in
	Printf.eprintf "(WHYLIB is set to %s)\n" s
      with Not_found ->
	Printf.eprintf "(WHYLIB is not set, libdir is %s)\n" Version.libdir
    end;
    exit 1
  end

(*
Local Variables:
compile-command: "unset LANG; make -j -C .. bin/why.byte"
End:
*)
