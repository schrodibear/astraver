(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: main.ml,v 1.13 2002-03-05 14:41:51 filliatr Exp $ i*)

open Options
open Ast
open Types
open Env
open Format
open Error
open Rename
open Util

(*s Prover selection. *)

let reset () = match !prover with
  | Pvs -> Pvs.reset ()
  | Coq -> Coq.reset ()

let push_obligations ol = match !prover with
  | Pvs -> Pvs.push_obligations ol
  | Coq -> Coq.push_obligations ol

let output fwe = match !prover with
  | Pvs -> Pvs.output_file fwe
  | Coq -> Coq.output_file fwe

(*s Processing of a single declaration [p]. *)

let interp_program id p =
  let ploc = p.info.loc in
  if_debug_3 eprintf "=== interpreting program %a ===@\n@?" Ident.print id;
  let p = Db.db_prog p in

  if_debug eprintf "=== typing with effects ===@\n@?";
  let env = Env.empty in
  let p = Typing.typef Typing.initial_labels env p in
  let c = p.info.kappa in
  let v = c.c_result_type in
  Error.check_for_not_mutable ploc v;
  if_debug_3 eprintf "%a@\n@?" print_type_c c;
  if !type_only then exit 0;

  if_debug eprintf "=== weakest preconditions ===@\n@?";
  let p = Wp.propagate p in
  if !wp_only then exit 0;

  if_debug eprintf "=== functionalization ===@\n@?";
  let ren = initial_renaming env in
  let cc = Mlize.trans ren p in
  let cc = Red.red cc in
  if_debug_3 eprintf "%a@\n@?" print_cc_term cc;

  if_debug eprintf "=== generating obligations ===@\n@?";
  let ol = Vcg.vcg (Ident.string id) cc in
  if_verbose_2 eprintf "%d proof obligation(s)@\n@?" (List.length ol);
  flush stderr;
  v, ol

(*s Processing of a program. *)
    
let interp_decl = function
  | Program (id, p) ->
      let v,ol = interp_program id p in
      push_obligations ol;
      Env.add_global id v None
  | External (ids, v) -> 
      List.iter (fun id -> Env.add_global id v None) ids
  | QPvs s ->
      Pvs.push_verbatim s

(*s Processinf of a channel / a file. *)

let deal_channel cin =
  let st = Stream.of_channel cin in
  let d = Grammar.Entry.parse Parser.decls st in
  List.iter interp_decl d

let deal_file f =
  Loc.set_file f;
  reset ();
  let cin = open_in f in 
  let fwe = Filename.chop_extension f in
  deal_channel cin;
  close_in cin;
  output fwe

(*s Command line parsing. *)

let usage () =
  eprintf "
usage: why [options] [files...]

If no file is given, the source is read on standard input and
output is written in file `WhyOutput'

General Options:
  -h, --help     prints this message
  -V, --verbose  verbose mode
  -q, --quiet    quiet mode (default)
  -d, --debug    debugging mode

Typing/Annotations options:
  -tc, --type-only  exits after type-checking
  -wp, --wp-only    exits after annotation

Prover options:
  --pvs      selects PVS prover
  --coq      selects COQ prover (default)
";
  flush stderr

let parse_args () =
  let files = ref [] in
  let rec parse = function
    | [] -> !files
    | ("-h" | "-help" | "--help") :: _ -> usage (); exit 0
    | ("-pvs" | "--pvs") :: args -> prover := Pvs; parse args
    | ("-coq" | "--coq") :: args -> prover := Coq; parse args
    | ("-d" | "--debug") :: args -> debug := true; parse args
    | ("-tc" | "--type-only") :: args -> type_only := true; parse args
    | ("-wp" | "--wp-only") :: args -> wp_only := true; parse args
    | ("-q" | "--quiet") :: args -> verbose := false; parse args
    | ("-V" | "--verbose") :: args -> verbose := true; parse args
    | f :: args -> files := f :: !files; parse args
  in
  parse (List.tl (Array.to_list Sys.argv))

let main () =
  let files = parse_args () in
  if files = [] then begin
    deal_channel stdin;
    output "WhyOutput" 
  end else
    List.iter deal_file files

let rec explain_exception fmt = function
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Stdpp.Exc_located (loc, e) ->
      Loc.report fmt loc;
      explain_exception fmt e
  | Error (Some loc, e) ->
      Loc.report fmt loc;
      report fmt e
  | Error (_, e) ->
      report fmt e
  | e ->
      fprintf fmt "Anomaly: %s" (Printexc.to_string e); raise e

let _ =
  try
    main ()
  with e ->
    explain_exception err_formatter e;
    pp_print_newline err_formatter ();
    exit 1


