(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: main.ml,v 1.7 2002-01-24 15:59:30 filliatr Exp $ i*)

open Options
open Ast
open Types
open Env
open Format
open Error
open Rename
open Util

let header fmt f = match !prover with
  | Pvs -> Pvs.begin_theory fmt f
  | Coq -> ()

let trailer fmt f = match !prover with
  | Pvs -> Pvs.end_theory fmt f
  | Coq -> ()

let print_obligations = function
  | Pvs -> Pvs.print_obligations 
  | Coq -> Coq.print_obligations

let out_file f = match !prover with
  | Pvs -> Pvs.out_file f
  | Coq -> Coq.out_file f

let interp_program id p =
  if !debug then eprintf "=== interpreting program %s@\n" (Ident.string id);
  (* 1. globalization *)
  let p = Db.db_prog p in
  (* 2. typing with effects *)
  if !debug then eprintf "=== typing with effects...@\n";
  let env = Env.empty in
  let ren = initial_renaming env in
  let p = Typing.states ren env p in
  let c = p.info.kappa in
  let v = c.c_result_type in
  Error.check_for_not_mutable p.loc v;
  if !debug then begin print_type_c err_formatter c; eprintf "@\n" end;
  (* 3. w.p. *)
  let p = Wp.propagate ren p in
  (* 4. functionalization *)
  if !debug then eprintf "=== functionalization...@\n";
  let cc = Mlize.trans ren p in
  let cc = Red.red cc in
  if !debug then begin print_cc_term err_formatter cc; eprintf "@\n" end;
  (* 5. VCG *)
  let ol = Vcg.vcg (Ident.string id) cc in
  if !verbose then eprintf "%d proof obligation(s)@\n" (List.length ol);
  flush stderr;
  v, ol
    
let interp_decl fmt = function
  | Program (id, p) ->
      let v,ol = interp_program id p in
      print_obligations !prover fmt ol;
      Env.add_global id v None
  | External (ids, v) -> 
      List.iter (fun id -> Env.add_global id v None) ids
  | QPvs s ->
      if !prover = Pvs then fprintf fmt "  %s@\n@\n" s
  | QCoq s ->
      if !prover = Coq then fprintf fmt "%s@\n@\n" s

let deal_channel theo cin fmt =
  let st = Stream.of_channel cin in
  let d = Grammar.Entry.parse Parser.decls st in
  header fmt theo;
  List.iter (interp_decl fmt) d;
  trailer fmt theo

let deal_file f =
  Loc.set_file f;
  let cin = open_in f in 
  let fwe = Filename.chop_extension f in
  let base = Filename.basename fwe in
  let cout = open_out (out_file fwe) in
  let fmt = formatter_of_out_channel cout in
  deal_channel base cin fmt;
  close_in cin;
  pp_print_flush fmt ();
  close_out cout

let usage () =
  eprintf "
usage: why [options] [files...]

If no file is given, the source is read on standard input and
output is written in file `WhyOutput'

Options are:
  --help     prints this message
  --pvs      selects PVS prover
  --coq      selects COQ prover (default)
  --verbose  verbose mode
  --quiet    quiet mode (default)
  --debug    debugging mode
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
    | ("-q" | "--quiet") :: args -> verbose := false; parse args
    | ("-V" | "--verbose") :: args -> verbose := true; parse args
    | f :: args -> files := f :: !files; parse args
  in
  parse (List.tl (Array.to_list Sys.argv))

let main () =
  let files = parse_args () in
  if files = [] then
    deal_channel "WhyOutput" stdin std_formatter
  else
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


