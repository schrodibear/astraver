
open Ast
open Types
open Env
open Format
open Error
open Rename
open Util

let debug = ref false

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
  if !debug then eprintf "%d proof obligation(s)@\n" (List.length ol);
  v, ol
    
let interp_decl fmt = function
  | Program (id, p) ->
      let v,ol = interp_program id p in
      Pvs.print_obligations fmt ol;
      Env.add_global id v None
  | External (ids, v) -> 
      List.iter (fun id -> Env.add_global id v None) ids
  | Pvs s ->
      fprintf fmt "  %s@\n@\n" s

let deal_channel theo cin fmt =
  let st = Stream.of_channel cin in
  let d = Grammar.Entry.parse Parser.decls st in
  Pvs.begin_theory fmt theo;
  List.iter (interp_decl fmt) d;
  Pvs.end_theory fmt theo

let deal_file f =
  Loc.set_file f;
  let cin = open_in f in 
  let fwe = Filename.chop_extension f in
  let base = Filename.basename fwe in
  let cout = open_out (fwe ^ ".pvs") in
  let fmt = formatter_of_out_channel cout in
  deal_channel base cin fmt;
  close_in cin;
  pp_print_flush fmt ();
  close_out cout

let parse_args () =
  let files = ref [] in
  let rec parse = function
    | [] -> !files
    | "-d" :: args -> debug := true; parse args
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


