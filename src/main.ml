
open Ast
open Types
open Env
open Format
open Error
open Rename
open Util

let debug = ref false

let interp_program id p =
  if !debug then eprintf "interpreting program %s@\n" (Ident.string id);
  (* 1. globalization *)
  let p = Db.db_prog p in
  (* 2. typing with effects *)
  if !debug then eprintf "typing with effects...@\n";
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
  if !debug then eprintf "functionalization...@\n";
  let cc = Mlize.trans ren p in
  let cc = Red.red cc in
  if !debug then begin print_cc_term err_formatter cc;eprintf "@\n" end;
  () (* TODO *)

let interp_decl = function
  | Program (id, p) -> interp_program id p
  | External (id, v) -> Env.add_global id v None

let deal_channel cin =
  let st = Stream.of_channel cin in
  let d = Grammar.Entry.parse Parser.decls st in
  List.iter interp_decl d

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
    deal_channel stdin
  else
    List.iter (fun f -> let c = open_in f in deal_channel c; close_in c) files

let rec explain_exception fmt = function
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Stdpp.Exc_located ((fc, lc), e) ->
      fprintf fmt "Characters %d-%d\n" fc lc;
      explain_exception fmt e
  | Error (Some (fc, lc), e) ->
      fprintf fmt "Characters %d-%d\n" fc lc;
      report fmt e
  | Error (_, e) ->
      report fmt e
  | e ->
      raise e
(*i
      fprintf fmt "Error: %s" (Printexc.to_string e)
i*)

let _ =
  try
    main ()
  with e ->
    explain_exception err_formatter e;
    pp_print_newline err_formatter ();
    exit 1


