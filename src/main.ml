(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: main.ml,v 1.38 2002-10-15 09:05:53 filliatr Exp $ i*)

open Options
open Ptree
open Ast
open Cc
open Types
open Env
open Format
open Error
open Report
open Misc
open Util

(*s Prover dependent functions. *)

let reset () = match prover with
  | Pvs -> Pvs.reset ()
  | Coq -> Coq.reset ()

let push_obligations ol = match prover with
  | Pvs -> Pvs.push_obligations ol
  | Coq -> Coq.push_obligations ol

let push_validation id v = 
  if valid && prover = Coq then Coq.push_validation id v

let push_parameter id v = match prover with
  | Pvs -> Pvs.push_parameter id v
  | Coq -> Coq.push_parameter id v

let output fwe = match prover with
  | Pvs -> Pvs.output_file fwe
  | Coq -> Coq.output_file fwe

(*s Processing of a single declaration [let id = p]. *)

let print_if_debug p x = if_debug_3 eprintf "  @[%a@]@." p x

let interp_program id p =
  reset_names ();
  let ploc = p.loc in
  if_verbose_3 eprintf "*** interpreting program %a@." Ident.print id;

  if_debug eprintf "* typing with effects@.";
  let env = Env.empty in
  let p = Typing.typef Env.initial_labels env p in
  let c = p.info.kappa in
  let v = c.c_result_type in
  Typing.check_for_not_mutable ploc v;
  Env.add_global id v None;
  print_if_debug print_type_c c;
  if type_only then raise Exit;

  if_debug eprintf "* weakest preconditions@.";
  let p,wp = Wp.wp p in
  print_if_debug print_wp wp;
  print_if_debug print_prog p;
  if wp_only then raise Exit;

  if_debug eprintf "* functionalization@.";
  let ren = initial_renaming env in
  let cc = Mlize.trans p ren in
  if_debug_3 eprintf "  %a@\n  -----@." print_cc_term cc;
  let cc = Red.red cc in
  print_if_debug print_cc_term cc;

  if_debug eprintf "* generating obligations@.";
  let ids = Ident.string id in
  let ol,v = Vcg.vcg ids cc in
  push_obligations ol;
  push_validation ids v;
  if_verbose_2 eprintf "%d proof obligation(s)@\n@." (List.length ol);
  flush stderr

(*s Processing of a program. *)

let add_external loc v id =
  if Env.is_global id then raise_located loc (Clash id);
  Env.add_global id v None

let add_parameter tv id =
  push_parameter (Ident.string id) tv
    
let interp_decl d = 
  let env = Env.empty in
  let lab = Env.initial_labels in
  let lenv = Env.logical_env env in
  match d with 
  | Program (id, p) ->
      if Env.is_global id then raise_located p.loc (Clash id);
      (try interp_program id p with Exit -> ())
  | Parameter (loc, ids, v) ->
      let v = Ltyping.type_v loc lab env lenv v in
      List.iter (add_external loc v) ids;
      if not (is_mutable v) then
	let tv = Monad.trad_type_v (initial_renaming env) env v in
	List.iter (add_parameter tv) ids
  | External (loc, ids, v) -> 
      let v = Ltyping.type_v loc lab env lenv v in
      if is_mutable v then raise_located loc MutableExternal;
      List.iter (add_external loc v) ids
  | Exception (loc, id, v) ->
      if is_exception id then raise_located loc (ClashExn id);
      add_exception id v
  | Logic (loc, id, t) ->
      if is_logic id lenv then raise_located loc (Clash id);
      add_global_logic id t
  | QPvs s ->
      Pvs.push_verbatim s

(*s Processing of a channel / a file. *)

let ml_parser c = 
   let st = Stream.of_channel c in
   Grammar.Entry.parse Parser.decls st
 
let c_parser c = 
  let d = Clexer.parse c in
  Cinterp.interp d

let deal_channel parsef cin =
  let d = parsef cin in
  if parse_only then exit 0;
  List.iter interp_decl d

let deal_file f =
  Loc.set_file f;
  reset ();
  let cin = open_in f in 
  let parsef = if Filename.check_suffix f ".c" then c_parser else ml_parser in
  deal_channel parsef cin;
  close_in cin;
  let fwe = Filename.chop_extension f in
  output fwe

let main () =
  if files = [] then begin
    deal_channel ml_parser stdin;
    output "WhyOutput" 
  end else
    List.iter deal_file files

let rec explain_exception fmt = function
  | Parsing.Parse_error -> 
      fprintf fmt "Syntax error"
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


