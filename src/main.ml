(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: main.ml,v 1.29 2002-06-07 09:34:45 filliatr Exp $ i*)

open Options
open Ast
open Types
open Env
open Format
open Error
open Misc
open Util

(*s Prover selection. *)

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
  let ploc = p.info.loc in
  if_verbose_3 eprintf "*** interpreting program %a@." Ident.print id;

  if_debug eprintf "* typing with effects@.";
  let env = Env.empty in
  let p = Typing.typef Typing.initial_labels env p in
  let c = p.info.kappa in
  let v = c.c_result_type in
  Error.check_for_not_mutable ploc v;
  Env.add_global id v None;
  print_if_debug print_type_c c;
  if type_only then raise Exit;

  if_debug eprintf "* weakest preconditions@.";
  let p,wp = Wp.propagate p in
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
  if Env.is_global id then Error.clash id (Some loc);
  Env.add_global id v None

let add_parameter tv id =
  push_parameter (Ident.string id) tv
    
let interp_decl = function
  | Program (id, p) ->
      if Env.is_global id then Error.clash id (Some p.info.loc);
      (try interp_program id p with Exit -> ())
  | Parameter (loc, ids, v) ->
      Typing.check_type_v (Some loc) Typing.initial_labels Env.empty v;
      List.iter (add_external loc v) ids;
      if not (is_mutable v) then
	let tv = Monad.trad_type_v (initial_renaming Env.empty) Env.empty v in
	List.iter (add_parameter tv) ids
  | External (loc, ids, v) -> 
      if is_mutable v then raise_with_loc (Some loc) MutableExternal;
      Typing.check_type_v (Some loc) Typing.initial_labels Env.empty v;
      List.iter (add_external loc v) ids
  | QPvs s ->
      Pvs.push_verbatim s

(*s Processinf of a channel / a file. *)

let deal_channel cin =
  let st = Stream.of_channel cin in
  let d = Grammar.Entry.parse Parser.decls st in
  if parse_only then exit 0;
  List.iter interp_decl d

let deal_file f =
  Loc.set_file f;
  reset ();
  let cin = open_in f in 
  let fwe = Filename.chop_extension f in
  deal_channel cin;
  close_in cin;
  output fwe

let main () =
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


