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

(*i $Id: main.ml,v 1.57 2003-03-26 07:10:17 filliatr Exp $ i*)

open Options
open Ptree
open Ast
open Cc
open Types
open Env
open Typing
open Format
open Error
open Report
open Misc
open Util

(*s Prover dependent functions. *)

let reset () =
  Vcg.logs := []; 
  match prover with
  | Pvs -> Pvs.reset ()
  | Coq -> Coq.reset ()
  | HolLight -> Holl.reset ()
  | Harvey -> Harvey.reset ()

let push_obligations ol = match prover with
  | Pvs -> Pvs.push_obligations ol
  | Coq -> Coq.push_obligations ol
  | HolLight -> Holl.push_obligations ol
  | Harvey -> Harvey.push_obligations ol

let push_validation id tt v = 
  if valid && prover = Coq then Coq.push_validation id tt v

let push_parameter id v tv = match prover with
  | Pvs -> if is_pure_type_v v then Pvs.push_parameter id tv
  | Coq -> Coq.push_parameter id tv
  | HolLight -> if is_pure_type_v v then Holl.push_parameter id tv
  | Harvey -> () (* nothing to do? *)

let output fwe = 
  if wol then begin
    let cout = open_out (fwe ^ ".wol") in
    output_value cout !Vcg.logs;    close_out cout
  end else if ocaml then 
    Options.output Ocaml.output 
  else begin match prover with
    | Pvs -> Pvs.output_file fwe
    | Coq -> Coq.output_file fwe
    | HolLight -> Holl.output_file fwe
    | Harvey -> Harvey.output_file fwe
  end

(*s Processing of a single declaration [let id = p]. *)

let print_if_debug p x = if_debug_3 eprintf "  @[%a@]@." p x

let interp_program id p =
  reset_names ();
  let ploc = p.ploc in
  if_verbose_3 eprintf "*** interpreting program %a@." Ident.print id;

  if_debug eprintf "* typing with effects@.";
  let env = Env.empty in
  let p = Typing.typef Label.empty env p in
  let c = p.info.kappa in
  let c = 
    { c with c_post = optpost_app (change_label p.info.label "") c.c_post }
  in
  let v = c.c_result_type in
  check_for_not_mutable ploc v;
  Env.add_global id v None;
  print_if_debug print_type_c c;
  if type_only then raise Exit;

  if_debug eprintf "* weakest preconditions@.";
  let p,wp = Wp.wp p in
  print_if_debug print_wp wp;
  print_if_debug print_prog p;
  if wp_only then raise Exit;

  if ocaml then begin Ocaml.push_program id p; raise Exit end;

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
  let tt = Monad.trad_type_c ren env c in
  push_validation ids tt v;
  if_verbose_2 eprintf "%d proof obligation(s)@\n@." (List.length ol);
  flush stderr

(*s Processing of a program. *)

let add_external loc v id =
  if Env.is_global id then raise_located loc (Clash id);
  Env.add_global id v None

let add_parameter v tv id =
  push_parameter (Ident.string id) v tv
    
let interp_decl d = 
  let env = Env.empty in
  let lab = Label.empty in
  let lenv = Env.logical_env env in
  match d with 
  | Program (id, p) ->
      if Env.is_global id then raise_located p.ploc (Clash id);
      (try interp_program id p with Exit -> ())
  | Parameter (loc, ids, v) ->
      let v = Ltyping.type_v loc lab env lenv v in
      List.iter (add_external loc v) ids;
      if ocaml then Ocaml.push_parameters ids v;
      if not (is_mutable v) then
	let tv = Monad.trad_type_v (initial_renaming env) env v in
	List.iter (add_parameter v tv) ids
  | External (loc, ids, v) -> 
      let v = Ltyping.type_v loc lab env lenv v in
      if is_mutable v then raise_located loc MutableExternal;
      if ocaml_externals then Ocaml.push_parameters ids v;
      List.iter (add_external loc v) ids
  | Exception (loc, id, v) ->
      if is_exception id then raise_located loc (ClashExn id);
      add_exception id v
  | Logic (loc, ids, t) ->
      let add id =
	if is_logic id lenv then raise_located loc (Clash id);
	add_global_logic id t
      in
      List.iter add ids

(*s Processing of a channel / a file. *)

let ml_parser c = 
   let st = Stream.of_channel c in
   Grammar.Entry.parse Parser.decls st
 
let c_parser c = 
  let d = Clexer.parse c in
  let p = Cinterp.interp d in
  print_if_debug print_pfile p;
  p

let deal_channel parsef cin =
  let p = parsef cin in
  if parse_only then exit 0;
  List.iter interp_decl p

let deal_file f =
  Loc.set_file f;
  reset ();
  let cin = open_in f in 
  c_file := Filename.check_suffix f ".c";
  let parsef = if !c_file then c_parser else ml_parser in
  deal_channel parsef cin;
  close_in cin;
  let fwe = Filename.chop_extension f in
  output fwe

let main () =
  if files = [] then begin
    deal_channel ml_parser stdin;
    output "Output" 
  end else
    List.iter deal_file files

let rec explain_exception fmt = function
  | Parsing.Parse_error -> 
      fprintf fmt "Syntax error"
  | Stream.Error s -> 
      fprintf fmt "Syntax error: %s" s
  | Error (Some loc, e) | Stdpp.Exc_located (_, Error (Some loc, e)) ->
      fprintf fmt "%a%a" Loc.report loc report e
  | Stdpp.Exc_located (loc, e) ->
      fprintf fmt "%a%a" Loc.report loc explain_exception e
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


