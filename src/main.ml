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

(*i $Id: main.ml,v 1.78 2005-05-31 07:55:33 filliatr Exp $ i*)

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
open Logic

(*s Prover dependent functions. *)

let typed_progs = ref [] (* for the GUI *)

let dispatch f_pvs f_coq f_hol f_miz f_hrv f_smp f_cvc f_smt f_isabelle x = 
  match prover with
  | Pvs -> f_pvs x
  | Coq _ -> f_coq x
  | HolLight -> f_hol x
  | Mizar -> f_miz x 
  | Harvey -> f_hrv x
  | Simplify -> f_smp x
  | CVCLite -> f_cvc x
  | SmtLib -> f_smt x
  | Isabelle -> f_isabelle x

let reset () =
  typed_progs := [];
  Vcg.logs := []; 
  Fpi.reset ();
  match prover with
  | Pvs -> Pvs.reset ()
  | Coq _ -> Coq.reset ()
  | HolLight -> Holl.reset ()
  | Mizar -> Mizar.reset ()
  | Harvey -> Harvey.reset ()
  | Simplify -> Simplify.reset ()
  | CVCLite -> Cvcl.reset ()
  | SmtLib -> Smtlib.reset ()
  | Isabelle -> Isabelle.reset ()

let push_obligations ol = match prover with
  | Pvs -> Pvs.push_obligations ol
  | Coq _ -> Coq.push_obligations ol
  | HolLight -> Holl.push_obligations ol
  | Mizar -> Mizar.push_obligations ol
  | Harvey -> Harvey.push_obligations ol
  | Simplify -> Simplify.push_obligations ol
  | CVCLite -> Cvcl.push_obligations ol
  | SmtLib -> Smtlib.push_obligations ol
  | Isabelle -> Isabelle.push_obligations ol

let prover_is_coq = match prover with Coq _ -> true | _ -> false

let push_validation id tt v = 
  if valid && prover_is_coq then Coq.push_validation id tt v

let is_pure_type_scheme s = 
  match s.scheme_type with
    | Set -> assert false
    | TypeV v -> is_pure_type_v v

let push_parameter id v tv = match prover with
  | Pvs -> if is_pure_type_scheme v then Pvs.push_parameter id tv
  | Coq _ -> if is_pure_type_scheme v || valid then Coq.push_parameter id tv
  | HolLight -> if is_pure_type_scheme v then Holl.push_parameter id tv
  | Isabelle -> if is_pure_type_scheme v then Isabelle.push_parameter id tv
  | Mizar -> if is_pure_type_scheme v then Mizar.push_parameter id tv
  | Harvey | Simplify | SmtLib -> () (* nothing to do? *)
  | CVCLite -> if is_pure_type_scheme v then Cvcl.push_parameter id tv

let push_logic id t = match prover with
  | Pvs -> Pvs.push_logic id t
  | Coq _ -> Coq.push_logic id t
  | HolLight -> Holl.push_logic id t
  | Isabelle -> Isabelle.push_logic id t
  | Mizar -> Mizar.push_logic id t
  | Harvey | Simplify | SmtLib -> () (* nothing to do? *)
  | CVCLite -> Cvcl.push_logic id t

let push_axiom id p = match prover with
  | Pvs -> Pvs.push_axiom id p
  | Coq _ -> Coq.push_axiom id p
  | HolLight -> Holl.push_axiom id p
  | Isabelle -> Isabelle.push_axiom id p
  | Mizar -> Mizar.push_axiom id p
  | Harvey -> Harvey.push_axiom id p
  | Simplify -> Simplify.push_axiom id p
  | CVCLite -> Cvcl.push_axiom id p
  | SmtLib -> Smtlib.push_axiom id p

let push_predicate id p = match prover with
  | Pvs -> Pvs.push_predicate id p
  | Coq _ -> Coq.push_predicate id p
  | HolLight -> Holl.push_predicate id p
  | Isabelle -> Isabelle.push_predicate id p
  | Mizar -> Mizar.push_predicate id p
  | Harvey -> Harvey.push_predicate id p
  | Simplify -> Simplify.push_predicate id p
  | CVCLite -> Cvcl.push_predicate id p
  | SmtLib -> Smtlib.push_predicate id p

let output fwe = 
  if wol then begin
    let cout = open_out (fwe ^ ".wol") in
    output_value cout !Vcg.logs;    close_out cout
  end else if ocaml then 
    Options.output Ocaml.output 
  else begin match prover with
    | Pvs -> Pvs.output_file fwe
    | Coq _ -> Coq.output_file fwe
    | HolLight -> Holl.output_file fwe
    | Mizar -> Mizar.output_file fwe
    | Harvey -> Harvey.output_file fwe
    | Simplify -> Simplify.output_file fwe
    | CVCLite -> Cvcl.output_file fwe
    | SmtLib -> Smtlib.output_file fwe
    | Isabelle -> Isabelle.output_file fwe
  end;
  if fpi then Fpi.output fwe

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
  print_if_debug print_prog p;
  if type_only then raise Exit;

  let p = if black then begin
    if_debug eprintf "* purification@.";
    let p = Annot.purify p in
    print_if_debug print_prog p;
    p
  end else 
    p
  in

  if_debug eprintf "* weakest preconditions@.";
  let p,wp = Wp.wp p in
  if !Options.gui then typed_progs := p :: !typed_progs;
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
  let ol = if fpi then Fpi.split ol else ol in
  push_obligations ol;
  let tt = Monad.trad_type_c ren env c in
  push_validation ids tt v;
  if_verbose_2 eprintf "%d proof obligation(s)@\n@." (List.length ol);
  flush stderr

(*s Processing of a program. *)

let add_external loc v id =
  if Env.is_global id then raise_located loc (Clash id);
  Env.add_global_gen id v None

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
  | Parameter (loc, ext, ids, v) ->
      let v = Ltyping.type_v loc lab env lenv v in
      if ext && is_mutable v then raise_located loc MutableExternal;
      let v = Env.generalize_type_v v in
      List.iter (add_external loc v) ids;
      let v_spec = snd (specialize_type_scheme v) in
      if ext && ocaml_externals || ocaml then Ocaml.push_parameters ids v_spec;
      if not ext && not (is_mutable v_spec) then
	let tv = Monad.trad_scheme_v (initial_renaming env) env v in
	List.iter (add_parameter v tv) ids
  | Exception (loc, id, v) ->
      if is_exception id then raise_located loc (ClashExn id);
      add_exception id v
  | Logic (loc, ext, ids, t) ->
      let add id =
	if is_logic id lenv then raise_located loc (Clash id);
	let t = generalize_logic_type t in
	add_global_logic id t;
	if not ext then push_logic (Ident.string id) t
      in
      List.iter add ids
  | Predicate_def (loc, id, pl, p) ->
      if is_logic id lenv then raise_located loc (Clash id);
      let t = Predicate (List.map snd pl) in
      let t = generalize_logic_type t in
      add_global_logic id t;
      let lenv' = 
	List.fold_right 
	  (fun (x,pt) -> add_logic ~generalize:false x (PureType pt)) pl lenv 
      in
      let p = Ltyping.predicate lab env lenv' p in
      let p = generalize_predicate_def (pl,p) in
      push_predicate (Ident.string id) p
  | Axiom (loc, id, p) ->
      let p = Ltyping.predicate lab env lenv p in
      let p = generalize_predicate p in
      push_axiom (Ident.string id) p

(*s Processing of a channel / a file. *)

let ml_parser c = 
   let st = Stream.of_channel c in
   Grammar.Entry.parse Parser.decls st
 
let deal_channel parsef cin =
  let p = parsef cin in
  if parse_only then exit 0;
  List.iter interp_decl p

let deal_file f =
  Loc.set_file f;
  reset ();
  let cin = open_in f in 
  deal_channel ml_parser cin;
  close_in cin;
  let fwe = Filename.chop_extension f in
  output (Options.file fwe)

let main () =
  if files = [] then begin
    deal_channel ml_parser stdin;
    output "Output" 
  end else
    List.iter deal_file files



