(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

open Astraver

open Stdlib
open Region
open Common

open Format

let parse_file f =
  try
    let c = open_in f in
    let d = Lexer.parse f c in
    close_in c;
    d
  with
  | Lexer.Lexical_error (l, s) ->
    eprintf "%a: lexical error: %s@." Loc.gen_report_position l s;
    exit 1

let compute_regions logic_components components =
  Separation.fixpoint @@ fun () ->
  Options.lprintf "Computation of regions@.";
  (* Preserve order between following calls *)
  Array.iter Separation.logic_component logic_components;
  StringHashtblIter.iter (Separation.prop []) Typing.lemmas_table;
  StringHashtblIter.iter
    (fun _id data ->
       List.iter
         (function
           | Typing.ADprop (pos, id, labs, kind, a) ->
             (Separation.prop []) id (pos, (* is_axiom = *)kind = `Axiom, [], labs, a))
         data.Typing.axiomatics_decls)
    Typing.axiomatics_table;
  Array.iter Separation.code_component components

let compute_effects logic_components components =
  Options.lprintf "Computation of effects@.";
  (* Preserve order between following calls *)
  Array.iter Effect.logic_effects logic_components;
  Array.iter Effect.function_effects components

let main () =
  let files = Options.files () in
  try
    match files with
    | [] | _ :: _ :: _ -> Options.usage ()
    | [file] ->
      let filename = Filename.chop_extension file in

      (*************************************************************************)
      (*                          PART 1: PARSING                              *)
      (*************************************************************************)

      (* phase 1: parsing *)
      Options.lprintf "Parsing@.";
      let ast = parse_file file in
      if Options.debug then
        Format.printf "@\nAST AFTER PARSING:@\n%a@." Print_p.pdecls ast;

      (*************************************************************************)
      (*                          PART 2: ANALYSIS                             *)
      (*************************************************************************)

      (* phase 2: normalization *)
      Options.lprintf "Normalization@.";
      let ast = Norm.decls ast in

      (* phase 3: typing *)

      (* phase 3.1: type logic labels *)
      Options.lprintf "Typing logic labels@.";
      List.iter Typing.type_labels_in_decl ast;

      (* phase 3.2: type code *)
      Options.lprintf "Typing code@.";
      Typing.type_file ast;

      if Options.debug then
        Format.printf "@\nAST AFTER TYPING:@\n%a@." Typing.print_file ();

      (* phase 4: computation of call graph *)
      Options.lprintf "Computation of call graph@.";
      IntHashtblIter.iter (fun _ (f, t) -> Callgraph.compute_logic_calls f t)
        Typing.logic_functions_table;
      IntHashtblIter.iter
        (fun _ (f, _loc, s, b) ->
           Option.iter (Callgraph.compute_calls f s) b)
        Typing.functions_table;

      let logic_components =
        Callgraph.compute_logic_components Typing.logic_functions_table
      in
      let components =
        Callgraph.compute_components Typing.functions_table
      in

      (* update field "component" of functions *)
      Array.iteri
        (fun i l -> List.iter (fun fi -> fi.Fenv.fun_component <- i) l)
        components;

      (* phase 5: no annotation inference *)

      (* phase 6: add invariants *)
      Options.lprintf "Adding invariants@.";
      let vil =
        IntHashtblIter.fold
          (fun _tag (vi, _eo) acc -> vi :: acc)
          Typing.variables_table
          []
      in
      IntHashtblIter.iter
      (fun _tag (f, loc, s, b) -> Invariants.code_function (f, loc, s, b) vil)
      Typing.functions_table;

      (* phase 7: computation of regions *)
      compute_regions logic_components components;

      (* phase 8: computation of effects *)
      compute_effects logic_components components;

      (*************************************************************************)
      (*                    PART 3: GENERATION OF WHY CODE                     *)
      (*************************************************************************)

      let push_entries, pop_entries =
        let entries = ref [] in
        (fun es -> entries := es @ !entries),
        fun () -> !entries
      in

      (* production phase 1: generation of Why types *)

      (* production phase 1.1: translate logic types *)
      Options.lprintf "Translate logic types@.";
      StringHashtblIter.iter
        (fun _ -> push_entries % Interp.logic_type)
        Typing.logic_type_table;

      (* production phase 1.2: translate coding types *)
      Options.lprintf "Translate structures@.";
      StringHashtblIter.iter
        (fun _ (st, _) -> push_entries @@ Interp.struc st)
        Typing.structs_table;

      Options.lprintf "Translate variants@.";
      StringHashtblIter.iter
        (fun _ -> push_entries % Interp.root)
        Typing.roots_table;

      Options.lprintf "Translate global regions@.";
      push_entries (Interp.globals ());

      (* production phase 3: generation of Why exceptions *)
      Options.lprintf "Translate exceptions@.";
      push_entries (Interp.exceptions ());

      (* production phase 3.1: translate enumerated types *)
      (* Yannick: why here and not together with translation of types? *)
      Options.lprintf "Translate enumerated types@.";
      (let enums = StringHashtblIter.fold (fun _ -> List.cons) Typing.enum_types_table [] in
       push_entries @@ Interp.enums enums;
       push_entries
         List.(concat @@ map Interp.enum_cast @@ Fn.uncurry (@) @@ fdup2 Fn.id (map swap) @@ all_pairs enums));

      Options.lprintf "Translate dummies@.";
      push_entries @@ Interp.dummies;

      (* production phase 4.1: generation of Why logic functions *)
      Options.lprintf "Translate standalone logic functions@.";
      IntHashtblIter.iter
        (fun _ (li, p) ->
           Options.lprintf "Logic function %s@." li.Fenv.li_name;
           push_entries @@ Interp.logic_fun li p)
        Typing.logic_functions_table;

      (* production phase 4.2: generation of axiomatic logic decls *)
      Options.lprintf "Translate axiomatic declarations@.";
      StringHashtblIter.iter
        (fun a data ->
           Options.lprintf "Axiomatic %s@." a;
           push_entries @@ Interp.axiomatic a data)
        Typing.axiomatics_table;

      (* production phase 4.3: generation of lemmas *)
      Options.lprintf "Translate lemmas@.";
      StringHashtblIter.iter
        (fun id (pos, is_axiom, _,labels,p) ->
           push_entries @@ Interp.prop pos id is_axiom labels p)
        Typing.lemmas_table;

      (* production phase 7: generation of Why functions *)
      Options.lprintf "Translate functions@.";
      IntHashtblIter.iter
        (fun _ (f, _, spec, _) ->
           Options.lprintf "Pre-treatement Function %s@." f.Fenv.fun_name;
           Interp.prepare_fun f spec)
     Typing.functions_table;
      IntHashtblIter.iter
        (fun _ (f, loc, s, b) ->
           Options.lprintf "Function %s@." f.Fenv.fun_name;
           push_entries @@ Interp.func f loc s b)
        Typing.functions_table;

      (*************************************************************************)
      (*                       PART 5: OUTPUT FILES                            *)
      (*************************************************************************)

      if !Region.some_bitwise_region then begin
        eprintf "Support for bitwise unions and bit-level pointer casts is disabled@.";
      exit 1
    end;

    let file = pop_entries () in

    (* ATTENTION: HACK! *)
    (* This is the workaround for strange behavior of Why3 failing with undefined type bool on "true <> false" *)
    let () =
      let open Output_ast in
      let open Output in
      let use_bool = Use (`As None, Th.dummy @@ "why3.Bool.Bool") in
      List.iter
        (function
          | Entry (Theory (_, Some (deps, _))) ->
            deps :=  use_bool :: !deps
          | Entry (Module (_, Some (deps, _, _))) ->
            deps := Dependency use_bool :: !deps
          | _ -> ())
        file
    in

    (* output phase 1: produce Why file *)
    Print_why3.file ~filename:(filename ^ ".mlw") file;

    (* output phase 3: produce makefile *)
    Options.lprintf "Produce makefile@.";
    (*
      we first have to update Options.libfiles depending on the current
      pragmas
    *)
    Options.add_to_libfiles
      (if !Region.some_bitwise_region then
         "jessie_bitvectors.why" else "jessie.why");
    if !Options.has_floats then begin
      match !Options.float_model with
      | Env.FMmath -> ()
      | Env.FMdefensive ->
        Options.add_to_libfiles "floats_strict.why"
      | Env.FMfull ->
        Options.add_to_libfiles "floats_full.why"
      | Env.FMmultirounding ->
        Options.add_to_libfiles "floats_multi_rounding.why"
    end;
    Make.makefile filename
  with
    | Typing.Typing_error (l, s) when not Options.debug ->
      eprintf "%a: typing error: %s@." Loc.gen_report_position l s;
      exit 1
    | Options.Error (l, s) when not Options.debug ->
      eprintf "%a: [Error]: %s@." Loc.gen_report_position l s;
      exit 1
    | Assert_failure (f, l, c) as exn when not Options.debug ->
      eprintf "%a:@." Loc.gen_report_line (f,l,c,c);
      raise exn

let _ =
  Sys.catch_break true;
  (* Yannick: [Printexc.catch] deprecated, normal system error seems ok,
     remove call? *)
  if Options.debug then main () else Printexc.catch main ()
