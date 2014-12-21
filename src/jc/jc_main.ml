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



open Stdlib
open Env
open Region
open Ast
(*open Fenv*)
open Common

open Format

module Output = (val Options.backend)

let parse_file f =
  try
    let c = open_in f in
    let d = Lexer.parse f c in
    close_in c;
    d
  with
  | Lexer.Lexical_error (l, s) ->
    eprintf "%a: lexical error: %s@." Why_loc.gen_report_position l s;
    exit 1

let compute_regions logic_components components =
  if !Options.separation_sem = SepRegions then begin
    Options.lprintf "Computation of regions@.";
    (* Preserve order between following calls *)
    Array.iter Separation.logic_component logic_components;
    StringHashtblIter.iter (Separation.axiom []) Typing.lemmas_table;
    StringHashtblIter.iter
      (fun _id data ->
         List.iter
           (function
            | Typing.ABaxiom (pos, id, labs, a) ->
              (Separation.axiom []) id (pos, (* is_axiom = *)true, [], labs, a))
           data.Typing.axiomatics_decls)
      Typing.axiomatics_table;
    Array.iter Separation.code_component components
  end

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

      (* (optional) phase 5: inference of annotations *)
      if !Options.annotation_sem <> AnnotNone then begin
        (* phase 5.1: pre-computation of regions *)
        compute_regions logic_components components;

        (* phase 5.2: pre-computation of effects *)
        compute_effects logic_components components;

        (* phase 5.3: inter- or intraprocedural inference of annotations *)
        Options.lprintf "Inference of annotations@.";
        if Options.interprocedural then begin
            (* interprocedural analysis over the call graph +
               intraprocedural analysis of each function called *)
          IntHashtblIter.iter
            (fun _ (fi, loc, fs, sl) ->
               if fi.Fenv.fun_name = Options.main then
                 Ai.main_function (fi, loc, fs, sl))
            Typing.functions_table;
        end else
          (* intraprocedural inference of annotations otherwise *)
          IntHashtblIter.iter
            (fun _ (f, loc, s, b) -> Ai.code_function (f, loc, s, b))
            Typing.functions_table
      end;

      (* phase 6: add invariants *)
      Options.lprintf "Adding invariants@.";
      let vil =
        IntHashtblIter.fold
          (fun _tag (vi, _eo) acc -> vi :: acc)
          Typing.variables_table
          []
      in
      IntHashtblIter.iter
      (fun _tag (f,loc,s,b) -> Invariants.code_function (f, loc, s, b) vil)
      Typing.functions_table;

      (* phase 7: computation of regions *)
      compute_regions logic_components components;

      (* phase 8: computation of effects *)
      compute_effects logic_components components;

      (* (optional)
         generation of the separation predicates : compute the needed
         generated predicates *)
      if Options.gen_frame_rule_with_ft then
        (Options.lprintf "Compute needed predicates@.";
         Frame.compute_needed_predicates ());


      (* (optional) phase 9: checking structure invariants *)
      begin match !Options.inv_sem with
      | InvOwnership ->
        Options.lprintf "Adding structure invariants@.";
        StringHashtblIter.iter
          (fun _name (_, invs) -> Invariants.check invs)
          Typing.structs_table
      | InvNone
      | InvArguments -> ()
      end;

      (*************************************************************************)
      (*                    PART 3: GENERATION OF WHY CODE                     *)
      (*************************************************************************)

      let push_decls, fold_decls, pop_decls =
        let decls = ref [] in
        (fun f -> decls := f !decls),
        (fun f acc -> let d, acc = f (!decls,acc) in decls := d; acc),
        (fun () -> !decls)
      in

      (* production phase 1: generation of Why types *)

      (* production phase 1.1: translate logic types *)
      Options.lprintf "Translate logic types@.";
      push_decls
        (StringHashtblIter.fold
           (fun _ id acc -> Interp.tr_logic_type id acc)
           Typing.logic_type_table);

      (* production phase 1.2: translate coding types *)
      Options.lprintf "Translate structures@.";
      push_decls
        (StringHashtblIter.fold (fun _ (st, _) acc -> Interp.struc st acc)
           Typing.structs_table);

      Options.lprintf "Translate variants@.";
      push_decls
        (StringHashtblIter.fold
           (fun _ -> Interp.root) Typing.roots_table);

      (* production phase 2: generation of Why variables *)

      (* production phase 2.1: translate coding variables *)
      Options.lprintf "Translate variables@.";
      push_decls
        (IntHashtblIter.fold (fun _ (v, e) acc -> Interp.tr_variable v e acc)
           Typing.variables_table);

      (* production phase 2.2: translate memories *)
      Options.lprintf "Translate memories@.";
      let regions =
        fold_decls
          (StringHashtblIter.fold
             (fun _ (fi, r) (acc, regions) ->
                let r = Region.representative r in
                let acc =
                  if RegionSet.mem r regions then acc
                                             else Interp.tr_region r acc
                in
                Interp.tr_memory (fi, r) acc,RegionSet.add r regions)
             Effect.constant_memories)
          (RegionSet.singleton dummy_region)
      in

    (* production phase 2.3: translate allocation tables *)
    Options.lprintf "Translate allocation tables@.";
    let regions =
      fold_decls
        (StringHashtblIter.fold
           (fun _ (a, r) (acc, regions) ->
              let r = Region.representative r in
              let acc =
                if RegionSet.mem r regions then acc
                                           else Interp.tr_region r acc
              in
              Interp.tr_alloc_table (a, r) acc, RegionSet.add r regions)
           Effect.constant_alloc_tables)
        regions
    in

    (* production phase 2.4: translate tag tables *)
    Options.lprintf "Translate tag tables@.";
    let _ =
      fold_decls
        (StringHashtblIter.fold
           (fun _ (a, r) (acc, regions) ->
              let r = Region.representative r in
              let acc =
                if RegionSet.mem r regions then acc
                                           else Interp.tr_region r acc
              in
              Interp.tr_tag_table (a, r) acc, RegionSet.add r regions)
           Effect.constant_tag_tables)
        regions
    in

    (* production phase 3: generation of Why exceptions *)
    Options.lprintf "Translate exceptions@.";
    push_decls
      (StringHashtblIter.fold
         (fun _ ei acc -> Interp.tr_exception ei acc)
         Typing.exceptions_table);

    (* production phase 3.1: translate enumerated types *)
    (* Yannick: why here and not together with translation of types? *)
    Options.lprintf "Translate enumerated types@.";
    push_decls
      (StringHashtblIter.fold
         (fun _ ri acc -> Interp.tr_enum_type ri acc)
         Typing.enum_types_table);
    let enumlist =
      StringHashtblIter.fold
        (fun _ ri acc -> ri::acc)
        Typing.enum_types_table
        []
    in
    let rec treat_enum_pairs pairs acc =
      match pairs with
      | [] -> acc
      | ri1 :: rest ->
        let acc =
          List.fold_left
            (fun acc ri2 ->
               Interp.tr_enum_type_pair ri1 ri2 acc) acc rest
        in
        treat_enum_pairs rest acc
    in
    push_decls (treat_enum_pairs enumlist);


    (* production phase 4.1: generation of Why logic functions *)
    Options.lprintf "Translate logic functions@.";
    push_decls
      (IntHashtblIter.fold
         (fun _ (li, p) acc ->
            Options.lprintf "Logic function %s@." li.Fenv.li_name;
            Frame.tr_logic_fun li p acc)
         Typing.logic_functions_table);

    (* production phase 4.2: generation of axiomatic logic decls*)
    Options.lprintf "Translate axiomatic declarations@.";
    push_decls
      (StringHashtblIter.fold
         (fun a data acc ->
            Options.lprintf "Axiomatic %s@." a;
            List.fold_left Interp.tr_axiomatic_decl acc
              data.Typing.axiomatics_decls)
         Typing.axiomatics_table);


    (* production phase 4.3: generation of lemmas *)
    Options.lprintf "Translate lemmas@.";
    push_decls
      (StringHashtblIter.fold
         (fun id (loc,is_axiom,_,labels,p) acc ->
            Interp.tr_axiom loc id is_axiom labels p acc)
         Typing.lemmas_table);

    (* (optional) production phase 6: generation of global invariants *)
    if !Options.inv_sem = InvOwnership then
      (Options.lprintf "Generation of global invariants@.";
       push_decls Invariants.make_global_invariants);

    (* production phase 7: generation of Why functions *)
    Options.lprintf "Translate functions@.";
    push_decls
      (IntHashtblIter.fold
         (fun _ (f, loc, s, b) acc ->
            Options.lprintf
              "Pre-treatement Function %s@." f.Fenv.fun_name;
            Interp.pre_tr_fun f loc s b acc)
         Typing.functions_table);
    push_decls
      (IntHashtblIter.fold
         (fun _ (f, loc, s, b) acc ->
            Options.lprintf "Function %s@." f.Fenv.fun_name;
            Interp.tr_fun f loc s b acc)
         Typing.functions_table);
    push_decls
      (StringHashtblIter.fold
         (fun n (fname, param_name_assoc) acc ->
            Interp.tr_specialized_fun n fname param_name_assoc acc)
         Interp_misc.specialized_functions);

    (* (optional) production phase 8: generation of global invariants *)
    if !Options.inv_sem = InvOwnership then begin
      (* production phase 8.1: "mutable" and "committed" declarations *)
      Options.lprintf "Translate mutable and committed declarations@.";
      push_decls
        (StringHashtblIter.fold
           (fun _ (st, _) acc -> Invariants.mutable_declaration st acc)
           Typing.structs_table);

      (* production phase 8.2: pack *)
      Options.lprintf "Translate pack@.";
      push_decls
        (StringHashtblIter.fold
           (fun _ (st, _) acc -> Invariants.pack_declaration st acc)
           Typing.structs_table);

      (* production phase 8.3: unpack *)
      Options.lprintf "Translate unpack@.";
      push_decls
        (StringHashtblIter.fold
           (fun _ (st, _) acc -> Invariants.unpack_declaration st acc)
           Typing.structs_table)
    end;

    (*************************************************************************)
    (*                       PART 5: OUTPUT FILES                            *)
    (*************************************************************************)

    (* union and pointer casts: disabled *)
    if !Region.some_bitwise_region then begin
      eprintf "Jessie support for unions and pointer casts is disabled@.";
      exit 1
    end;

    let decls = pop_decls () in

    (* output phase 1: produce Why file *)
    Output.print_to_file ~float_model:!Options.float_model filename decls;

    (* output phase 3: produce makefile *)
    Options.lprintf "Produce makefile@.";
    (*
      we first have to update Options.libfiles depending on the current
      pragmas
    *)
    Options.add_to_libfiles
      (if !Region.some_bitwise_region then
         "jessie_bitvectors.why" else "jessie.why");
    if !Options.has_floats then  begin
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
      eprintf "%a: typing error: %s@." Why_loc.gen_report_position l s;
      exit 1
    | Options.Error (l, s) when not Options.debug ->
      eprintf "%a: [Error]: %s@." Why_loc.gen_report_position l s;
      exit 1
    | Assert_failure (f, l, c) as exn when not Options.debug ->
      eprintf "%a:@." Why_loc.gen_report_line (f,l,c,c);
      raise exn

let _ =
  Sys.catch_break true;
  (* Yannick: [Printexc.catch] deprecated, normal system error seems ok,
     remove call? *)
  if Options.debug then main () else Printexc.catch main ()


(*
  Local Variables:
  compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
  End:
*)
