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
open Ast
open Fenv

open Constructors
open Common

module O = Output

let rec invariant_for_struct ?pos this si =
  let _, invs =
    StringHashtblIter.find Typing.structs_table si.si_name
  in
  let invs = Assertion.mkand ?pos
    ~conjuncts:(List.map
                  (fun (li, _) ->
                     let a = { app_fun = li;
                               app_args = [this];
                               app_label_assoc = [];
                               app_region_assoc = [] }
                     in
                       new assertion ?pos (JCAapp a)) invs)
    ()
  in
    match si.si_parent with
      | None -> invs
      | Some(si, _) -> (* add invariants from the type hierarchy *)
          let this =
            match this#typ with
              | JCTpointer (_, a, b) ->
                  new term_with ~typ:(JCTpointer (JCtag(si, []), a, b)) this
              | _ -> assert false (* never happen *)
          in
            Assertion.mkand ?pos
              ~conjuncts:[invs; (invariant_for_struct ?pos this si)]
              ()

let code_function (fi, pos, fs, _sl) vil =
  (* Calculate global invariants. *)
  let _vitl =
    List.map
      (fun vi -> Term.mkvar ~var:vi ()) vil
  in
  let global_invariants =
    IntHashtblIter.fold
      (fun _ (li, _) acc ->
         (* li.li_parameters <- vil; *)
         let a = { app_fun = li;
                   app_args = (* vitl *)[];
                   app_label_assoc = [];
                   app_region_assoc = [] }
         in
         (new assertion ~mark:(Common.new_label_name ())
           ~pos (JCAapp a)) :: acc)
      Typing.global_invariants_table []
  in
  let global_invariants = Assertion.mkand ~pos ~conjuncts:global_invariants () in
  (* Calculate invariants for each parameter. *)
  let pre_invariants,post_invariants =
    List.fold_left
      (fun (acc1,acc2) (valid,vi) ->
         match vi.vi_type with
         | JCTpointer (JCtag (st, []), _, _) ->
           let inv =
             invariant_for_struct ~pos
               (Term.mkvar ~var:vi ()) st
           in
           ((if valid then
               Assertion.mkand ~pos
                 ~conjuncts: [acc1; inv] ()
             else acc1),
            Assertion.mkand ~pos
              ~conjuncts: [acc2; inv] ())
         | _ -> (acc1,acc2))
      (global_invariants,global_invariants)
      fi.fun_parameters
  in
  (* add invariants to the function precondition *)
  fs.fs_requires <-
    Assertion.mkand ~pos
      ~conjuncts:[fs.fs_requires; pre_invariants] ();
  (* add invariants to the function postcondition *)
  if is_purely_exceptional_fun fs then () else
    let safety_exists = ref false in
    let post = post_invariants in
    List.iter
      (fun (_, s, b) ->
         if s = "safety" then safety_exists := true;
         b.b_ensures <-
           Assertion.mkand ~pos ~conjuncts:[b.b_ensures; post] ())
      fs.fs_behavior;
    (* add the 'safety' spec if it does not exist
       (it could exist e.g. from Krakatoa) *)
    if not !safety_exists then
      if Options.verify_invariants_only then
        let invariants_b = { default_behavior with b_ensures = post } in
        fs.fs_behavior <-
          (Loc.dummy_position, "invariants", invariants_b) :: fs.fs_behavior;
      else
        let safety_b = { default_behavior with b_ensures = post } in
        fs.fs_behavior <-
          (Loc.dummy_position, "safety", safety_b) :: fs.fs_behavior;
