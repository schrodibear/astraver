(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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



open Options
open Vcg
open Logic
open Logic_decl

type elem = Logic_decl.t

let stack = ref []

let add_elem e = stack := e :: !stack

let oblig = Queue.create ()
let oblig_h = Hashtbl.create 97

let add_oblig ((_,_,_,id,_) as o) =
  let so = (List.rev !stack, o) in
  Queue.add so oblig ;
  Hashtbl.add oblig_h id so

let rec f_of_seq ctx g = 
  match ctx with
    | [] -> g
    | Cc.Svar (id, v) :: hyps -> Forall(false,id,id,v,[],f_of_seq hyps g)
    | Cc.Spred (_id, p) :: hyps -> Pimplies(false,p,f_of_seq hyps g)

let push_decl d =
  match d with
  | Dgoal (loc, is_lemma, expl, id, s) -> 
      add_oblig (loc, is_lemma, expl, id, s);
      if is_lemma then 
        let (_l,(ctx,g)) = Env.specialize_sequent s in
        add_elem (Daxiom(loc,id,Env.generalize_predicate (f_of_seq ctx g)))
  | d -> add_elem d

let iter f = Queue.iter (fun (_,o) -> f o) oblig

(* calling prover *)

open DpConfig

let push_elem p e =
  if not pruning then
    assert (match e with Dgoal _ -> false | _ -> true);
  match p with
  | Simplify | Vampire -> Simplify.push_decl e
  | Harvey -> Harvey.push_decl e
  | Cvcl -> Cvcl.push_decl e
  | Zenon -> Zenon.push_decl e
  | Rvsat | Yices | Cvc3 | Z3 | VeriT -> Smtlib.push_decl e
  | Ergo | ErgoSelect | SimplifySelect
  | GappaSelect -> Pretty.push_decl ~ergo:true e
  | Coq -> Coq.push_decl e
  | PVS -> Pvs.push_decl e
  | Gappa -> Gappa.push_decl e

let push_obligation p (loc, is_lemma, expl, id, s) =
  let g = Dgoal (loc, is_lemma, expl, id, s) in
  match p with
  | Simplify | Vampire -> Simplify.push_decl g
  | Harvey -> Harvey.push_decl g
  | Cvcl -> Cvcl.push_decl g
  | Zenon -> Zenon.push_decl g
  | Rvsat | Yices | Cvc3 | Z3 | VeriT -> Smtlib.push_decl g
  | Ergo | ErgoSelect | SimplifySelect
  | GappaSelect -> Pretty.push_decl g
  | Coq -> Coq.push_decl g
  | PVS -> Pvs.push_decl g
  | Gappa -> Gappa.push_decl g

(* output_file is a CRITICAL SECTION *)
(** @parama elems is the List that stores the theory
    @parama o is the proof obligation
**)

let get_project () =
  match !Options.gui_project with
    | Some p -> p
    | None ->
	failwith "For interactive provers, option --project must be set"


let output_file ?encoding p (elems,o) =
  begin match encoding with
      Some e -> set_types_encoding e
    | None -> () end;
  begin match p with
    | Simplify | Vampire -> Simplify.reset ()
    | Harvey -> Harvey.reset ()
    | Cvcl -> Cvcl.prelude_done := false; Cvcl.reset ()
    | Zenon -> Zenon.prelude_done := false; Zenon.reset ()
    | Rvsat | Yices | Cvc3 | Z3 | VeriT -> Smtlib.reset ()
    | Ergo | ErgoSelect | SimplifySelect
    | GappaSelect -> Pretty.reset ()
    | Coq -> () (* Coq.reset () *)
    | PVS -> Pvs.reset()
    | Gappa -> Gappa.reset ()
  end;

  if pruning then
    begin
      (**stores into the declarationQueue
	 all the elements of the elems list and th obligation**)
      let declQ = Queue.create () in
      List.iter (fun p -> Queue.add p declQ) elems ;
      let (loc, is_lemma, expl, id, s) = o in
      let g = Dgoal (loc, is_lemma, expl, id, s) in
      Queue.add g declQ;
      if debug then
	Format.printf "Before the pruning dedicated to the PO: %d @."
	  (Queue.length declQ);
      (** reduce the theory **)
      let q = Theory_filtering.reduce declQ in
      if debug then
	Format.printf "After the pruning dedicated to the PO: %d @."
	  (Queue.length q);
      Queue.iter (push_elem p) q ;
      push_obligation p o
    end
  else
    begin
      List.iter (push_elem p) elems;
      push_obligation p o
    end;
  match p with
    | Simplify ->
	let f = Filename.temp_file "gwhy" "_why.sx" in
	Simplify.output_file ~allowedit:false f; f
    | Vampire ->
        let f = Filename.temp_file "gwhy" "_why.vp" in
        Simplify.output_file ~allowedit:false f; f
    | Harvey ->
	let f = Filename.temp_file "gwhy" "_why.rv" in
	Harvey.output_file f; f
    | Cvcl ->
	let f = Filename.temp_file "gwhy" "_why.cvc" in
	Cvcl.output_file ~allowedit:false f; f
    | Zenon ->
	let f = Filename.temp_file "gwhy" "_why.znn" in
	Zenon.output_file ~allowedit:false f; f
    | Rvsat | Yices | Cvc3 ->
	let f = Filename.temp_file "gwhy" "_why.smt" in
	Smtlib.output_file ~logic:"AUFLIRA" f; f
    | VeriT ->
        let f = Filename.temp_file "gwhy" "_why.smt" in
        Smtlib.output_file ~logic:"AUFLIRA" f; f
    | Z3 ->
	let f = Filename.temp_file "gwhy" "_why.smt" in
	Smtlib.output_file f; f
    | Ergo
    | ErgoSelect ->
	let f = Filename.temp_file "gwhy" "_why.why" in
	Pretty.output_file ~ergo:true f; f
    | SimplifySelect
    | GappaSelect ->
	let f = Filename.temp_file "gwhy" "_why.why" in
	Pretty.output_file ~ergo:false f; f
    | Gappa ->
	let f = Filename.temp_file "gwhy" "_why.gappa" in
	Gappa.output_one_file ~allowedit:false f; f
    | Coq ->
	let (_, _, _, f, _) = o in
	let _p = get_project () in
	(* if necessary, Pretty.output_project "name ?"; *)
	(* file should already be generated ?? *)
	(* Coq.output_file f; *)
	if debug then Format.printf "Reusing coq file %s_why.v@." f;
	f ^ "_why.v"
    | PVS ->
	assert false (* no PVS in Gwhy *)
(*
	let f = Filename.temp_file "gwhy" "_why.pvs" in
        Pvs.output_file ~allowedit:false f; f
*)



open Format

let prover_name p =
  try
    let (info,_) = List.assoc p DpConfig.prover_list in
    info.name
  with
      Not_found -> "(unnamed)"
(*
  | Simplify -> "Simplify"
  | Harvey -> "haRVey"
  | Cvcl -> "CVC Lite"
  | Zenon -> "Zenon"
  | Rvsat -> "rv-sat"
  | Yices -> "Yices"
  | Ergo ->
      DpConfig.alt_ergo.DpConfig.name ^ " " ^
      DpConfig.alt_ergo.DpConfig.version
  | Cvc3 -> "CVC3"
  | Graph -> "Graph"
  | Z3 -> "Z3"
  | Coq -> DpConfig.coq.DpConfig.name
*)

let call_prover ?(debug=false) ?timeout ?encoding ~obligation:o p =
  let so = try Hashtbl.find oblig_h o with Not_found -> assert false in
  let filename = output_file ?encoding p so in
  if debug then eprintf "calling %s on %s@." (prover_name p) filename;
  let r = match p with
    | Simplify ->
	Calldp.simplify ~debug ?timeout ~filename ()
    | Vampire ->
        Calldp.vampire ~debug ?timeout ~filename ()
    | Harvey ->
	Calldp.harvey ~debug ?timeout ~filename ()
    | Cvcl ->
	Calldp.cvcl ~debug ?timeout ~filename ()
    | Zenon ->
	Calldp.zenon ~debug ?timeout ~filename ()
    | Rvsat ->
	Calldp.rvsat ~debug ?timeout ~filename ()
    | Yices ->
	Calldp.yices ~debug ?timeout ~filename ()
    | Ergo ->
	Calldp.ergo ~select_hypotheses:false ~debug ?timeout ~filename ()
    | ErgoSelect ->
	Calldp.ergo ~select_hypotheses:true ~debug ?timeout ~filename ()
    | Cvc3 ->
	Calldp.cvc3 ~debug ?timeout ~filename ()
    | Z3 ->
	Calldp.z3 ~debug ?timeout ~filename ()
    | VeriT ->
        Calldp.verit ~debug ?timeout ~filename ()
    | SimplifySelect ->
	Calldp.generic_hypotheses_selection ~debug ?timeout ~filename
	  DpConfig.Simplify ()
    | Coq ->
	Calldp.coq ~debug ?timeout ~filename ()
    | PVS ->
	Calldp.pvs ~debug ?timeout ~filename ()
    | Gappa ->
	Calldp.gappa ~debug ?timeout ~filename ()
    | GappaSelect ->
	Calldp.generic_hypotheses_selection ~debug ?timeout ~filename
	  DpConfig.Gappa ()
  in
  begin match p with
    | Coq -> ()
    | _ -> Lib.remove_file ~debug filename
  end;
  r
