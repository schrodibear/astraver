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

open Gobject.Data
open Options

(* columns of the model *)

let cols = new GTree.column_list
let name = cols#add string
let fullname = cols#add string
let parent = cols#add string
let total = cols#add int
let result = cols#add int
let stat = cols#add string

let first_row = ref None


type prover = {
  pr_id : DpConfig.prover_id;
  pr_info : DpConfig.prover_data;
  pr_result : int GTree.column;
  pr_icon : GtkStock.id GTree.column;
  pr_image : GdkPixbuf.pixbuf GTree.column ;
  mutable pr_viewcol : (GTree.view_column * GTree.view_column) option;
  pr_enc : Options.encoding;
}

let enc_name ~nl n p =
  let nl x = if nl then "\n" ^ x else x in
  match p.pr_enc with
    | NoEncoding ->
	begin match p.pr_id with
	  | DpConfig.SimplifySelect
	  | DpConfig.GappaSelect
	  | DpConfig.ErgoSelect -> n ^ nl "(Select)"
	  | _ -> n ^ nl ""
	end
    | SortedStratified -> n ^ nl "(SS)"
    | Monomorph -> n ^ nl "(mono)"
    | Recursive -> n ^ nl "(rec)"
    | Stratified -> n ^ nl "(Strat)"
    | Predicates -> n ^ nl "(pred)"
    | MonoInst -> n ^ nl "(monoinst)"

let prover_id p =
  enc_name ~nl:false p.pr_info.DpConfig.name p

let prover_name_with_version_and_enc p =
  let v = p.pr_info.DpConfig.version in
  let n = p.pr_info.DpConfig.name in
  let n = if v <> "" then n ^ "\n" ^ v else n ^ "\n(uninstalled)" in
  enc_name ~nl:true n p


let simplify = {
  pr_id = DpConfig.Simplify;
  pr_info = DpConfig.simplify;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
  }

let simplify_select = {
  pr_id = DpConfig.SimplifySelect;
  pr_info = DpConfig.simplify;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
  }

let simplify_pred = {
  pr_id = DpConfig.Simplify;
  pr_info = DpConfig.simplify;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = Predicates;
  }
let simplify_strat = {
  pr_id = DpConfig.Simplify;
  pr_info = DpConfig.simplify;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = Stratified;
  }
let simplify_sstrat = {
  pr_id = DpConfig.Simplify;
  pr_info = DpConfig.simplify;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = SortedStratified;
  }
let simplify_rec = {
  pr_id = DpConfig.Simplify;
  pr_info = DpConfig.simplify;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = Recursive;
  }

let vampire = {
  pr_id = DpConfig.Vampire;
  pr_info = DpConfig.vampire;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
  }

let gappa = {
  pr_id = DpConfig.Gappa;
  pr_info = DpConfig.gappa;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
  }

let gappa_select = {
  pr_id = DpConfig.GappaSelect;
  pr_info = DpConfig.gappa;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
  }

(*
let zenon = {
  pr_name = "Zenon";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_id = Dispatcher.Zenon;
  pr_enc = NoEncoding;
}
let zenon_pred = {
  pr_name = "Zenon(P)";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_id = Dispatcher.Zenon;
  pr_enc = Predicates;
}
let zenon_strat = {
  pr_name = "Zenon(S)";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_id = Dispatcher.Zenon;
  pr_enc = Stratified;
}
let zenon_rec = {
  pr_name = "Zenon(R)";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_id = Dispatcher.Zenon;
  pr_enc = Recursive;
}
let harvey = {
  pr_name = "haRVey";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_id = Dispatcher.Harvey;
  pr_enc = NoEncoding;
}
let cvcl = {
  pr_name = "CVCL";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_id = Dispatcher.Cvcl;
  pr_enc = SortedStratified;
}
let rvsat = {
  pr_name = "rv-sat";
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_id = Dispatcher.Rvsat;
  pr_enc = SortedStratified;
  }
*)
let yices = {
  pr_id = DpConfig.Yices;
  pr_info = DpConfig.yices;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = Monomorph;
  }
let yicesSS = {
  pr_id = DpConfig.Yices;
  pr_info = DpConfig.yices;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = SortedStratified;
  }
let ergo = {
  pr_id = DpConfig.Ergo;
  pr_info = DpConfig.alt_ergo;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
  }
let ergo_select = {
  pr_id = DpConfig.ErgoSelect;
  pr_info = DpConfig.alt_ergo;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
  }
let ergoSS = {
  pr_id = DpConfig.Ergo;
  pr_info = DpConfig.alt_ergo;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = SortedStratified;
  }
let verit =
  { pr_id = DpConfig.VeriT;
    pr_info = DpConfig.verit;
    pr_result = cols#add int;
    pr_icon = cols#add GtkStock.conv;
    pr_image = cols#add Gobject.Data.gobject;
    pr_viewcol = None;
    pr_enc = SortedStratified;
  }

let cvc3SS = {
  pr_id = DpConfig.Cvc3;
  pr_info = DpConfig.cvc3;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = SortedStratified;
  }
let z3SS = {
  pr_id = DpConfig.Z3;
  pr_info = DpConfig.z3;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = SortedStratified;
  }

let cvc3MI = {
  pr_id = DpConfig.Cvc3;
  pr_info = DpConfig.cvc3;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = MonoInst;
  }
let z3MI = {
  pr_id = DpConfig.Z3;
  pr_info = DpConfig.z3;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = MonoInst;
  }


let coq = {
  pr_id = DpConfig.Coq;
  pr_info = DpConfig.coq;
  pr_result = cols#add int;
  pr_icon = cols#add GtkStock.conv;
  pr_image = cols#add Gobject.Data.gobject;
  pr_viewcol = None;
  pr_enc = NoEncoding;
}


(***********

all provers


******)

let all_known_provers = [
  ergo;
  ergo_select;
  (*ergoSS;*)
  simplify;
  simplify_select;
  vampire;
  z3SS ;
  yicesSS;
  cvc3SS;
  z3MI;
  cvc3MI;
  (*simplify_sstrat;*)
(*
  simplify_strat;
*)
  yices;
  gappa ;
  gappa_select ;
  verit
(*
  coq ;
*)
  (* rvsat; *)
  (* zenon; zenon_pred; zenon_strat; zenon_rec;*)
  (* harvey; cvcl *)]

let prover_states = List.map (fun x -> (x,ref false)) all_known_provers

let get_prover_states () =
  List.map (fun (x,y) -> (x,!y)) prover_states

let default_prover = ref (List.hd all_known_provers)

let get_default_prover () = !default_prover

let set_default_prover p =
  default_prover := p

let select_prover p =
  let s = List.assq p prover_states in s:= true

let deselect_prover p =
  let s = List.assq p prover_states in s:= false

  let get_prover s =
  let rec next = function
    | [] ->
	raise Not_found
    | (p',_) :: r ->
	if prover_id p' = s then p' else next r
  in next prover_states


(* all obligations *)
let obligs = Hashtbl.create 97
let find_oblig = Hashtbl.find obligs

(* obligation name -> its model row *)
let orows = Hashtbl.create 97
(* obligation name -> its failure messages *)
let fwrows = Hashtbl.create 97

(* function -> its model row *)
let frows = Hashtbl.create 17
let find_fct = Hashtbl.find frows

(* function -> list of its obligations *)
let fobligs = Hashtbl.create 97
let find_fobligs = Hashtbl.find fobligs
let iter_fobligs fct f = Queue.iter f (Hashtbl.find fobligs fct)

(* functions *)
let fq = Queue.create ()

let add_failure row (p:prover) (message:string) =
  try
    let messages = Hashtbl.find fwrows row in
    if Hashtbl.mem messages p then
      Hashtbl.replace messages p message
    else Hashtbl.add messages p message
  with Not_found -> begin
    let h = Hashtbl.create 97 in
    Hashtbl.add h p message;
    Hashtbl.add fwrows row h
  end

let _ =
  let h = Hashtbl.create 1 in
  Hashtbl.add h simplify "";
  Hashtbl.add fwrows " " h;
  Hashtbl.clear h;
  Hashtbl.clear fwrows

let create_model () =
  let model = GTree.tree_store cols in
  Dispatcher.iter
    (fun ((_loc,_is_lemma, expl,s,_seq) as o) ->
       Hashtbl.add obligs s o;
       let f,n = Tools.decomp_name s in
       let row =
	 try
	   Hashtbl.find frows f
	 with Not_found ->
	   let row = model#append () in
	   Queue.add f fq;
	   Hashtbl.add frows f row;
	   Hashtbl.add fobligs f (Queue.create ());
	   let fname =
	     if f="" then "User goals" else
	       try
		 let (id,beh,(_f,_l,_b,_e)) = Hashtbl.find Util.program_locs f in
		 id ^ "\n" ^ beh
	       with Not_found -> "why " ^ f
	   in
	   model#set ~row ~column:name fname;
	   model#set ~row ~column:fullname f;
	   model#set ~row ~column:parent f;
	   model#set ~row ~column:total 0;
	   List.iter
	     (fun p -> model#set ~row ~column:p.pr_result 0)
	     all_known_provers;
	   row
       in
       let row_n = model#append ~parent:row () in
       (match !first_row with None -> first_row := Some(row_n) | Some _ -> ());
       Hashtbl.add orows s row_n;
       Queue.add row_n (Hashtbl.find fobligs f);
       let msg =
	 match expl.Logic_decl.vc_kind with
	   | Logic_decl.EKLemma -> "Lemma " ^ expl.Logic_decl.lemma_or_fun_name
	   | k -> Explain.msg_of_kind k
       in
       model#set ~row:row_n ~column:name (if f="" then msg else (n^". "^msg));
       model#set ~row:row_n ~column:fullname s;
       model#set ~row:row_n ~column:parent f;
       model#set ~row:row_n ~column:result 0;
       List.iter
	 (fun p ->
            model#set ~row:row_n ~column:p.pr_icon `REMOVE;
            model#set ~row:row_n ~column:p.pr_image !Tools.image_default;
            ()
         )
	 all_known_provers
    );
  model
