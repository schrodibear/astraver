(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: fastwp.ml,v 1.7 2007-02-21 10:56:12 filliatr Exp $ i*)

(*s Fast weakest preconditions *)

open Ident
open Logic
open Types
open Effect
open Misc
open Util
open Ast
open Env

module Subst = struct

  type t = { 
    current : Ident.t Idmap.t; (* current name for each variable *)
    sigma : Ident.t Idmap.t;   (* substitution for all variables *)
    types : pure_type Idmap.t; (* types, for quantifiers *)
    all_vars : Idset.t;        (* all names already used *)
  }

  let empty = 
    { current = Idmap.empty;
      sigma = Idmap.empty; 
      types = Idmap.empty; 
      all_vars = Idset.empty }

  let add x pt s = 
    { current = Idmap.add x x s.sigma;
      sigma = Idmap.add x x s.sigma;
      types = Idmap.add x pt s.types;
      all_vars = Idset.add x s.all_vars }

  let add_aux x pt s = 
    { s with
	types = Idmap.add x pt s.types;
	all_vars = Idset.add x s.all_vars }

  let frame env ef s =
    let r,w,_ = Effect.get_repr ef in
    List.fold_left 
      (fun s x -> 
	 try 
	   begin match Env.type_in_env env x with
	     | Ref pt -> add x pt s
	     | _ -> assert false end
	 with Not_found -> assert false) 
      s (r @ w)

  let find x s = Idmap.find x s.current

  let fresh x s =
    assert (Idmap.mem x s.types);
    let x' = next_away x s.all_vars in
    x',
    { current = Idmap.add x x' s.current; 
      sigma = Idmap.add x x' s.sigma; 
      types = Idmap.add x' (Idmap.find x s.types) s.types;
      all_vars = Idset.add x' s.all_vars }

  let write x s = let _,s = fresh x s in s
  let writes = List.fold_right write

  let term s = Misc.subst_in_term s.sigma
  let predicate s = Misc.subst_in_predicate s.sigma

  (* we cross the label l => 
     the values at label l are mapped to the current values of references *)
  let label l s =
    { s with sigma =
	Idmap.fold 
	  (fun x x' m -> 
	     if not (is_at x) then Idmap.add (at_id x l) x' m else m)
	  s.current s.sigma }

  (* debug *)
  open Format
  let print fmt s =
    let print_map fmt m = 
      Idmap.iter 
	(fun x x' -> fprintf fmt "(%a->%a)" Ident.lprint x Ident.lprint x') m
    in
    fprintf fmt "@[<hov 2>current=%a,@ sigma=%a@]" print_map s.current
      print_map s.sigma

end
open Subst

let merge s1 s2 =
  let d = 
    Idmap.fold 
      (fun x x1 d ->
	 try 
	   let x2 = Subst.find x s2 in if x1 != x2 then Idset.add x d else d
	 with Not_found -> 
	   Format.eprintf "@[merge avec %a et %a ; pbm avec x=%a@]@." 
	     Subst.print s1 Subst.print s2 Ident.lprint x;
	   Format.eprintf "Idmap.mem x s2 = %b@." (Idmap.mem x s2.sigma);
	   assert false)
      s1.current Idset.empty
  in
  let s12 = { s1 with all_vars = Idset.union s1.all_vars s2.all_vars } in
  Idset.fold 
    (fun x (s',r1,r2) -> 
       let x',s' = Subst.fresh x s' in
       let ty = PureType (Idmap.find x s'.types) in
       s', 
       wpand r1 (tequality ty (Tvar x') (Tvar (Subst.find x s1))),
       wpand r2 (tequality ty (Tvar x') (Tvar (Subst.find x s2))))
    d (s12, Ptrue, Ptrue)

let wpforall = pforall ~is_wp:true
let wpforalls = foralls ~is_wp:true

let ssubst_in_predicate s p = simplify (tsubst_in_predicate s p)

let norm (p,_) = p
let exn x pl = try List.assoc x pl with Not_found -> Pfalse
let exns e ee = List.map (fun x -> x, ee x) (get_exns e.info.t_effect)

(* INPUT
   - e : program
   - s : Subst.t
   OUTPUT
   - ok : predicate = correctness of e
   - (n,el) : predicate * (Ident.t * predicate) list, such that
     * if e terminates normally then n holds
     * if e raises exception E then List.assoc E el holds
   - s' : Subst.t
*)

let rec wp e s = 
  let _,(_,ee),_ as r = wp0 e s in
  assert (List.length ee = List.length (get_exns e.info.t_effect));
  r

and wp0 e s =
  (*Format.eprintf "@[wp avec %a@]@." Subst.print s;*)
  let v = result_type e in
  match e.desc with
  | Expression t ->
      (* OK: true
	 NE: result=t *)
      let t = Subst.term s (unref_term t) in
      Ptrue, (tequality v tresult t, []), s
  | If (e1, e2, e3) ->
      (* OK: ok(e1) /\ (ne(e1,true) => ok(e2)) /\ (ne(e1,false) => ok(e3))
	 NE: (ne(e1,true) /\ ne(e2,result)) \/ (ne(e1,false) /\ ne(e3,result)) 
      *)
      let ok1,(ne1,ee1),s1 = wp e1 s in
      let ok2,(ne2,ee2),s2 = wp e2 s1 in
      let ok3,(ne3,ee3),s3 = wp e3 s1 in
      let ne1true = ssubst_in_predicate (subst_one result ttrue) ne1 in
      let ne1false = ssubst_in_predicate (subst_one result tfalse) ne1 in
      let ok = wpands [ok1; wpimplies ne1true ok2; wpimplies ne1false ok3] in
      let s',r2,r3 = merge s2 s3 in
      let ne = por (wpands [ne1true; ne2; r2]) (wpands [ne1false; ne3; r3]) in
      let ee x = 
	pors [exn x ee1; wpand ne1true (exn x ee2); wpand ne1false (exn x ee3)]
      in
      ok, (ne, exns e ee), s'
  | Seq (e1, e2) ->
      (* OK: ok(e1) /\ (ne(e1,void) => ok(e2))
	 NE: ne(e1,void) /\ ne(e2,result) *)
      let ok1,(ne1,ee1),s1 = wp e1 s in
      let ok2,(ne2,ee2),s' = wp e2 s1 in
      let ne1void = tsubst_in_predicate (subst_one result tvoid) ne1 in
      let ok = wpand ok1 (wpimplies ne1void ok2) in
      let ne = wpand ne1void ne2 in
      let ee x = por (exn x ee1) (wpand ne1void (exn x ee2)) in
      ok, (ne, exns e ee), s'
  | AppRef (e, _, k) 
  | AppTerm (e, _, k) ->
      let lab = e.info.t_label in
      let s = Subst.label lab s in
      let q = optpost_app (asst_app (change_label "" lab)) k.t_post in
      let ok,((ne,ee) as nee),s' = wp e s in
      let s' = Subst.writes (Effect.get_writes k.t_effect) s' in
      assert (not (occur_predicate result ne));
      let nee = match q with
	| Some (q', qe) -> 
	    wpand ne (Subst.predicate s' q'.a_value),
	    (let ee x = 
	       let q' = List.assoc x qe in
	       por (exn x ee) (wpand ne (Subst.predicate s' q'.a_value))
	     in
	     exns e ee)
	| None -> 
	    nee
      in
      ok, nee, s'
  | Lam (bl, pl, e) ->
      (* OK: forall bl. pl => ok(e)
	 NE: forall bl. pl /\ ne(e, result) *)
      let s = Subst.frame e.info.t_env e.info.t_effect s in
      let ok,ne,s' = wp e s in
      let pl = List.map (fun a -> subst_in_predicate s.sigma a.a_value) pl in
      let q = List.filter (function (_,PureType _) -> true | _ -> false) bl in
      wpforalls q (wpimplies (wpands pl) ok),
      (wpforalls q (wpands (pl@[ok])), []),
      s'
  | Assertion (al, e1) ->
      (* OK: al /\ ok(e)
	 NE: al /\ ne(e,result) *)
      let ok,(ne1,ee1),s' = wp e1 s in
      let pl = List.map (fun a -> subst_in_predicate s.sigma a.a_value) al in
      let ee x = wpands (pl @ [exn x ee1]) in
      wpands (pl@[ok]), (wpands (pl@[ne1]), exns e ee), s'
  | Post (e1, q, _) ->
      (* TODO: what to do with the transparency here? *)
      let lab = e1.info.t_label in
      let s = Subst.label lab s in
      let ok,(ne1,ee1),s' = wp e1 s in
      let qql = post_app (asst_app (change_label "" lab)) q in
      let subst p = subst_in_predicate s'.sigma p.a_value in
      let (q,ql) = post_app subst qql in
      let ok = 
	wpands 
	  (ok :: 
	     wpforall result e1.info.t_result_type (wpimplies ne1 q) ::
	     List.map2 (fun (x,ex) (x',qx) -> assert (x=x'); 
			  wpimplies ex qx) ee1 ql)
      in
      let nee = 
	let ee x = wpand (exn x ee1) (List.assoc x ql) in
	wpand ne1 q, exns e ee
      in
      ok, nee, s'
  | Label (l, e) ->
      wp e (Subst.label l s)
  | LetIn (x, e1, e2) ->
      let ok1,ne1,s1 = wp e1 s in
      let ok2,ne2,s2 = wp e2 s1 in
      begin match e1.info.t_result_type with
	| PureType pt as ty1 ->
	    let ne1x = subst_in_predicate (subst_onev result x) (fst ne1) in
	    let ok = wpand ok1 (wpforall x ty1 (wpimplies ne1x ok2)) in
	    let ne = (*exists x ty1*) (wpand ne1x (fst ne2)) in
	    ok, (ne, []), Subst.add_aux x pt s2
	| Arrow _ ->
	    assert (not (occur_predicate result (fst ne1)));
	    assert (not (occur_predicate x (fst ne2)));
	    let ok = wpand ok1 (wpimplies (fst ne1) ok2) in (* ok1 /\ ok2 ? *)
	    let ne = wpand (fst ne1) (fst ne2) in
	    ok, (ne, []), s2
	| Ref _ -> 
	    assert false
      end
  | LetRef (x, e1, e2) ->
      let ok1,ne1,s1 = wp e1 s in
      let pt = match e1.info.t_result_type with 
	| PureType pt -> pt | Ref _ | Arrow _ -> assert false 
      in
      let s1 = Subst.add x pt s1 in
      let ok2,ne2,s2 = wp e2 s1 in
      let ne1x = subst_in_predicate (subst_onev result x) (fst ne1) in
      let ok = wpand ok1 (wpimplies ne1x ok2) in
      let ne = wpand ne1x (fst ne2) in
      ok, (ne, []), s2
  | Var _ -> 
      (* this must be an impure function, thus OK = NE = true *)
      Ptrue, (Ptrue, []), s
  | Absurd -> 
      (* OK = NE = false *)
      Pfalse, (Pfalse, []), s
  | Loop _ ->
      assert false (*TODO*)
  | Raise (id, None) -> 
      (* OK: true  
	 N : false  
	 E : true *)
      Ptrue, (Pfalse, [id, Ptrue]), s
  | Raise (id, Some e1) -> 
      (* OK: ok(e1)
	 N : false
	 E : ne(e1) \/ E(e1) if E=id, E(e1) otherwise *)
      let ok1,(ne1,ee1),s1 = wp e1 s in
      let ee x = 
	if x == id then 
	  try por ne1 (List.assoc x ee1) with Not_found -> ne1
	else
	  try List.assoc x ee1 with Not_found -> assert false
      in
      ok1, (Pfalse, exns e ee), s1
  | Try _ ->
      assert false (*TODO*)
  | Rec _ ->
      assert false (*TODO*)
  | Any _ ->
      assert false (*TODO*)
(***
  | Loop of assertion option * variant option * 'a t (* infinite loop *)
  (* exceptions *)
  | Raise of variable * 'a t option
  | Try of 'a t * (exn_pattern * 'a t) list 
  (* functions and applications *)
  | Rec of variable * type_v binder list * type_v * variant option * 
      precondition list * 'a t
  (* undeterministic expression *)
  | Any of type_c
***)

let wp e =
  let s = Subst.frame e.info.t_env e.info.t_effect Subst.empty in
  let ok,_,s = wp e s in
  let q = Idmap.fold (fun x pt q -> (x, PureType pt) :: q) s.types [] in
  wpforalls q ok

