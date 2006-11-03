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

(*i $Id: fastwp.ml,v 1.2 2006-11-03 09:23:51 filliatr Exp $ i*)

(*s Fast weakest preconditions *)

open Ident
open Logic
open Types
open Misc
open Util
open Ast
open Env

module Subst = struct

  type t = { 
    sigma : Ident.t Idmap.t;
    types : pure_type Idmap.t; 
    all_vars : Idset.t;
  }

  let empty = { 
    sigma = Idmap.empty; 
    types = Idmap.empty; 
    all_vars = Idset.empty 
  }

  let add x pt s = { 
    sigma = Idmap.add x x s.sigma;
    types = Idmap.add x pt s.types;
    all_vars = Idset.add x s.all_vars 
  }

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

  let find x s = Idmap.find x s.sigma

  let fresh x s =
    assert (Idmap.mem x s.types);
    let x' = next_away x s.all_vars in
    x',
    { sigma = Idmap.add x x' s.sigma; 
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
	  s.sigma s.sigma }

  (* debug *)
  open Format
  let print fmt s =
    fprintf fmt "@[<hov 2>sigma = ";
    Idmap.iter 
      (fun x x' -> fprintf fmt "%a->%a@ " Ident.lprint x Ident.lprint x') 
      s.sigma;
    fprintf fmt "@]"

end
open Subst

let merge s1 s2 =
  let d = 
    Idmap.fold 
      (fun x x1 d ->
	 try 
	   let x2 = Subst.find x s2 in if x1 != x2 then Idset.add x d else d
	 with Not_found -> assert false)
      s1.sigma Idset.empty
  in
  Idset.fold 
    (fun x (s',r1,r2) -> 
       let x',s' = Subst.fresh x s' in
       let ty = PureType (Idmap.find x s'.types) in
       s', 
       wpand r1 (tequality ty (Tvar x') (Tvar (Subst.find x s1))),
       wpand r2 (tequality ty (Tvar x') (Tvar (Subst.find x s2))))
    d (s1, Ptrue, Ptrue)

let wpforall = pforall ~is_wp:true
let wpforalls = foralls ~is_wp:true

let ssubst_in_predicate s p = simplify (tsubst_in_predicate s p)

(* input
   - e : program
   - s : Subst.t
   output
   - ok : predicate
   - (n,el) : predicate * (Ident.t * predicate) list
   - s' : Subst.t
*)

let rec wp e s = 
  Format.eprintf "@[wp avec %a@]@." Subst.print s;
  let v = result_type e in
  assert (Effect.get_exns (effect e) = []);
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
      let ok1,ne1,s1 = wp e1 s in
      let ok2,ne2,s2 = wp e2 s1 in
      let ok3,ne3,s3 = wp e3 s1 in
      let ne1true = ssubst_in_predicate (subst_one result ttrue) (fst ne1) in
      let ne1false = ssubst_in_predicate (subst_one result tfalse) (fst ne1) in
      let ok = wpands [ok1; wpimplies ne1true ok2; wpimplies ne1false ok3] in
      let s',r2,r3 = merge s2 s3 in
      let ne = 
	por (wpands [ne1true; fst ne2; r2]) (wpands [ne1false; fst ne3; r3]) 
      in
      ok, (ne, []), s'
  | Seq (e1, e2) ->
      (* OK: ok(e1) /\ (ne(e1,void) => ok(e2))
	 NE: ne(e1,void) /\ ne(e2,result) *)
      let ok1,ne1,s1 = wp e1 s in
      let ok2,ne2,s' = wp e2 s1 in
      let ne1void = tsubst_in_predicate (subst_one result tvoid) (fst ne1) in
      wpand ok1 (wpimplies ne1void ok2), (wpand ne1void (fst ne2), []), s'
  | AppRef (e, _, k) 
  | AppTerm (e, _, k) ->
      let lab = e.info.t_label in
      let s = Subst.label lab s in
      let q = optpost_app (asst_app (change_label "" lab)) k.t_post in
      let ok,ne,s' = wp e s in
      let s' = Subst.writes (Effect.get_writes k.t_effect) s' in
      assert (not (occur_predicate result (fst ne)));
      let ne = match q with
	| Some (q', _) -> wpand (fst ne) (Subst.predicate s' q'.a_value)
	| None -> fst ne
      in
      ok, (ne, []), s'
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
  | Assertion (al, e) ->
      (* OK: al /\ ok(e)
	 NE: al /\ ne(e,result) *)
      let ok,ne,s' = wp e s in
      let pl = List.map (fun a -> subst_in_predicate s.sigma a.a_value) al in
      wpands (pl@[ok]), (wpands (pl@[fst ne]), []), s'
  | Post (e, q, _) ->
      (* TODO: what to do with the transparency here? *)
      let lab = e.info.t_label in
      let s = Subst.label lab s in
      let ok,ne,s' = wp e s in
      let q = post_app (asst_app (change_label "" lab)) q in
      let q = subst_in_predicate s'.sigma (fst q).a_value in
      wpand ok (wpforall result e.info.t_result_type (wpimplies (fst ne) q)),
      (wpand (fst ne) q, []), s'
  | Label (l, e) ->
      wp e (Subst.label l s)
  | LetIn (x, e1, e2) ->
      let ok1,ne1,s1 = wp e1 s in
      let ok2,ne2,s2 = wp e2 s1 in
      let ne1x = subst_in_predicate (subst_onev result x) (fst ne1) in
      let ty1 = e1.info.t_result_type in
      let ok = wpand ok1 (wpforall x ty1 (wpimplies ne1x ok2)) in
      let ne = exists x ty1 (wpand ne1x (fst ne2)) in
      ok, (ne, []), s2
  | LetRef _ ->
      assert false (*TODO*)
  | Var _ -> (* this must be an impure function *)
      (* OK: true NE: true *)
      Ptrue, (Ptrue, []), s
  | Loop _ ->
      assert false (*TODO*)
  | Absurd -> 
      (* OK = NE = false *)
      Pfalse, (Pfalse, []), s
  | Raise _ -> 
      assert false (*TODO*)
  | Try _ ->
      assert false (*TODO*)
(***
  | Loop of assertion option * variant option * 'a t (* infinite loop *)
  | LetRef of variable * 'a t * 'a t
  | LetIn of variable * 'a t * 'a t
  (* assertion *)
  | Label of label * 'a t
  | Post of 'a t * postcondition * transp
  (* exceptions *)
  | Raise of variable * 'a t option
  | Try of 'a t * (exn_pattern * 'a t) list 
  (* functions and applications *)
  | Rec of variable * type_v binder list * type_v * variant option * 
      precondition list * 'a t
  (* undeterministic expression *)
  | Any of type_c
  (* proof term *)
  | Proof of type_c * (Cc.proof_term list -> Cc.proof_term)
***)
  | _ ->
      assert false (*TODO*)

let wp e =
  let s = Subst.frame e.info.t_env e.info.t_effect Subst.empty in
  let ok,_,s = wp e s in
  let q = Idmap.fold (fun x pt q -> (x, PureType pt) :: q) s.types [] in
  wpforalls q ok

