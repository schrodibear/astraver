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

(*i $Id: wp.ml,v 1.81 2003-07-10 15:41:43 filliatr Exp $ i*)

(*s Weakest preconditions *)

open Ident
open Error
open Logic
open Misc
open Types
open Ast
open Util
open Env
open Effect
open Annot

(*s to quantify over all the variables modified by [p] *)

let output p = 
  let w = Effect.get_writes (effect p) in
  let env = p.info.env in
  List.map (fun id -> (id, type_in_env env id)) w

(*s [filter_post k q] removes exc. postconditions from [q] which do not
    appear in typing info [k] *)

let filter_post k =
  let ef = k.kappa.c_effect in
  let keep (x,_) = is_exn ef x in
  option_app (fun (q, ql) -> (q, List.filter keep ql))

(*s [saturate_post k a q] makes a postcondition for a program of type [k]
    out of a normal postcondition [a] and the exc. postconditions from [q] *)

let saturate_post k a q = 
  let ql = match q with Some (_,l) -> l | None -> [] in
  let set_post x = x, try List.assoc x ql with Not_found -> default_post in
  let xs = get_exns k.kappa.c_effect in
  let saturate a = (a, List.map set_post xs) in
  option_app saturate a

(*s Misc. test functions *)

let need_a_post p = 
  match p.desc with Lam _ | Rec _ -> false | _ -> true

let is_while p = 
  match p.desc with While _ -> true | _ -> false

(*s Weakest precondition of an annotated program:
    \begin{verbatim}
    wp(e{Q'}, Q) = forall y,v. Q' => Q
    \end{verbatim}
    When [e] may raise exceptions:
    \begin{verbatim}
    wp(e{Q'|Q'1|...Q'k}, Q|Q1|...Qk) =
    (forall y,v. Q' => Q) and ... and (forall y,x. Q'k => Qk)
    \end{verbatim} *)

let abstract_wp (q',ql') (q,ql) res out =
  assert (List.length ql' = List.length ql);
  let quantify a' a res =
    let vars = match res with Some b -> b :: out | None -> out in
    foralls true vars (Pimplies (true, a'.a_value, a.a_value)) 
  in
  let quantify_h (x',a') (x,a) =
    assert (x' = x);
    let pt = find_exception x in
    quantify a' a (option_app (fun t -> (result, PureType t)) pt)
  in
  pands true (quantify q' q (Some res) :: List.map2 quantify_h ql' ql)

(*s Adding precondition and obligations to the wp *)

let add_to_wp loc al w =
  let al = List.map (fun p -> p.a_value) al in
  if al = [] then
    w
  else match w with
    | Some w -> Some (asst_app (fun w -> List.fold_left (pand true) w al) w) 
    | None -> Some (wp_named loc (pands true al))

let add_pre_and_oblig p = add_to_wp p.info.loc (pre p @ obligations p)

(*s WP. [wp p q] computes the weakest precondition [wp(p,q)]
    and gives postcondition [q] to [p] if necessary.

    [wp: typed_program -> postcondition option -> assertion option] *)

let rec wp p q =
  let q = option_app (force_post_loc p.info.loc) q in
  let env = p.info.env in
  let lab = p.info.label in
  let postp = post p in
  let q0 = Annot.sup postp q (* if postp = None then q else postp *) in
  let q0_ = optpost_app (change_label "" lab) q0 in
  let d,w = wp_desc p.info p.desc q0_ in
  let p = change_desc p d in
  let w = option_app (asst_app (erase_label lab)) w in
  let p = if need_a_post p then force_post env q0 p else p in
  let w = match postp, q with
    (* abstrac wrt existing post, unless [p] is a loop *)
    | Some q', Some q when not (is_while p) ->
	let res = (result, result_type p) in
	let w = abstract_wp q' q res (output p) in
	Some (wp_named p.info.loc (erase_label lab (erase_label "" w)))
    | _ -> 
	force_wp_name w
  in
  let w = add_pre_and_oblig p w in
  p, w

and wp_desc info d q = 
  let result = info.kappa.c_result_name in
  match d with
    (* TODO: check if likely *)
    | Var x ->
	let w = optpost_val q in
	d, optasst_app (tsubst_in_predicate (subst_one result (Tvar x))) w
    (* $wp(E,q) = q[result \leftarrow E]$ *)
    | Expression t ->
	let w = optpost_val q in
	let t = unref_term t in
	let s = subst_one result t in
	d, optasst_app (fun p -> simplify (tsubst_in_predicate s p)) w
    (* $wp(!x,q) = q[result \leftarrow x]$ *)
    | Acc x ->
	let w = optpost_val q in
	d, optasst_app (subst_in_predicate (subst_onev result x)) w
    (* $wp(x := e, q) = wp(e, q[result\leftarrow void; x\leftarrow result])$ *)
    | Aff (x, p) ->
	let q = optval_app (tsubst_in_predicate (subst_one result tvoid)) q in
	let q = optval_app (subst_in_predicate (subst_onev x result)) q in
	let p',w = wp p q in
	Aff (x, p'), w
    | TabAcc (ck, x, e1) ->
	let t = make_raw_access info.env (x,x) (Tvar result) in
	let q = optpost_app (tsubst_in_predicate (subst_one result t)) q in
	let e'1,w = wp e1 q in
	TabAcc (ck, x, e'1), w
    | TabAff (ck, x, 
	      ({desc=Expression ce1} as e1), ({desc=Expression ce2} as e2)) ->
	let w = optpost_val q in
	let w = optasst_app (tsubst_in_predicate (subst_one result tvoid)) w in
	let st = make_raw_store info.env (x,x) ce1 ce2 in
	let w = optasst_app (tsubst_in_predicate (subst_one x st)) w in
	let e'1,_ = wp e1 None in
	let e'2,_ = wp e2 None in
	TabAff (ck, x, e'1, e'2), w
    | TabAff _ ->
	assert false

    | If (p1, p2, p3) ->
	let p'2,w2 = wp p2 (filter_post p2.info q) in
	let p'3,w3 = wp p3 (filter_post p3.info q) in
	(match w2, w3 with
	   | Some {a_value=q2}, Some {a_value=q3} -> 
	       (* $wp(if p1 then p2 else p3, q) =$ *)
	       (* $wp(p1, if result then wp(p2, q) else wp(p3, q))$ *)
	       let result1 = p1.info.kappa.c_result_name in
	       let q1 = create_postval (Pif (Tvar result1, q2, q3)) in
	       let q1 = force_wp_name q1 in
	       let q1 = saturate_post p1.info q1 q in
	       let p'1,w1 = wp p1 q1 in
	       If (p'1, p'2, p'3), w1
	   | _ ->
	       let p'1,_ = wp p1 None in
	       If (p'1, p'2, p'3), None)
    | Seq bl -> 
	let bl',w = wp_block bl q in
	Seq bl', w
    | App (p1, Term p2, k) ->
	let p'1,_ = wp p1 None in
	let p'2,_ = wp p2 None in
	App (p'1, Term p'2, k), None
    | App (p1, a, k) ->
	let p'1,_ = wp p1 None in
	App (p'1, a, k), None
    | Lam (bl, p) ->
	let p',_ = wp p None in
	Lam (bl, p'), None
    | LetIn (x, _, _) | LetRef (x, _, _) when occur_post x q ->
        Report.raise_unlocated 
	  (AnyMessage ("cannot compute wp due to capture variable;\n" ^
                       "please rename variable " ^ Ident.string x))

    | LetIn (x, e1, e2) ->
	let e'2, w2 = wp e2 (filter_post e2.info q) in
	let q1 = optasst_app (subst_in_predicate (subst_onev x result)) w2 in
	let q1 = saturate_post e1.info q1 q in
	let e'1,w = wp e1 q1 in
	LetIn (x, e'1, e'2), w
    | LetRef (x, e1, e2) ->
	(* same as LetIn: correct? *)
	let e'2, w2 = wp e2 (filter_post e2.info q) in
	let q1 = optasst_app (subst_in_predicate (subst_onev x result)) w2 in
	let q1 = saturate_post e1.info q1 q in
	let e'1,w = wp e1 q1 in
	LetRef (x, e'1, e'2), w
    | Rec (f, bl, v, var, e) ->
	let e',_ = wp e None in
	Rec (f, bl, v, var, e'), None
    | While (b, inv, var, e) ->
	let b',_ = wp b None in
	let qbl = while_post_block info.env inv var e in
	let q = Annot.sup (Some qbl) q in (* exc. posts taken from [q] *)
	let e',_ = wp e q in
	While (b', inv, var, e'), inv (* None *)

    | Raise (id, None) ->
	(* $wp(raise E, _, R) = R$ *)
	d, option_app (fun (_,ql) -> List.assoc id ql) q
    | Raise (id, Some e) ->
        (* $wp(raise (E e), _, R) = wp(e, R, R)$ *)
	let make_post (_,ql) = let r = List.assoc id ql in (r, ql) in
	let qe = filter_post e.info (option_app make_post q) in
	let e',w = wp e qe in
	Raise (id, Some e'), w

    | Try (e, hl) ->
        (* $wp(try e1 with E -> e2, Q, R) = wp(e1, Q, wp(e2, Q, R))$ *)
	let subst w = function
	  | None -> w
	  | Some x -> optasst_app (subst_in_predicate (subst_onev x result)) w
	in
	let hl' = 
	  List.map (fun ((x,v) as p, h) -> 
		      let h',w = wp h (filter_post h.info q) in
		      (p,h'), (x, subst w v)) hl 
	in
	let hl',hwl = List.split hl' in
	let make_post (q,ql) = 
	  let hpost (x,r) =
	    x, 
	    try (match List.assoc x hwl with None -> r | Some w -> w)
	    with Not_found -> r
	  in
	  (q, List.map hpost ql)
	in
	let q = saturate_post e.info (option_app fst q) q in
	let qe = filter_post e.info (option_app make_post q) in
	let e',w = wp e qe in
	Try (e', hl'), w

    | Absurd ->
	Absurd, Some (anonymous info.loc Pfalse)

and wp_block bl q = match bl with
  | [] ->
      [], option_app post_val q
  | Statement p :: bl ->
      let bl', w = wp_block bl q in
      let w = saturate_post p.info w q in
      let p', w' = wp p w in
      Statement p' :: bl', w'
  | Label l :: bl ->
      let bl', w = wp_block bl q in
      Label l :: bl', optasst_app (erase_label l) w
  | Assert p :: bl ->
      let bl', w = wp_block bl q in
      Assert p :: bl', add_to_wp p.a_loc [p] w

let wp p = wp p None
