(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(*i $Id: wp.ml,v 1.60 2002-10-15 09:05:53 filliatr Exp $ i*)

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
  let set_post x = x, try List.assoc x ql with Not_found -> anonymous Ptrue in
  let xs = get_exns k.kappa.c_effect in
  let saturate a = (a, List.map set_post xs) in
  option_app saturate a

let need_a_post p = 
  post p = None && match p.desc with Lam _ | Rec _ -> false | _ -> true

(*s WP. [wp p q] computes the weakest precondition [wp(p,q)]
    and gives postcondition [q] to [p] if necessary.

    wp: typed_program -> postcondition option -> assertion option *)

let rec wp p q =
  let env = p.info.env in
  let lab = p.info.label in
  let postp = post p in
  let q0 = if postp = None then q else postp in
  let q0 = optpost_app (change_label "" lab) q0 in
  let d,w = wp_desc p.info p.desc q0 in
  let p = change_desc p d in
  let w = option_app (named_app (erase_label lab)) w in
  let p = if need_a_post p then force_post env q0 p else p in
  let w = match postp, q with
    | Some ({a_value=q'}, []), Some ({a_value=q}, []) ->
	let vars = (result, result_type p) :: (output p) in
	let w = foralls vars (Pimplies (q', q)) in
	Some (anonymous (erase_label lab w))
    | Some _, Some _ ->
	assert false
    | _ -> 
	w
  in
  p, w

and wp_desc info d q = 
  let result = info.kappa.c_result_name in
  match d with
    (* TODO: check if likely *)
    | Var x ->
	let w = optpost_val q in
	d, optnamed_app (tsubst_in_predicate (subst_one result (Tvar x))) w
    (* $wp(E,q) = q[result \leftarrow E]$ *)
    | Expression t ->
	let w = optpost_val q in
	d, optnamed_app (tsubst_in_predicate (subst_one result t)) w
    (* $wp(!x,q) = q[result \leftarrow x]$ *)
    | Acc x ->
	let w = optpost_val q in
	d, optnamed_app (subst_in_predicate (subst_onev result x)) w
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
    | TabAff (ck, x, e1, e2) ->
	(* TODO: does not propagate inside [e1] *)
	let q = optpost_app (tsubst_in_predicate (subst_one result tvoid)) q in
	let v = fresh_var () in
	let st = make_raw_store info.env (x,x) (Tvar result) (Tvar v) in
	let q1 = optpost_app (tsubst_in_predicate (subst_one x st)) q in
	let q1 = filter_post e1.info q1 in
	let _,w1 = wp e1 q1 in
	let e'1,_ = wp e1 None in
	let w1 = optnamed_app (subst_in_predicate (subst_onev v result)) w1 in
	let q2 = saturate_post e2.info w1 q in
	let e'2,w2 = wp e2 q2 in
	TabAff (ck, x, e'1, e'2), w2
    (* conditional: two cases depending on [p1.post] *)
    | If (p1, p2, p3) ->
	let p'2,w2 = wp p2 (filter_post p2.info q) in
	let p'3,w3 = wp p3 (filter_post p3.info q) in
	(match w2, w3, post p1 with
	   | Some {a_value=q2}, Some {a_value=q3}, _ -> 
	       (* $wp(if p1 then p2 else p3, q) = 
		  wp(p1, if result then wp(p2, q) else wp(p3, q))$ *)
	       let result1 = p1.info.kappa.c_result_name in
	       let q1 = create_postval (Pif (Tvar result1, q2, q3)) in
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
	let q1 = optnamed_app (subst_in_predicate (subst_onev x result)) w2 in
	let q1 = saturate_post e1.info q1 q in
	let e'1,w = wp e1 q1 in
	LetIn (x, e'1, e'2), w
    | LetRef (x, e1, e2) ->
	(* same as LetIn: correct? *)
	let e'2, w2 = wp e2 (filter_post e2.info q) in
	let q1 = optnamed_app (subst_in_predicate (subst_onev x result)) w2 in
	let q1 = saturate_post e1.info q1 q in
	let e'1,w = wp e1 q1 in
	LetRef (x, e'1, e'2), w
    | Rec (f, bl, v, var, e) ->
	let e',_ = wp e None in
	Rec (f, bl, v, var, e'), None
    | While (b, inv, var, e) ->
	let b',_ = wp b None in
	let q = while_post_block info.env inv var e in
	let e',_ = wp e (Some q) in
	While (b', inv, var, e'), None
    (* $wp(raise E, _, R) = R$ *)
    | Raise (id, None) ->
	d, option_app (fun (_,ql) -> List.assoc id ql) q
    (* $wp(raise (E e), _, R) = wp(e, R, R)$ *)
    | Raise (id, Some e) ->
	let make_post (_,ql) = let r = List.assoc id ql in (r, ql) in
	let qe = filter_post e.info (option_app make_post q) in
	let e',w = wp e qe in
	Raise (id, Some e'), w
    (* $wp(try e1 with E -> e2, Q, R) = wp(e1, Q, wp(e2, Q, R))$ *)
    | Try (e, hl) ->
	let subst w = function
	  | None -> w
	  | Some x -> optnamed_app (subst_in_predicate (subst_onev x result)) w
	in
	let hl' = 
	  List.map (fun ((x,v) as p, h) -> 
		      let h',w = wp h (filter_post h.info q) in
		      (p,h'), (x, subst w v)) hl 
	in
	let hl',hwl = List.split hl' in
	let make_post (q,ql) = 
	  let hpost (x,r) =
	    x, try (match List.assoc x hwl with None -> r | Some w -> w)
	       with Not_found -> r
	  in
	  (q, List.map hpost ql)
	in
	let q = saturate_post e.info (option_app fst q) q in
	let qe = filter_post e.info (option_app make_post q) in
	let e',w = wp e qe in
	Try (e', hl'), w

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
      Label l :: bl', optnamed_app (erase_label l) w
  | Assert p :: bl ->
      let bl', w = wp_block bl q in
      Assert p :: bl', optnamed_app (fun c -> pand p.a_value c) w

let wp p = wp p None
