
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: wp.ml,v 1.2 2001-08-19 02:44:48 filliatr Exp $ *)

open Ident
open Logic
open Misc
open Types
open Ast
open Util
open Env
open Effect
open Typing
open Rename

(* In this module:
 *  - we try to insert more annotations to achieve a greater completeness;
 *  - we recursively propagate annotations inside programs;
 *  - we normalize boolean expressions.
 *
 * The propagation schemas are the following:
 * 
 *  1. (f a1 ... an)  ->  (f a1 ... an) {Qf} if the ai are functional
 *
 *  2. (if e1 then e2 else e3) {Q}  ->  (if e1 then e2 {Q} else e3 {Q}) {Q}
 * 
 *  3. (let x = e1 in e2) {Q}  ->  (let x = e1 in e2 {Q}) {Q}
 *)

(* force a post-condition *)
let update_post env top ef c =
  let i,o = Effect.get_repr ef in
  let al = 
    Idset.fold
      (fun id l -> 
	 if is_mutable_in_env env id then
	   if is_write ef id then l else (id,at_id id "")::l
	 else if is_at id then
	   let (uid,d) = un_at id in
	   if is_mutable_in_env env uid && d="" then 
	     (id,at_id uid top) :: l 
	   else 
	     l
	 else
	   l) 
      (predicate_vars c) []
  in
  subst_in_predicate al c
  
let force_post up env top q e =
  let ef = e.info.kappa.c_effect in
  let q' = 
    if up then option_app (named_app (update_post env top ef)) q else q 
  in
  let c' = { e.info.kappa with c_post = q' } in
  let i = { env = e.info.env; kappa = c' } in
  { desc = e.desc; pre = e.pre; post = q'; loc = e.loc; info = i }

(* put a post-condition if none is present *)
let post_if_none_up env top q = function
  | { post = None } as p -> force_post true env top q p 
  | p -> p

let post_if_none env q = function
  | { post = None } as p -> force_post false env "" q p 
  | p -> p

(* [annotation_candidate p] determines if p is a candidate for a 
 * post-condition *)

let annotation_candidate = function
  | { desc = If _ | LetIn _ | LetRef _ ; post = None } -> true
  | _ -> false

(* [extract_pre p] erase the pre-condition of p and returns it *)
let extract_pre pr =
  { desc = pr.desc; pre = []; post = pr.post; loc = pr.loc;
    info = { env = pr.info.env; kappa = { pr.info.kappa with c_pre = [] } } },
  pr.info.kappa.c_pre

(* adds some pre-conditions *)
let add_pre p1 pr =
  let k = pr.info.kappa in
  let p' = p1 @ k.c_pre in
  { desc = pr.desc; pre = p'; post = pr.post; loc = pr.loc;
    info = { env = pr.info.env; kappa = { k with c_pre = p' } } }
  
(* change the statement *)
let change_desc p d =
  { desc = d; pre = p.pre; post = p.post; loc = p.loc; info = p.info }

let create_bool_post c =
  Some { a_value = c; a_name = Name (bool_name()) }

(* [normalize_boolean b] checks if the boolean expression b (of type bool) is 
 * annotated, and if it is not the case tries to add the annotation
 * (if result then c=true else c=false) if b is an expression c.
 *)

let is_bool = function
  | PureType PTbool -> true
  | _ -> false

let normalize_boolean ren env b =
  let k = b.info.kappa in
  Error.check_no_effect b.loc k.c_effect;
  if is_bool k.c_result_type then
    let q = k.c_post in
    match q with
      | Some _ ->
	  (* il y a une annotation : on se contente de lui forcer un nom *)
	  let q = force_bool_name q in
	  { b with post = q;
  	           info = { b.info with kappa = { k with c_post = q } } }
      | None -> begin
	  (* il n'y a pas d'annotation : on cherche à en mettre une *)
	  match b.desc with
	    | Expression c ->
		let q = 
		  Pif (Pterm (Tvar Ident.result),
		       Pterm (equals_true c),
		       Pterm (equals_false c))
		in
		let q = Some { a_value = q; a_name = Name (bool_name ()) } in
		{ b with post = q; 
                         info = { b.info with kappa = { k with c_post = q } } }
	    | _ -> b
	end
  else
    Error.should_be_boolean b.loc

(* [decomp_boolean c] returns the specs R and S of a boolean expression *)

let decomp_boolean = function
  | Some { a_value = q } ->
      tsubst_in_predicate [Ident.result, Tconst (ConstBool true)] q,
      tsubst_in_predicate [Ident.result, Tconst (ConstBool false)] q
(*i
      Reduction.whd_betaiota (Term.applist (q, [constant "true"])),
      Reduction.whd_betaiota (Term.applist (q, [constant "false"]))
i*)
  | _ -> invalid_arg "Typing.decomp_boolean"

let result_eq_true = 
  Pterm (Tapp (t_eq, [Tvar result; Tconst (ConstBool true)]))

let result_eq_false = 
  Pterm (Tapp (t_eq, [Tvar result; Tconst (ConstBool false)]))

let spec_and r1 s1 r2 s2 =
  Pand (Pimplies (result_eq_true, Pand (r1, r2)),
	Pimplies (result_eq_false, Por (s1, s2)))

let spec_or r1 s1 r2 s2 =
  Pand (Pimplies (result_eq_true, Por (r1, r2)),
	Pimplies (result_eq_false, Pand (s1, s2)))

let spec_not r s =
  Pand (Pimplies (result_eq_true, s), Pimplies (result_eq_false, r))

(* top point of a program *)

let top_point = function
  | PPoint (s,_) as p -> s,p
  | p -> let s = label_name() in s, PPoint(s,p)

let top_point_block = function
  | (Label s :: _) as b -> s,b
  | b -> let s = label_name() in s, (Label s)::b

(*i let abstract_unit q = abstract [result_id,constant "unit"] q i*)

(* [add_decreasing env ren ren' phi r bl] adds the decreasing condition
 *    phi(ren') r phi(ren)
 * to the last assertion of the block [bl], which is created if needed
 *)

let add_decreasing env inv (var,r) lab bl =
  let ids = term_now_vars env var in
  let al = Idset.fold (fun id l -> (id,at_id id lab) :: l) ids [] in
  let var_lab = subst_in_term al var in
  let dec = Pterm (applist r [var;var_lab]) in
  let post = match inv with
    | None -> anonymous dec
    | Some i -> { a_value = Pand (dec, i.a_value); a_name = i.a_name }
  in
  bl @ [ Assert post ]

(* [post_last_statement env top q bl] annotates the last statement of the
 * sequence bl with q if necessary *)

let post_last_statement env top q bl =
  match List.rev bl with
    | Statement e :: rem when annotation_candidate e -> 
	List.rev ((Statement (post_if_none_up env top q e)) :: rem)
    | _ -> bl

(* [propagate_desc] moves the annotations inside the program 
 * info is the typing information coming from the outside annotations *)
let rec propagate_desc ren info d = 
  let env = info.env in
  let p = info.kappa.c_pre in
  let q = info.kappa.c_post in
  match d with
    | If (e1,e2,e3) ->
      (* propagation number 2 *)
	let e1' = normalize_boolean ren env (propagate ren e1) in
	if e2.post = None || e3.post = None then
	  let top = label_name() in
	  let ren' = push_date ren top in
	  PPoint (top, If (e1', 
			   propagate ren' (post_if_none_up env top q e2),
			   propagate ren' (post_if_none_up env top q e3)))
	else
	  If (e1', propagate ren e2, propagate ren e3)
    | Aff (x,e) ->
      	Aff (x, propagate ren e)
    | TabAcc (ch,x,e) ->
      	TabAcc (ch, x, propagate ren e)
    | TabAff (ch,x,({desc=Expression c} as e1),e2) ->
	let p = make_pre_access ren env x c in
	let e1' = add_pre [(anonymous_pre true p)] e1 in
      	TabAff (false, x, propagate ren e1', propagate ren e2)
    | TabAff (ch,x,e1,e2) ->
      	TabAff (ch, x, propagate ren e1, propagate ren e2)
    | App (f,l) ->
      	App (propagate ren f, List.map (propagate_arg ren) l)
    | SApp (f,l) ->
	let l = 
	  List.map (fun e -> normalize_boolean ren env (propagate ren e)) l
	in
      	SApp (f, l)
    | Lam (bl,e) ->
      	Lam (bl, propagate ren e)
    | Seq bl ->
	let top,bl = top_point_block bl in
	let bl = post_last_statement env top q bl in
      	Seq (propagate_block ren env bl)
    | While (b,inv,var,bl) ->
	let b = normalize_boolean ren env (propagate ren b) in
	let lab,bl = top_point_block bl in
	let bl = add_decreasing env inv var lab bl in
      	While (b,inv,var,propagate_block ren env bl)
    | LetRef (x,e1,e2) ->
	let top = label_name() in
	let ren' = push_date ren top in
	PPoint (top, LetRef (x, propagate ren' e1, 
	      		     propagate ren' (post_if_none_up env top q e2)))
    | LetIn (x,e1,e2) ->
	let top = label_name() in
	let ren' = push_date ren top in
      	PPoint (top, LetIn (x, propagate ren' e1, 
			    propagate ren' (post_if_none_up env top q e2)))
    | LetRec (f,bl,v,var,e) ->
      	LetRec (f, bl, v, var, propagate ren e)
    | PPoint (s,d) -> 
      	PPoint (s, propagate_desc ren info d)
    | Debug _ | Var _ 
    | Acc _ | Expression _ as d -> d
	  

(* [propagate] adds new annotations if possible *)
and propagate ren p =
  let env = p.info.env in
  let p = match p.desc with
    | App (f,l) ->
	let _,(_,so,ok),capp = effect_app ren env f l in
	let qapp = capp.c_post in
	if ok then
	  let q = option_app (named_app (tsubst_in_predicate so)) qapp in
	  post_if_none env q p
	else
	  p
    | _ -> p
  in
  let d = propagate_desc ren p.info p.desc in
  let p = change_desc p d in
  match d with
    | Aff (x,e) ->
	let e1,p1 = extract_pre e in
	change_desc (add_pre p1 p) (Aff (x,e1))

    | TabAff (check, x, ({ desc = Expression _ } as e1), e2) ->
	let e1',p1 = extract_pre e1 in
	let e2',p2 = extract_pre e2 in
	change_desc (add_pre (p1@p2) p) (TabAff (check,x,e1',e2'))

    | While (b,inv,_,_) ->
	let _,s = decomp_boolean b.post in
	let s = make_before_after s in
	let q = match inv with
	    None -> Some (anonymous s)
	  | Some i -> Some { a_value = Pand (i.a_value, s); a_name = i.a_name }
	in
	(*i let q = option_app (named_app abstract_unit) q in i*)
	post_if_none env q p

    | SApp ([Var id], [e1;e2]) when id == p_and || id == p_or ->
	let q1 = e1.info.kappa.c_post 
	and q2 = e2.info.kappa.c_post in
	let (r1,s1) = decomp_boolean q1
	and (r2,s2) = decomp_boolean q2 in
	let q =
	  let c = (if id == p_and then spec_and else spec_or) r1 s1 r2 s2 in
	  create_bool_post c
	in
	post_if_none env q p

    | SApp ([Var id], [e1]) when id == p_not ->
	let q1 = e1.info.kappa.c_post in
	let (r1,s1) = decomp_boolean q1 in
	let q = create_bool_post (spec_not r1 s1) in
	post_if_none env q p

    | _ -> p

and propagate_arg ren = function
  | Type _ | Refarg _ as a -> a
  | Term e -> Term (propagate ren e)


and propagate_block ren env = function 
  | [] -> 
      []
  | (Statement p) :: (Assert q) :: rem when annotation_candidate p ->
      let q' =
	(*i let ((id,v),_,_,_) = p.info.kappa in
	let tv = Monad.trad_ml_type_v ren env v in
	named_app (abstract [id,tv]) i*) q
      in
      let p' = post_if_none env (Some q') p in
      (Statement (propagate ren p')) :: (Assert q) 
      :: (propagate_block ren env rem)
  | (Statement p) :: rem ->
      (Statement (propagate ren p)) :: (propagate_block ren env rem)
  | (Label s as x) :: rem ->
      x :: propagate_block (push_date ren s) env rem
  | x :: rem ->
      x :: propagate_block ren env rem
