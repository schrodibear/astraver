(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: red.ml,v 1.12 2002-04-15 13:29:19 filliatr Exp $ i*)

open Ast
open Logic
open Ident
open Misc
open Util

(*s Here we only perform eta-reductions on programs to eliminate
    redexes of the kind [let (x1,...,xn) = e in (x1,...,xn)] *)

(*s Traversing binders and substitution within CC types *)

let rec cc_subst_binder s (id,b) = 
  let b' = match b with 
    | CC_var_binder c -> CC_var_binder (cc_type_subst s c)
    | CC_pred_binder c -> CC_pred_binder (tsubst_in_predicate s c)
    | CC_untyped_binder -> CC_untyped_binder
  in
  (id,b'), Idmap.remove id s

and cc_subst_binders s = function
  | [] -> 
      [], s
  | b :: bl -> 
      let b',s' = cc_subst_binder s b in 
      let bl',s'' = cc_subst_binders s' bl in
      b'::bl', s''

and cc_type_subst s = function
  | TTarray (t, tt) -> 
      TTarray (tsubst_in_term s t, cc_type_subst s tt)
  | TTlambda (b, tt) ->
      let b',s' = cc_subst_binder s b in TTlambda (b', cc_type_subst s' tt)
  | TTarrow (b, tt) -> 
      let b',s' = cc_subst_binder s b in TTarrow (b', cc_type_subst s' tt)
  | TTtuple (ttl, p) -> 
      let s' = List.fold_right Idmap.remove (List.map fst ttl) s in
      TTtuple (List.map (fun (id,t) -> (id, cc_type_subst s t)) ttl,
	       option_app (tsubst_in_predicate s') p)
  | TTpure _ as t -> 
      t

(*s Eta and iota redexes. *)

let is_eta_redex bl al =
  try
    List.for_all2
      (fun (id,_) t -> match t with CC_var id' -> id=id' | _ -> false)
      bl al
  with Invalid_argument "List.for_all2" -> 
    false

let is_term = function CC_term _ -> true | _ -> false

let dterm = function CC_term t -> t | _ -> assert false

let is_iota_redex l1 l2 = 
  (List.length l1 = List.length l2) && List.for_all is_term l2

let rec iota_subst s = function
  | [], [] -> s
  | (id,_) :: l1, CC_term t :: l2 -> iota_subst (Idmap.add id t s) (l1, l2)
  | _ -> assert false

(*s Reduction. Substitution is done at the same time for greater efficiency *)

let rec red s = function
  | CC_var x ->
      CC_term (try Idmap.find x s with Not_found -> Tvar x)
  | CC_letin (dep, bl, e1, e2) ->
      (match red s e1 with
	 (* [let x = t1 in e2] *)
	 | CC_term t1 when List.length bl = 1 ->
	     red (Idmap.add (fst (List.hd bl)) t1 s) e2
	 (* [let (x1,...,xn) = (t1,...,tn) in e2] *)
	 | CC_tuple al when is_iota_redex bl al ->
	     red (iota_subst s (bl, al)) e2
	 | re1 ->
	     let bl',s' = cc_subst_binders s bl in
	     (match red s' e2 with
		(* [let (x1,...,xn) = e1 in (x1,...,xn)] *)
		| CC_tuple al when is_eta_redex bl al ->
		    red s e1
		| re2 ->
		    CC_letin (dep, bl', re1, re2)))
  | CC_lam (b, e) ->
      let b',s' = cc_subst_binder s b in
      CC_lam (b', red s' e)
  | CC_app (e, al) ->
      let al' = List.map (red s) al in
      (match red s e with
	 | CC_term t when List.for_all is_term al' ->
	     CC_term (applist t (List.map dterm al'))
	 | _ -> 
	     CC_app (red s e, List.map (red s) al))
  | CC_case (e1, el) ->
      let red_branch (bl,e) = 
	let bl',s' = cc_subst_binders s bl in (bl', red s' e)
      in
      CC_case (red s e1, List.map red_branch el)
  | CC_if (a,b,c) ->
      CC_if (red s a, red s b, red s c)
  | CC_tuple al ->
      CC_tuple (List.map (red s) al)
  | CC_term c ->
      CC_term (tsubst_in_term s c)
  | CC_hole ty ->
      CC_hole (tsubst_in_predicate s ty)
  | CC_type t ->
      CC_type (cc_type_subst s t)


let red = red Idmap.empty
