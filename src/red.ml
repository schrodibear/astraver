(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: red.ml,v 1.25 2002-09-18 06:12:19 filliatr Exp $ i*)

open Ast
open Logic
open Ident
open Misc
open Util
open Cc

(*s Reductions of interpretations. *)

(*s We proceed in two phases (simpler without de Bruijn indices).
    (1) first we rename bound variables, so that successive binders have 
        different names;
    (2) then we reduce, performing substitutions without possible captures *)

(*s Phase 1: Renaming of bound variables. Argument [fv] is the set of 
    already traversed binders (a set of identifiers) *)

let rec uniq_tt fv s = function
  | TTarray (t, tt) -> 
      TTarray (tsubst_in_term s t, uniq_tt fv s tt)
  | TTlambda (b, tt) ->
      let b',fv',s' = uniq_binder fv s b in TTlambda (b', uniq_tt fv' s' tt)
  | TTarrow (b, tt) -> 
      let b',fv',s' = uniq_binder fv s b in TTarrow (b', uniq_tt fv' s' tt)
  | TTtuple (bl, p) -> 
      let bl',fv',s' = uniq_binders fv s bl in
      TTtuple (bl', option_app (uniq_tt fv' s') p)
  | TTpred p ->
      TTpred (tsubst_in_predicate s p)
  | TTpure _ as t -> 
      t
  | TTapp (id, l) ->
      TTapp (id, List.map (uniq_tt fv s) l)

and uniq_binder fv s (id,b) =
  let b' = match b with 
    | CC_var_binder c -> CC_var_binder (uniq_tt fv s c)
    | CC_pred_binder c -> CC_pred_binder (tsubst_in_predicate s c)
    | CC_untyped_binder -> CC_untyped_binder
  in
  let id' = next_away id fv in
  if id' <> id then 
    (id',b'), Idset.add id' fv, Idmap.add id (Tvar id') s 
  else 
    (id,b'), Idset.add id fv, s

and uniq_binders fv s = function
  | [] -> 
      [], fv, s
  | b :: bl -> 
      let b',fv',s' = uniq_binder fv s b in 
      let bl',fv'',s'' = uniq_binders fv' s' bl in
      b' :: bl', fv'', s''

let rec uniq_cc fv s = function
  | CC_var x | CC_term (Tvar x) ->
      CC_term (try Idmap.find x s with Not_found -> Tvar x)
  | CC_letin (dep, bl, e1, e2) ->
      let bl',fv',s' = uniq_binders fv s bl in
      CC_letin (dep, bl', uniq_cc fv s e1, uniq_cc fv' s' e2)
  | CC_lam (b, e) ->
      let b',fv',s' = uniq_binder fv s b in
      CC_lam (b', uniq_cc fv' s' e)
  | CC_app (f, a) ->
      CC_app (uniq_cc fv s f, uniq_cc fv s a)
  | CC_if (a,b,c) ->
      CC_if (uniq_cc fv s a, uniq_cc fv s b, uniq_cc fv s c)
  | CC_tuple (al, po) ->
      CC_tuple (List.map (uniq_cc fv s) al, option_app (uniq_tt fv s) po)
  | CC_case (e,pl) ->
      CC_case (uniq_cc fv s e, List.map (fun (p,e) -> (p, uniq_cc fv s e)) pl)
  | CC_term c ->
      CC_term (tsubst_in_term s c)
  | CC_hole ty ->
      CC_hole (tsubst_in_predicate s ty)
  | CC_type t ->
      CC_type (uniq_tt fv s t)


(*s Phase 2: we reduce. *)

(*s Occurrence in the range of a substitution *)

let in_rng id s =
  try
    Idmap.iter (fun _ t -> if occur_term id t then raise Exit) s; false
  with Exit ->
    true

(*s Traversing binders and substitution within CC types *)

let rec cc_subst_binder_type s = function
  | CC_var_binder c -> CC_var_binder (cc_type_subst s c)
  | CC_pred_binder c -> CC_pred_binder (tsubst_in_predicate s c)
  | CC_untyped_binder -> CC_untyped_binder

and cc_subst_binder s (id,b) = (id, cc_subst_binder_type s b)

and cc_subst_binders s = List.map (cc_subst_binder s)

and cc_type_subst s = function
  | TTarray (t, tt) -> 
      TTarray (tsubst_in_term s t, cc_type_subst s tt)
  | TTlambda (b, tt) ->
      let b' = cc_subst_binder s b in TTlambda (b', cc_type_subst s tt)
  | TTarrow (b, tt) -> 
      let b' = cc_subst_binder s b in TTarrow (b', cc_type_subst s tt)
  | TTtuple (bl, p) -> 
      let bl' = cc_subst_binders s bl in
      TTtuple (bl', option_app (cc_type_subst s) p)
  | TTpred p ->
      TTpred (tsubst_in_predicate s p)
  | TTpure _ as t -> 
      t
  | TTapp (id, l) ->
      TTapp (id, List.map (cc_type_subst s) l)

(*s Eta and iota redexes. *)

let is_eta_redex bl al =
  try
    List.for_all2
      (fun (id,_) t -> match t with CC_var id' -> id = id' | _ -> false)
      bl al
  with Invalid_argument "List.for_all2" -> 
    false

let is_term = function CC_term _ -> true | _ -> false

let is_iota_redex l1 l2 = 
  (List.length l1 = List.length l2) && List.for_all is_term l2

let rec iota_subst s = function
  | [], [] -> s
  | (id,_) :: l1, CC_term t :: l2 -> iota_subst (Idmap.add id t s) (l1, l2)
  | _ -> assert false

(*s Reduction. Substitution is done at the same time for greater efficiency *)

let rec red sp s cct = 
  match cct with
  | CC_var x | CC_term (Tvar x) ->
      (try Idmap.find x sp 
       with Not_found -> CC_term (try Idmap.find x s with Not_found -> Tvar x))
  | CC_letin (dep, bl, e1, e2) ->
      (match red sp s e1 with
	 (* [let x = t1 in e2] *)
	 | CC_term t1 when List.length bl = 1 ->
	     red sp (Idmap.add (fst (List.hd bl)) t1 s) e2
         (* [let x = [_]_ in e2] *)
	 | CC_lam _ as re1 when List.length bl = 1 ->
	     red (Idmap.add (fst (List.hd bl)) re1 sp) s e2
	 (* [let (x1,...,xn) = (t1,...,tn) in e2] *)
	 | CC_tuple (al,_) when is_iota_redex bl al ->
	     red sp (iota_subst s (bl, al)) e2
	 | re1 ->
	     let bl' = cc_subst_binders s bl in
	     (match red sp s e2 with
		(* [let (x1,...,xn) = e1 in (x1,...,xn)] *)
		| CC_tuple (al,_) when is_eta_redex bl al ->
		    red sp s e1
		| re2 ->
		    CC_letin (dep, bl', re1, re2)))
  | CC_lam (b, e) ->
      let b' = cc_subst_binder s b in
      CC_lam (b', red sp s e)
  | CC_app (f, a) ->
      (match red sp s f, red sp s a with
	 (* two terms *)
	 | CC_term tf, CC_term ta ->
	     CC_term (applist tf [ta])
	 (* beta-redex *)
	 | CC_lam ((x,_),e) as rf, CC_term ta ->
	     red sp (Idmap.add x ta s) e
	 | CC_lam ((x,_),e) as rf, ra ->
	     red (Idmap.add x ra sp) s e
	 | rf, ra -> 
	     CC_app (rf, ra))
  | CC_if (a, b, c) ->
      CC_if (red sp s a, red sp s b, red sp s c)
  | CC_case (e, pl) ->
      CC_case (red sp s e, List.map (fun (p,e) -> (p, red sp s e)) pl)
  | CC_tuple (al, po) ->
      CC_tuple (List.map (red sp s) al,	option_app (cc_type_subst s) po)
  | CC_term c ->
      CC_term (tsubst_in_term s c)
  | CC_hole ty ->
      CC_hole (tsubst_in_predicate s ty)
  | CC_type t ->
      CC_type (cc_type_subst s t)


let red c = 
  let c' = uniq_cc Idset.empty Idmap.empty c in
  red Idmap.empty Idmap.empty c'

