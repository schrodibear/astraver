(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: red.ml,v 1.8 2002-03-19 12:59:33 filliatr Exp $ i*)

open Ast
open Misc
open Util

let rec cc_subst subst = function
  | CC_var id as c -> 
      (try CC_expr (List.assoc id subst) with Not_found -> c)
  | CC_letin (b,bl,c1,c2) ->
      CC_letin (b, cc_subst_binders subst bl,
		cc_subst subst c1, cc_subst (cc_cross_binders subst bl) c2)
  | CC_lam (bl, c) ->
      CC_lam (cc_subst_binders subst bl, 
	      cc_subst (cc_cross_binders subst bl) c)
  | CC_app (c, cl) ->
      CC_app (cc_subst subst c, List.map (cc_subst subst) cl)
  | CC_tuple cl ->
      CC_tuple (List.map (cc_subst subst) cl)
  | CC_case (c, cl) ->
      CC_case (cc_subst subst c,
	       List.map (fun (bl,e) -> 
			   (cc_subst_binders subst bl,
			    cc_subst (cc_cross_binders subst bl) e)) cl)
  | CC_if (a,b,c) ->
      CC_if (cc_subst subst a, cc_subst subst b, cc_subst subst c)
  | CC_expr c ->
      CC_expr (tsubst_in_term subst c)
  | CC_hole ty ->
      CC_hole (tsubst_in_predicate subst ty)
  | CC_type t ->
      CC_type (cc_type_subst subst t)

and cc_subst_binders subst = List.map (cc_subst_binder subst)

and cc_subst_binder subst = function
  | id, CC_var_binder c -> id, CC_var_binder (cc_type_subst subst c)
  | id, CC_pred_binder c -> id, CC_pred_binder (tsubst_in_predicate subst c)
  | b -> b

and cc_cross_binders subst = function
  | [] -> subst
  | (id,_) :: bl -> cc_cross_binders (List.remove_assoc id subst) bl

and cc_type_subst subst = function
  | TTarray (t, tt) -> 
      TTarray (tsubst_in_term subst t, cc_type_subst subst tt)
  | TTlambda (b, tt) ->
      TTlambda (cc_subst_binder subst b,
		cc_type_subst (cc_cross_binders subst [b]) tt)
  | TTarrow (b, tt) -> 
      TTarrow (cc_subst_binder subst b, 
	       cc_type_subst (cc_cross_binders subst [b]) tt)
  | TTtuple (ttl, p) -> 
      let subst' = List.fold_right List.remove_assoc (List.map fst ttl) subst in
      TTtuple (List.map (fun (id,t) -> (id, cc_type_subst subst t)) ttl,
	       option_app (tsubst_in_predicate subst') p)
  | TTpure _ as t -> 
      t

(* here we only perform eta-reductions on programs to eliminate
 * redexes of the kind
 *
 *   let (x1,...,xn) = e in (x1,...,xn)  -->  e
 *
 *)

let is_eta_redex bl al =
  try
    List.for_all2
      (fun (id,_) t -> match t with CC_var id' -> id=id' | _ -> false)
      bl al
  with Invalid_argument("List.for_all2") -> 
    false

let is_expr = function CC_expr _ -> true | _ -> false

let is_iota_redex l1 l2 = 
  (List.length l1 = List.length l2) &&
  List.for_all is_expr l2

let rec iota_subst = function
  | [], [] -> []
  | (id,_) :: l1, CC_expr t :: l2 -> (id,t) :: iota_subst (l1, l2)
  | _ -> assert false

let rec red = function
  | CC_letin (_, [id,_], CC_expr c1, e2) ->
      red (cc_subst [id,c1] e2)
  | CC_letin (dep, bl, e1, e2) ->
      (match red e2 with
	 | CC_tuple al when is_eta_redex bl al ->
	     red e1
	 | re2 ->
	     (match red e1 with
		| CC_tuple al when is_iota_redex bl al ->
		    red (cc_subst (iota_subst (bl, al)) re2)
		| re1 ->
		    CC_letin (dep, bl, re1, re2)))
  | CC_lam (bl, e) ->
      CC_lam (bl, red e)
  | CC_app (e, al) ->
      CC_app (red e, List.map red al)
  | CC_case (e1, el) ->
      CC_case (red e1, List.map (fun (bl,e) -> (bl, red e)) el)
  | CC_if (a,b,c) ->
      CC_if (red a, red b, red c)
  | CC_tuple al ->
      CC_tuple (List.map red al)
  | CC_var _ | CC_hole _ | CC_expr _ | CC_type _ as e -> e


