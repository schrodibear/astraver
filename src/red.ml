
(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(* $Id: red.ml,v 1.2 2001-08-19 02:44:48 filliatr Exp $ *)

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
  | CC_expr c ->
      CC_expr (tsubst_in_term subst c)
  | CC_hole ty ->
      CC_hole (tsubst_in_predicate subst ty)

and cc_subst_binders subst = List.map (cc_subst_binder subst)

and cc_subst_binder subst = function
  | id,CC_var_binder c -> id, CC_var_binder (type_v_rsubst subst c)
  | id,CC_pred_binder c -> id, CC_pred_binder (tsubst_in_predicate subst c)
  | b -> b

and cc_cross_binders subst = function
  | [] -> subst
  | (id,_) :: bl -> cc_cross_binders (List.remove_assoc id subst) bl

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

let rec red = function
  | CC_letin (_, [id,_], CC_expr c1, e2) ->
      red (cc_subst [id,c1] e2)
  | CC_letin (dep, bl, e1, e2) ->
      begin match red e2 with
	| CC_tuple al ->
	    if is_eta_redex bl al then
	      red e1
	    else
	      CC_letin (dep, bl, red e1,
			CC_tuple (List.map red al))
	| e -> 
	    CC_letin (dep, bl, red e1, e)
      end
  | CC_lam (bl, e) ->
      CC_lam (bl, red e)
  | CC_app (e, al) ->
      CC_app (red e, List.map red al)
  | CC_case (e1, el) ->
      CC_case (red e1, List.map (fun (bl,e) -> (bl, red e)) el)
  | CC_tuple al ->
      CC_tuple (List.map red al)
  | e -> e


(* How to reduce uncomplete proof terms when they have become constr *)
(*i
open Term
open Reduction

(* Il ne faut pas reduire de redexe (beta/iota) qui impliquerait
 * la substitution d'une m�tavariable.
 * 
 * On commence par rendre toutes les applications binaire (strong bin_app)
 * puis on applique la reduction sp�ciale programmes d�finie dans
 * typing/reduction *)

(*i
let bin_app = function
  | DOPN(AppL,v) as c ->
      (match Array.length v with
	 | 1 -> v.(0)
	 | 2 -> c
	 | n ->
	     let f = DOPN(AppL,Array.sub v 0 (pred n)) in
	     DOPN(AppL,[|f;v.(pred n)|]))
  | c -> c
i*)

let red_cci c = 
  (*i let c = strong bin_app c in i*) 
  strong whd_programs (Global.env ()) Evd.empty c

i*)
