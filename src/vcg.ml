
(*s Verification Conditions Generator. *)

open Logic
open Types
open Ast

type context_element =
  | Svar of Ident.t * type_v
  | Spred of predicate

type sequent = context_element list * predicate

type obligation = string * sequent

let vcg base t =
  let po = ref [] in
  let cpt = ref 0 in
  let push ctx p = 
    incr cpt;
    let id = base ^ "_po_" ^ string_of_int !cpt in
    po := (id, (List.rev ctx, p)) :: !po 
  in
  let rec traverse ctx = function
    | CC_var _ -> 
	()
    | CC_letin (_, bl, e1, e2) -> 
	traverse ctx e1; traverse (traverse_binders ctx bl) e2
    | CC_lam (bl, e) ->
	traverse (traverse_binders ctx bl) e
    | CC_app (e, el) ->
	traverse ctx e; List.iter (traverse ctx) el
    | CC_tuple el ->
	List.iter (traverse ctx) el
    | CC_case (e, pl) ->
	traverse ctx e;
	List.iter (fun (bl,e) -> traverse (traverse_binders ctx bl) e) pl
    | CC_expr _ -> 
	()
    | CC_hole p -> 
	push ctx p
  and traverse_binder ctx = function
    | id, CC_var_binder v -> (Svar (id,v)) :: ctx
    | _,  CC_pred_binder p -> (Spred p) :: ctx
    | id, CC_untyped_binder -> assert false
  and traverse_binders ctx = List.fold_left traverse_binder ctx
  in
  traverse [] t;
  List.rev !po

