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

(*i $Id: misc.ml,v 1.95 2004-07-13 14:55:41 filliatr Exp $ i*)

open Options
open Ident
open Logic
open Types 
open Ast
open Ptree
open Cc

(*s Utility functions. *)

let map_succeed f = 
  let rec map_f = function 
    | [] -> []
    | h :: t -> try let x = f h in x :: map_f t with Failure _ -> map_f t
  in 
  map_f 

let option_app f = function None -> None | Some x -> Some (f x)

let option_iter f = function None -> () | Some x -> f x

let option_fold f x c = match x with None -> c | Some x -> f x c 

let list_of_some = function None -> [] | Some x -> [x]

let if_labelled f id = if is_at id then f (un_at id)

let difference l1 l2 =
  let rec diff = function
    | [] -> []
    | a::rem -> if List.mem a l2 then diff rem else a::(diff rem)
  in
  diff l1

let rec list_combine3 a b c = match a, b, c with
  | [], [], [] -> []
  | xa::ra, xb::rb, xc::rc -> (xa, xb, xc) :: list_combine3 ra rb rc
  | _ -> invalid_arg "list_combine3"

let rec list_first f = function
  | [] -> raise Exit
  | x :: l -> try f x with Exit -> list_first f l

(*s Functions on names *)

type avoid = Ident.set

let renaming_of_ids avoid ids =
  let rec rename avoid = function
    | [] -> 
	[], avoid
    | x :: rem ->
	let al,avoid = rename avoid rem in
	let x' = Ident.next_away x avoid in
	(x,x')::al, Idset.add x' avoid
  in
  rename avoid ids

(*s hypotheses names *)

let next s r = function
  | Anonymous -> incr r; Ident.create (s ^ string_of_int !r)
  | Name id -> id

let reset_names_table = ref []
let reset_names () = List.iter (fun f -> f ()) !reset_names_table

let gen_sym_name s =
  let r = ref 0 in 
  reset_names_table := (fun () -> r := 0) :: !reset_names_table;
  next s r

let gen_sym s = let g = gen_sym_name s in fun () -> g Anonymous

let pre_name = gen_sym_name "Pre"
let post_name = gen_sym_name "Post"
let inv_name = gen_sym_name "Inv"
let test_name = gen_sym_name "Test"
let wp_name = gen_sym "WP"
let bool_name = gen_sym "Bool"
let variant_name = gen_sym "Variant"
let phi_name = gen_sym "rphi"
let for_name = gen_sym "for"
let label_name = let f = gen_sym "_label_" in fun () -> Ident.string (f ())
let fresh_hyp = gen_sym "HW_"
let fresh_axiom = gen_sym "AXIOM_"
let fresh_var = gen_sym "aux_"
let fresh_c_var = gen_sym "c_aux_"
let wf_name = gen_sym "wf"

let id_of_name = function Name id -> id | Anonymous -> default

let is_post id =
  let s = Ident.string id in
  String.length s >= 4 && String.sub s 0 4 = "Post"

let post_name_from = 
  let avoid = ref Idset.empty in
  reset_names_table := (fun () -> avoid := Idset.empty) :: !reset_names_table;
  function
  | Anonymous ->
      post_name Anonymous
  | Name id when is_post id ->
      post_name Anonymous
  | Name id -> 
      let id' = Ident.next_away id !avoid in
      avoid := Idset.add id' !avoid;
      id'

let warning s = Format.eprintf "warning: %s@\n" s
let wprintf loc f = 
  Format.eprintf "%awarning: " Loc.report loc; Format.eprintf f
let unlocated_wprintf f = 
  Format.eprintf "warning: "; Format.eprintf f

(*s Various utility functions. *)

let rec is_closed_pure_type = function
  | PTint | PTbool | PTreal | PTunit -> true
  | PTarray pt -> is_closed_pure_type pt
  | PTvarid _ | PTvar {type_val=None} -> false
  | PTvar {type_val=Some t} -> is_closed_pure_type t
  | PTexternal (ptl,_) -> List.for_all is_closed_pure_type ptl

let rationalize s =
  let n = String.length s in
  let i = String.index s '.' in
  let d = n - i - 1 in
  String.sub s 0 i ^ String.sub s (succ i) d, "1" ^ String.make d '0'

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function PureType _ -> true | _ -> false

let asst_app f x = { x with a_value = (f x.a_value) }

let post_app f (q,l) = 
  (asst_app f q, List.map (fun (x,a) -> (x, asst_app f a)) l)

let optpost_app f = option_app (post_app f)

let asst_fold f x v = f x.a_value v
let post_fold f (q,l) v = 
  List.fold_right (fun (_,p) -> asst_fold f p) l (asst_fold f q v)
let optpost_fold f = option_fold (post_fold f)

let anonymous loc x = { a_name = Anonymous; a_value = x; a_loc = loc }
let wp_named loc x = { a_name = Name (wp_name ()); a_value = x; a_loc = loc }

let force_wp_name = option_app (fun a -> { a with a_name = Name (wp_name ()) })

let force_name f a = { a with a_name = Name (f a.a_name) }

let force_post_name = option_app (fun (q,l) -> (force_name post_name q, l))

let force_bool_name = 
  let f = function Name id -> id | Anonymous -> bool_name() in
  option_app (fun (q,l) -> (force_name f q, l))

let force_loc l a = { a with a_loc = l }

let force_post_loc l (q,ql) = 
  (force_loc l q, List.map (fun (x,a) -> (x, force_loc l a)) ql)

let rec force_type_c_loc l c =
  { c with 
      c_result_type = force_type_v_loc l c.c_result_type;
      c_pre = List.map (force_loc l) c.c_pre;
      c_post = option_app (force_post_loc l) c.c_post }

and force_type_v_loc l = function
  | Ref v -> Ref (force_type_v_loc l v)
  | Array v -> Array (force_type_v_loc l v)
  | Arrow (bl, c) -> Arrow (bl, force_type_c_loc l c)
  | (PureType _) as v -> v


(* selection of postcondition's parts *)
let post_val = fst
let post_exn x (_,l) = List.assoc x l

let optpost_val = option_app post_val
let optpost_exn x = option_app (post_exn x)

(* substititution within some parts of postconditions *)
let val_app f (x,xl) = (asst_app f x, xl)
let exn_app x f (x,xl) = (x, List.map (fun (x,a) -> x, asst_app f a) xl)

let optval_app f = option_app (val_app f)
let optexn_app x f = option_app (exn_app x f)

let optasst_app f = option_app (asst_app f)

(*s Functions on terms and predicates. *)

let applist f l = match (f,l) with
  | f, [] -> f
  | Tvar id, l -> Tapp (id, l, [])
  | Tapp (id, l, il), l' -> assert (il = []); Tapp (id, l @ l', [])
  | (Tconst _ | Tderef _), _ -> assert false

let papplist f l = match (f,l) with
  | f, [] -> f
  | Pvar id, l -> Papp (id, l, [])
  | Papp (id, l, il), l' -> assert (il = []); Papp (id, l @ l', [])
  | _ -> assert false

let rec predicate_of_term = function
  | Tvar x -> Pvar x
  | Tapp (id, l, i) -> Papp (id, l, i)
  | _ -> assert false

let rec collect_term s = function
  | Tvar id | Tderef id -> Idset.add id s
  | Tapp (_, l, _) -> List.fold_left collect_term s l
  | Tconst _ -> s

let rec collect_pred s = function
  | Pvar _ | Ptrue | Pfalse -> s
  | Papp (_, l, _) -> List.fold_left collect_term s l
  | Pimplies (_, a, b) | Pand (_, a, b) | Por (a, b) | Piff (a, b)
  | Forallb (_, a, b) -> 
      collect_pred (collect_pred s a) b
  | Pif (a, b, c) -> collect_pred (collect_pred (collect_term s a) b) c
  | Pnot a -> collect_pred s a
  | Forall (_, _, _, _, p) -> collect_pred s p
  | Exists (_, _, _, p) -> collect_pred s p
  | Pfpi (t, _, _) -> collect_term s t

let term_vars = collect_term Idset.empty
let predicate_vars = collect_pred Idset.empty

let post_vars (q,al) = 
  List.fold_left 
    (fun s (_,a) -> Idset.union s (predicate_vars a.a_value))
    (predicate_vars q.a_value)
    al

let rec tsubst_in_term s = function
  | Tvar x as t -> 
      (try Idmap.find x s with Not_found -> t)
  | Tderef x as t ->
      (try Idmap.find x s with Not_found -> t)
  | Tapp (x,l,i) -> 
      Tapp (x, List.map (tsubst_in_term s) l, i)
(*i***EXP
      let l' = List.map (tsubst_in_term s) l in
      (try applist (Idmap.find x s) l' with Not_found -> Tapp (x,l'))
***i*)
  | Tconst _ as t -> 
      t

let rec map_predicate f = function
  | Pimplies (w, a, b) -> Pimplies (w, f a, f b)
  | Pif (a, b, c) -> Pif (a, f b, f c)
  | Pand (w, a, b) -> Pand (w, f a, f b)
  | Por (a, b) -> Por (f a, f b)
  | Piff (a, b) -> Piff (f a, f b)
  | Pnot a -> Pnot (f a)
  | Forall (w, id, b, v, p) -> Forall (w, id, b, v, f p)
  | Exists (id, b, v, p) -> Exists (id, b, v, f p)
  | Forallb (w, a, b) -> Forallb (w, f a, f b)
  | Ptrue | Pfalse | Pvar _ | Papp _ | Pfpi _ as p -> p

let rec tsubst_in_predicate s = function
  | Papp (id, l, i) -> Papp (id, List.map (tsubst_in_term s) l, i)
  | Pif (a, b ,c) -> Pif (tsubst_in_term s a, 
			  tsubst_in_predicate s b, 
			  tsubst_in_predicate s c)
  | Pfpi (t, f1, f2) -> Pfpi (tsubst_in_term s t, f1, f2)
  | p -> map_predicate (tsubst_in_predicate s) p

let subst_in_term s = 
  tsubst_in_term (Idmap.map (fun id -> Tvar id) s)

let subst_in_predicate s = 
  tsubst_in_predicate (Idmap.map (fun id -> Tvar id) s)

let subst_one x t = Idmap.add x t Idmap.empty

let subst_onev = subst_one

let rec subst_manyv vl1 vl2 = match vl1, vl2 with
  | [], [] -> Idmap.empty
  | x1 :: l1, x2 :: l2 -> Idmap.add x1 x2 (subst_manyv l1 l2)
  | _ -> invalid_arg "subst_manyv"
  
let rec unref_term = function
  | Tderef id -> Tvar id
  | Tapp (id, tl, i) -> Tapp (id, List.map unref_term tl, i)
  | Tvar _ | Tconst _ as t -> t

let equals_true = function
  | Tapp (id, _, _) as t when is_relation id -> t
  | t -> Tapp (t_eq, [t; Tconst (ConstBool true)], [])

let negate id =
  if id == t_lt then t_ge
  else if id == t_le then t_gt 
  else if id == t_gt then t_le
  else if id == t_ge then t_lt
  else if id == t_eq then t_neq
  else if id == t_neq then t_eq
  else if id == t_lt_int then t_ge_int
  else if id == t_le_int then t_gt_int
  else if id == t_gt_int then t_le_int
  else if id == t_ge_int then t_lt_int
  else if id == t_eq_int then t_neq_int
  else if id == t_neq_int then t_eq_int
  else if id == t_lt_real then t_ge_real
  else if id == t_le_real then t_gt_real
  else if id == t_gt_real then t_le_real
  else if id == t_ge_real then t_lt_real
  else if id == t_eq_real then t_neq_real
  else if id == t_neq_real then t_eq_real
  else if id == t_eq_bool then t_neq_bool
  else if id == t_neq_bool then t_eq_bool 
  else if id == t_eq_unit then t_neq_unit
  else if id == t_neq_unit then t_eq_unit 
  else assert false

let make_int_relation id =
  if id == t_lt then t_lt_int
  else if id == t_le then t_le_int
  else if id == t_gt then t_gt_int
  else if id == t_ge then t_ge_int
  else id

let equals_false = function
  | Tapp (id, l, i) when is_relation id -> Tapp (negate id, l, i)
  | t -> Tapp (t_eq, [t; Tconst (ConstBool false)], [])

let rec mlize_type = function
  | PureType pt -> pt
  | Ref v -> mlize_type v
  | Array v -> PTarray (mlize_type v)
  | Arrow _ -> assert false

(*s Substitutions *)

let rec type_c_subst s c =
  let {c_result_name=id; c_result_type=t; c_effect=e; c_pre=p; c_post=q} = c in
  let s' = Idmap.fold (fun x x' -> Idmap.add (at_id x "") (at_id x' "")) s s in
  { c_result_name = id;
    c_result_type = type_v_subst s t;
    c_effect = Effect.subst s e;
    c_pre = List.map (asst_app (subst_in_predicate s)) p;
    c_post = option_app (post_app (subst_in_predicate s')) q }

and type_v_subst s = function
  | Ref v -> Ref (type_v_subst s v)
  | Array v -> Array (type_v_subst s v)
  | Arrow (bl,c) -> Arrow (List.map (binder_subst s) bl, type_c_subst s c)
  | (PureType _) as v -> v

and binder_subst s = function
  | (n, BindType v) -> (n, BindType (type_v_subst s v))
  | b -> b

(*s substitution of term for variables *)

let rec type_c_rsubst s c =
  { c_result_name = c.c_result_name;
    c_result_type = type_v_rsubst s c.c_result_type;
    c_effect = c.c_effect;
    c_pre = List.map (asst_app (tsubst_in_predicate s)) c.c_pre;
    c_post = option_app (post_app (tsubst_in_predicate s)) c.c_post }

and type_v_rsubst s = function
  | Ref v -> Ref (type_v_rsubst s v)
  | Array v -> Array (type_v_rsubst s v)
  | Arrow (bl,c) -> Arrow(List.map (binder_rsubst s) bl, type_c_rsubst s c)
  | PureType _ as v -> v

and binder_rsubst s = function
  | (n, BindType v) -> (n, BindType (type_v_rsubst s v))
  | b -> b

let ptype_c_of_v v =
  { pc_result_name = Ident.result;
    pc_result_type = v;
    pc_effect = Effect.bottom; pc_pre = []; pc_post = None }

let type_c_of_v v =
  { c_result_name = Ident.result;
    c_result_type = v;
    c_effect = Effect.bottom; c_pre = []; c_post = None }

(* make_arrow bl c = (x1:V1)...(xn:Vn)c *)

let make_arrow bl c = match bl with
  | [] -> 
      invalid_arg "make_arrow: no binder"
  | _ -> 
      let rename (id,v) (bl,s) = 
	let id' = Ident.bound id in 
	(id',v) :: bl, 
	Idmap.add id id' (Idmap.add (at_id id "") (at_id id' "") s)
      in
      let bl',s = List.fold_right rename bl ([], Idmap.empty) in
      Arrow (bl', type_c_subst s c)

(*s Smart constructors. *)

let ttrue = Tconst (ConstBool true)
let tfalse = Tconst (ConstBool false)
let tresult = Tvar Ident.result
let tvoid = Tconst ConstUnit

let relation op t1 t2 = Papp (op, [t1; t2], [])
let not_relation op = relation (negate op)
let lt = relation t_lt
let le = relation t_le
let gt = relation t_gt
let ge = relation t_ge
let ge_real = relation t_ge_real
let eq = relation t_eq
let neq = relation t_neq

let array_length id i = Tapp (array_length, [Tderef id], [i])

let lt_int = relation t_lt_int
let le_int = relation t_le_int

let pif a b c =
  if a = ttrue then b else if a = tfalse then c else Pif (a, b ,c)

let pand ?(is_wp=false) a b = 
  if a = Ptrue then b else if b = Ptrue then a else
  if a = Pfalse || b = Pfalse then Pfalse else
  Pand (is_wp, a, b)

let pands ?(is_wp=false) = List.fold_left (pand ~is_wp) Ptrue

let por a b =
  if a = Ptrue || b = Ptrue then Ptrue else
  if a = Pfalse then b else if b = Pfalse then a else
  Por (a, b)

let pnot a =
  if a = Ptrue then Pfalse else if a = Pfalse then Ptrue else Pnot a

let pimplies ?(is_wp=false) p1 p2 = 
  if p2 = Ptrue then Ptrue else Pimplies (is_wp, p1, p2)

(*s [simplify] only performs simplications which are Coq reductions.
     Currently: only [if true] and [if false] *)

let rec simplify = function
  | Pif (Tconst (ConstBool true), a, _) -> simplify a
  | Pif (Tconst (ConstBool false), _, b) -> simplify b
  | p -> map_predicate simplify p

(*s Debug functions *)

module Size = struct

  let rec term = function
    | Tconst _ | Tvar _ | Tderef _ -> 1 
    | Tapp (_, tl, _) -> List.fold_left (fun s t -> s + term t) 1 tl

  let rec predicate = function
    | Pvar _ | Ptrue | Pfalse -> 1
    | Papp (_, tl, _) -> List.fold_left (fun s t -> s + term t) 1 tl
    | Pand (_, p1, p2) 
    | Por (p1, p2) 
    | Piff (p1, p2) 
    | Pimplies (_, p1, p2) -> 1 + predicate p1 + predicate p2
    | Pif (t, p1, p2) -> 1 + term t + predicate p1 + predicate p2
    | Pnot p -> 1 + predicate p
    | Forall (_,_,_,_,p) -> 1 + predicate p
    | Exists (_,_,_,p) -> 1 + predicate p
    | Forallb (_,p1,p2) -> 1+ predicate p1 + predicate p2
    | Pfpi (t,_,_) -> 1 + term t

  let assertion a = predicate a.a_value

  let postcondition (q,ql) = 
    assertion q + List.fold_left (fun s (_,q) -> s + assertion q) 0 ql

  let postcondition_opt = function None -> 0 | Some q -> postcondition q

end

(*s functions over CC terms *)

let cc_var x = CC_var x

let cc_term t = CC_term t

let rec cc_applist f l = match (f, l) with
  | f, [] -> f
  | f, x :: l -> cc_applist (CC_app (f, x)) l

let cc_lam bl = List.fold_right (fun b c -> CC_lam (b, c)) bl

let tt_var x = TTterm (Tvar x)

let tt_arrow = List.fold_right (fun b t -> TTarrow (b, t))

(*s functions over AST *)

let arg_loc = function 
  | Sterm t -> t.Ptree.ploc 
  | Stype _ -> assert false (* TODO *)

open Format

let file_formatter f cout =
  let fmt = formatter_of_out_channel cout in
  f fmt;
  pp_print_flush fmt ()

let do_not_edit file before sep after =
  let cout = 
    if not (Sys.file_exists file) then begin
      let cout = open_out file in
      file_formatter before cout;
      output_string cout ("\n" ^ sep ^ "\n\n");
      cout
    end else begin
      let file_bak = file ^ ".bak" in
      Sys.rename file file_bak;
      let cin = open_in file_bak in
      let cout = open_out file in
      begin try 
	while true do 
	  let s = input_line cin in
	  output_string cout (s ^ "\n");
	  if s = sep then raise Exit
	done
      with
	| End_of_file -> output_string cout (sep ^ "\n\n")
	| Exit -> output_string cout "\n"
      end;
      cout
    end
  in
  file_formatter after cout;
  close_out cout


