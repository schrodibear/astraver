(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: cltyping.ml,v 1.44 2004-06-10 15:40:31 marche Exp $ i*)

open Cast
open Clogic
open Creport
open Cerror
open Cenv

let option_app f = function Some x -> Some (f x) | None -> None

(* Typing terms *)

let noattr tyn = { ctype_node = tyn; 
		   ctype_storage = No_storage;
		   ctype_const = false;
		   ctype_volatile = false }
let c_void = noattr CTvoid
let c_int = noattr (CTint (Signed, Int))
let c_char = noattr (CTint (Unsigned, Char))
let c_float = noattr (CTfloat Float)
let c_string = noattr (CTpointer c_char)
let c_array ty = noattr (CTarray (ty, None))
let c_array_size ty s = noattr (CTarray (ty, Some s))
let c_pointer ty = noattr (CTpointer ty)
let c_void_star = c_pointer c_void
let c_addr = noattr (CTvar "addr")

let is_null t = match t.term_node with
  | Tnull -> true
  | Tconstant s -> (try int_of_string s = 0 with _ -> false)
  | _ -> false

let compatible t1 t2 = 
  sub_type t1.term_type t2.term_type || 
  sub_type t2.term_type t1.term_type ||
  (pointer_or_array_type t1.term_type && is_null t2) ||
  (pointer_or_array_type t2.term_type && is_null t1)

let compatible_term_type t ty = 
  sub_type t.term_type ty || 
  sub_type ty t.term_type ||
  (pointer_or_array_type ty && is_null t)

let expected_type loc t1 t2 =
  if not (eq_type t1 t2) then raise_located loc (ExpectedType (t1, t2))

let expected_term_type loc t1 t2 =
  if not (compatible_term_type t1 t2) 
  then raise_located loc (ExpectedType (t1.term_type, t2))

let expected_num loc t = match t.term_type.ctype_node with
  | CTenum _ | CTint _ | CTfloat _ -> ()
  | _ -> error loc "invalid operand (expected integer or float)"

let expected_num_pointer loc t = match t.term_type.ctype_node with
  | CTenum _ | CTint _ | CTfloat _ 
  | CTarray _ | CTpointer _ -> ()
  | _ -> error loc "invalid operand (expected integer, float or pointer)"

let expected_int loc t = match t.term_type.ctype_node with
  | CTint _ -> ()
  | _ -> error loc "invalid operand (expected integer)"

let max_type t1 t2 = match t1.ctype_node, t2.ctype_node with
  | CTint _, CTint _ -> c_int
  | CTint _, CTfloat _
  | CTfloat _, CTint _
  | CTfloat _, CTfloat _ -> c_float
  | _ -> assert false

(* Typing terms *)

open Info

let rec type_term env t =
  let t, ty = type_term_node t.lexpr_loc env t.lexpr_node in
  { term_node = t; term_type = ty }

and type_term_node loc env = function
  | PLconstant c -> 
      (try 
	 let _ = int_of_string c in Tconstant c, c_int
       with _ -> 
	 Tconstant c, c_float)
  | PLvar x ->
      let (ty,info) = 
	try Env.find x.var_name env with Not_found -> 
	try find_sym x.var_name with Not_found -> 
        error loc ("unbound variable " ^ x.var_name)
      in 
      Tvar info, ty
  | PLapp (f, tl) ->
      (try 
	 let pl, ty, info = find_fun f.logic_name in
	 let tl = type_terms loc env pl tl in
	 Tapp (info, tl), ty
       with Not_found -> 
	 error loc ("unbound function " ^ f.logic_name))
  | PLunop (Uminus, t) -> 
      let t = type_num_term env t in
      Tunop (Uminus, t), t.term_type
  | PLunop (Ustar, t) -> 
      let t = type_term env t in
      begin match t.term_type.ctype_node with
	| CTpointer ty | CTarray (ty, _) -> Tunop (Ustar, t), ty
	| _ -> error loc "invalid type argument of `unary *'"
      end
  | PLunop (Uamp, t) -> 
      let t = type_term env t in
      Tunop (Uamp, t), noattr (CTpointer t.term_type)
  | PLunop (Ufloat_of_int, _) ->
      assert false
  | PLbinop (t1, Badd, t2) ->
      let t1 = type_term env t1 in
      let ty1 = t1.term_type in
      let t2 = type_term env t2 in
      let ty2 = t2.term_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (CTenum _ | CTint _ | CTfloat _), (CTenum _ | CTint _ | CTfloat _) ->
	    Tbinop (t1, Badd, t2), max_type ty1 ty2
	| (CTpointer _ | CTarray _), (CTint _ | CTenum _) -> 
	    Tbinop (t1, Badd, t2), ty1
	| (CTenum _ | CTint _), (CTpointer _ | CTarray _) ->
	    Tbinop (t2, Badd, t1), ty2
	| _ -> 
	    error loc "invalid operands to binary +"
      end
  | PLbinop (t1, Bsub, t2) ->
      let t1 = type_term env t1 in
      let ty1 = t1.term_type in
      let t2 = type_term env t2 in
      let ty2 = t2.term_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (CTenum _ | CTint _ | CTfloat _), (CTenum _ | CTint _ | CTfloat _) ->
	    Tbinop (t1, Bsub, t2), max_type ty1 ty2
	| (CTpointer _ | CTarray _), (CTint _ | CTenum _) -> 
	    let mt2 = { term_node = Tunop (Uminus, t2); term_type = ty2 } in
	    Tbinop (t1, Badd, mt2), ty1
	| (CTpointer _ | CTarray _), (CTpointer _ | CTarray _) ->
	    Tbinop (t1, Bsub, t2), ty1 (* TODO check types *)
	| _ -> error loc "invalid operands to binary -"
      end
  | PLbinop (t1, (Bmul | Bdiv as op), t2) ->
      let t1 = type_num_term env t1 in
      let t2 = type_num_term env t2 in
      Tbinop (t1, op, t2), max_type t1.term_type t2.term_type
  | PLbinop (t1, Bmod, t2) ->
      let t1 = type_int_term env t1 in
      let t2 = type_int_term env t2 in
      Tbinop (t1, Bmod, t2), c_int
  | PLdot (t, x) ->
      let t = type_term env t in
      let x,ty = type_of_field loc x t.term_type in
      let t_dot_x = match t.term_node with
	| Tunop (Ustar, e) -> 
	    Tarrow (e, x)
	| Tarrget (e1, e2) -> 
	    let a = 
	      { term_node = Tbinop (e1, Badd, e2); term_type = e1.term_type }
	    in
	    Tarrow (a, x)
	| _ -> 
	    Tdot (t, x)
      in
      t_dot_x, ty
  | PLarrow (t, x) ->
      let t = type_term env t in
      begin match t.term_type.ctype_node with
	| CTpointer ty -> 
	    let x,ty = type_of_field loc x ty in
	    Tarrow (t, x), ty
	| _ -> 
	    error loc "invalid type argument of `->'"
      end
  | PLarrget (t1, t2) ->
      let t1 = type_term env t1 in
      (match t1.term_type.ctype_node with
	 | CTarray (ty, _) | CTpointer ty ->
	     let t2 = type_int_term env t2 in
	     Tarrget (t1, t2), ty
	 | _ ->
	     error loc "subscripted value is neither array nor pointer")
  | PLif (t1, t2, t3) ->
      (* TODO type de t1 ? *)
      unsupported "logic if-then-else"
  | PLold t ->
      let t = type_term env t in
      Told t, t.term_type
  | PLat (t, l) ->
      (* TODO check label l *)
      let t = type_term env t in
      Tat (t, l), t.term_type
  | PLbase_addr t ->
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | CTarray _ | CTpointer _ -> Tbase_addr t, c_addr
	 | _ -> error loc "subscripted value is neither array nor pointer")
  | PLblock_length t ->
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | CTarray _ | CTpointer _ -> Tblock_length t, c_int
	 | _ -> error loc "subscripted value is neither array nor pointer")
  | PLresult ->
      (try let ty,_ = Env.find "\\result" env in Tresult, ty
       with Not_found -> error loc "\\result meaningless")
  | PLnull ->
      Tnull, c_void_star
  | PLcast (ty, t) ->
      unsupported "logic cast"
  | PLvalid _ | PLvalid_index _ | PLvalid_range _ | PLfresh _ 
  | PLexists _ | PLforall _ | PLnot _ | PLimplies _ | PLiff _
  | PLor _ | PLand _ | PLrel _ | PLtrue | PLfalse ->
      raise (Stdpp.Exc_located (loc, Parsing.Parse_error))

and type_int_term env t =
  let tt = type_term env t in
  expected_int t.lexpr_loc tt;
  tt

and type_num_term env t =
  let tt = type_term env t in
  expected_num t.lexpr_loc tt;
  tt

and type_num_pointer_term env t =
  let tt = type_term env t in
  expected_num_pointer t.lexpr_loc tt;
  tt

and type_terms loc env at tl =
  let rec type_list = function
    | [], [] -> 
	[]
    | et :: etl, ({lexpr_loc=tloc} as t) :: tl ->
	let t = type_term env t in
	expected_term_type tloc t et;
	t :: type_list (etl, tl)
    | [], _ ->
	raise_located loc TooManyArguments
    | _, [] ->
	raise_located loc PartialApp
  in
  type_list (at, tl)

(* Typing logic types *)

let rec type_type env t = 
  { t with ctype_node = type_type_node env t.ctype_node }

and type_type_node env = function
  | CTint _ | CTfloat _ as t -> t
  | CTarray (ty, None) -> CTarray (type_type env ty, None)
  | _ -> assert false

let rec type_logic_type env = function
  | LTint -> c_int
  | LTfloat -> c_float
  | LTarray ty -> c_array (type_logic_type env ty)
  | LTpointer ty -> c_pointer (type_logic_type env ty)
  | LTvar id ->  
      noattr (try (find_typedef id).ctype_node with Not_found -> CTvar id)

(** abandon provisoire 
let rec type_logic_type env = function
  | PTctype ct ->
      PTctype (type_type env ct)
  | PTvar {tag=n; type_val =t } -> 
      PTvar { tag = n; type_val = option_app (type_logic_type env) t }
  | PTexternal (tl, s) -> 
      PTexternal (List.map (type_logic_type env) tl, s)
**)

let type_quantifier env (ty, x) = (type_logic_type env ty, x)
let type_quantifiers env = List.map (type_quantifier env)

let add_quantifiers q env =
  List.fold_left
    (fun env (ty, x) -> Env.add x ty (Info.default_var_info x) env)
    env q

let zero = { term_node = Tconstant "0"; term_type = c_int }

(* Typing predicates *)

let rec type_predicate env p0 = match p0.lexpr_node with
  | PLfalse -> Pfalse
  | PLtrue -> Ptrue
  | PLrel ({lexpr_node = PLrel (_, _, t2)} as p1, op, t3) ->
      let p1 = type_predicate env p1 in
      let p2 = { lexpr_node = PLrel (t2, op, t3); lexpr_loc = p0.lexpr_loc } in
      let p2 = type_predicate env p2 in
      Pand (p1, p2)
  | PLrel (t1, (Lt | Le | Gt | Ge as r), t2) -> 
      let loc = Loc.join t1.lexpr_loc t2.lexpr_loc in
      let t1 = type_num_pointer_term env t1 in
      let t2 = type_num_pointer_term env t2 in
      if not (compatible t1 t2) then 
	error loc "comparison of incompatible types";
      Prel (t1, r, t2)
  | PLrel (t1, (Eq | Neq as r), t2) -> 
      let loc = Loc.join t1.lexpr_loc t2.lexpr_loc in
      let t1 = type_term env t1 in
      let t2 = type_term env t2 in
      if not (compatible t1 t2) then 
	error loc "comparison of incompatible types";
      Prel (t1, r, t2)
  | PLand (p1, p2) -> 
      Pand (type_predicate env p1, type_predicate env p2)
  | PLor (p1, p2) -> 
      Por (type_predicate env p1, type_predicate env p2)
  | PLimplies (p1, p2) -> 
      Pimplies (type_predicate env p1, type_predicate env p2) 
  | PLiff (p1, p2) -> 
      Piff (type_predicate env p1, type_predicate env p2) 
  | PLnot p -> 
      (match type_predicate env p with
	 | Prel (t, Neq, z) when z == zero -> Prel (t, Eq, zero)
	 | p -> Pnot p)
  | PLapp (p, tl) ->
      (try
	 let pl,info = find_pred p.logic_name in
	 let tl = type_terms p0.lexpr_loc env pl tl in
	 Papp (info, tl)
       with Not_found -> 
	 error p0.lexpr_loc ("unbound predicate " ^ p.logic_name))
  | PLif (t, p1, p2) -> 
      (* TODO type t ? *)
      let t = type_term env t in
      Pif (t, type_predicate env p1, type_predicate env p2)
  | PLforall (q, p) -> 
      let q = type_quantifiers env q in
      let env' = add_quantifiers q env in
      Pforall (q, type_predicate env' p)
  | PLexists (q, p) -> 
      let q = type_quantifiers env q in
      let env' = add_quantifiers q env in
      Pexists (q, type_predicate env' p)
  | PLfresh (t) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | CTarray _ | CTpointer _ -> Pfresh(t)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLvalid (t) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      (match t.term_type.ctype_node with
	 | CTstruct _ | CTunion _
	 | CTarray _ | CTpointer _ -> Pvalid(t)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLvalid_index (t,a) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      let a = type_int_term env a in
      (match t.term_type.ctype_node with
	 | CTarray _ | CTpointer _ -> Pvalid_index(t,a)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLvalid_range (t,a,b) ->
      let tloc = t.lexpr_loc in
      let t = type_term env t in
      let a = type_int_term env a in
      let b = type_int_term env b in
      (match t.term_type.ctype_node with
	 | CTarray _ | CTpointer _ -> Pvalid_range(t,a,b)
	 | _ -> error tloc "subscripted value is neither array nor pointer")
  | PLold p ->
      Pold (type_predicate env p)
  | PLat (p, l) ->
      (* TODO check label l *)
      Pat (type_predicate env p, l)
  | PLcast _ | PLblock_length _ | PLbase_addr _ | PLarrget _ | PLarrow _ 
  | PLdot _ | PLbinop _ | PLunop _ | PLconstant _ | PLvar _ | PLnull 
  | PLresult ->
      (*raise (Stdpp.Exc_located (p0.lexpr_loc, Parsing.Parse_error))*)
      (* interpret term [t] as [t != 0] *)
      let t = type_int_term env p0 in
      Prel (t, Neq, zero)

let type_variant env = function 
  | (t, None) -> (type_int_term env t, None)
  | (t, r) -> (type_term env t, r)

let rec type_location env = function
  | Lterm t -> 
      Lterm (type_term env t)
  | Lstar l -> 
      Lstar (type_term env l)
  | Lrange (l1, l2, l3) -> 
      Lrange (type_term env l1, type_term env l2, type_term env l3)

let type_loop_annot env la =
  { invariant = option_app (type_predicate env) la.invariant;
    loop_assigns = option_app (List.map (type_location env)) la.loop_assigns;
    variant = option_app (type_variant env) la.variant }

let type_spec result env s = 
  let p = option_app (type_predicate env) s.requires in
  let env' = match result with
    | None -> env
    | Some ty -> Env.add "\\result" ty (Info.default_var_info "\\result") env
  in
  let q = option_app (type_predicate env') s.ensures in
  let v = option_app (type_variant env) s.decreases in
  let m = option_app (List.map (type_location env)) s.assigns in
  { requires = p;
    assigns = m;
    ensures = q;
    decreases = v }

(* Automatic invariants expressing validity of local/global variables *)

let int_constant n = { term_node = Tconstant n; term_type = c_int }

let eval_array_size e = 
  let rec eval e = match e.texpr_node with
    | TEconstant c -> int_of_string c
    | TEunary (Uplus, t) -> eval t
    | TEunary (Cast.Uminus, t) -> -(eval t)
    | TEbinary (t1, Cast.Badd_int, t2) -> eval t1 + eval t2
    | _ -> assert false
  in
  { term_node = Tconstant (string_of_int (eval e)); term_type = c_int }

let tpred t = match t.term_node with
  | Tconstant c -> 
      { t with term_node = Tconstant (string_of_int (int_of_string c - 1)) }
  | _ ->
      { t with term_node = Tbinop (t, Bsub, int_constant "1") }

let make_and p1 p2 = match p1, p2 with
  | Ptrue, _ -> p2
  | _, Ptrue -> p1
  | _ -> Pand (p1, p2)

let fresh_index = 
  let r = ref (-1) in fun () -> incr r; "index_" ^ string_of_int !r

let valid_for_type loc v ty =
  let rec valid_for tn ty = match ty.ctype_node with
    | CTstruct (n, _) ->
	let t = { term_node = tn; term_type = c_pointer ty } in
	begin match tag_type_definition n with
	  | Defined (CTstruct (_, Decl fl)) ->
	      List.fold_right 
		(fun (tyf, f, _) acc -> match tyf.ctype_node with
		   | CTstruct _ | CTarray _ ->
		       let tnf = Tarrow (t, find_field n f) in
		       make_and acc (valid_for tnf tyf)
		   | _ ->
		       acc)
		fl (Pvalid t)
	  | Defined _ ->
	      assert false
	  | Incomplete ->
	      error loc ("`" ^ v.var_name ^ "' has incomplete type")
	end
    | CTarray (ty, None) ->
	error loc ("array size missing in `" ^ v.var_name ^ "'")
    | CTarray (ty, Some s) ->
	let t = { term_node = tn; term_type = c_array_size ty s } in
	let ts = eval_array_size s in
	begin match ty.ctype_node with
	  | CTstruct _ | CTarray _ ->
	      let i = default_var_info (fresh_index ()) in
	      let vari = { term_node = Tvar i; term_type = c_int } in
	      let vti = valid_for (Tbinop (t, Badd, vari)) ty in
	      let ineq = Pand (Prel (int_constant "0", Le, vari),
			       Prel (vari, Lt, ts)) in
	      Pforall ([c_int, i.var_name], Pimplies (ineq, vti))
	  | _ ->
	      Pvalid_range (t, int_constant "0", tpred ts)
	end
    | _ -> 
	assert false
  in
  valid_for (Tvar v) ty
