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

(*i $Id: cinterp.ml,v 1.214 2006-10-17 12:26:55 moy Exp $ i*)


open Format
open Coptions
open Output
open Info
open Cast
open Clogic
open Creport
open Ctypes
open Cseparation
open Pp


let print_effects2 fmt l =
  fprintf fmt "@[%a@]"
    (print_list space (fun fmt (z,s,_) -> fprintf fmt " %s_%s " s z.name)) 
    (ZoneSet.elements l)

let print_effects fmt l =
  fprintf fmt "@[%a@]"
    (print_list space (fun fmt v -> pp_print_string fmt v.var_unique_name)) 
    (HeapVarSet.elements l)

let heap_var_name v =
  match v.var_why_type with
    | Info.Memory(_,z) ->
	v.var_unique_name ^ "_" ^ (found_repr z)
    | _ -> v.var_unique_name

let is_bin_op = function
  | "add_int"
  | "sub_int" -> true
  | _ -> false

let rec is_pure e =
  match e with
    | Var _ | Deref _ | Cte _ -> true
    | App(Var id,l) -> is_bin_op id && is_pure l
    | App(e1,e2) -> is_pure e1 && is_pure e2
    | _ -> false

let tempvar_count = ref 0
let reset_tmp_var () = tempvar_count := 0
let tmp_var () = incr tempvar_count; "caduceus_" ^ string_of_int !tempvar_count

let interp_int_rel = function
  | Lt -> "lt_int"
  | Le -> "le_int"
  | Gt -> "gt_int"
  | Ge -> "ge_int"
  | Eq -> "eq_int"
  | Neq -> "neq_int"

let interp_real_rel = function
  | Lt -> "lt_real"
  | Le -> "le_real"
  | Gt -> "gt_real"
  | Ge -> "ge_real"
  | Eq -> "eq_real"
  | Neq -> "neq_real"

let interp_pointer_rel = function
  | Lt -> "lt_pointer"
  | Le -> "le_pointer"
  | Gt -> "gt_pointer"
  | Ge -> "ge_pointer"
  | Eq -> "eq"
  | Neq -> "neq"

let real_of_int (t : nctype nterm) = 
  { nterm_type = c_real; 
    nterm_loc = Loc.dummy_position;
    nterm_node = NTunop (Ufloat_of_int, t);
  }

let interp_rel (t1 : nctype nterm) t2 r = 
  match t1.nterm_type.ctype_node, t2.nterm_type.ctype_node with
  | (Tenum _ | Tint _), (Tenum _ | Tint _) -> 
      t1, interp_int_rel r, t2
  | (Tfloat Real), (Tfloat Real) -> 
      t1, interp_real_rel r, t2
  | (Tenum _ | Tint _), (Tfloat Real) -> 
      real_of_int t1, interp_real_rel r, t2
  | (Tfloat Real), (Tenum _ | Tint _) -> 
      t1, interp_real_rel r, real_of_int t2
  | (Tarray _|Tpointer _), (Tarray _|Tpointer _) -> 
      t1, interp_pointer_rel r, t2
  | _ ->
      (match r with Eq -> t1,"eq",t2 | Neq -> t1,"neq",t2 | _ -> assert false)

let interp_term_bin_op ty1 ty2 op =
  match ty1.ctype_node, ty2.ctype_node, op with
  | (Tenum _ | Tint _), _, Badd -> "add_int"
  | (Tenum _ | Tint _), _, Bsub -> "sub_int"
  | (Tenum _ | Tint _), _, Bmul -> "mul_int"
  | (Tenum _ | Tint _), _, Bdiv -> "div_int"
  | (Tenum _ | Tint _), _, Bmod -> "mod_int"
  | Tfloat _, _, Badd -> "add_real"
  | Tfloat _, _, Bsub -> "sub_real"
  | Tfloat _, _, Bmul -> "mul_real"
  | Tfloat _, _, Bdiv -> "div_real"
  | _, _, Bpow_real -> "pow_real"
  | (Tpointer _ | Tarray _), _, Badd -> "shift"
  | (Tpointer _ | Tarray _), (Tenum _ | Tint _), Bsub -> 
      assert false (* normalized at typing *)
  | (Tpointer _ | Tarray _), (Tpointer _ | Tarray _), Bsub -> "sub_pointer"
  | (Tpointer _ | Tarray _), _, Bsub -> assert false
  | Tfloat _, _, Bmod -> assert false
  | Tarray _, _, (Bmod|Bdiv|Bmul) -> assert false
  | Tpointer _, _, (Bmod|Bdiv|Bmul) -> assert false
  | Tfun (_, _), _, _-> assert false 
  | Tunion _ , _, _ -> assert false
  | Tstruct _ , _, _-> assert false
  | Tvar _ , _, _-> assert false 
  | Tvoid , _, _-> assert false

let string_of_rounding_mode = function
  | RM_nearest_even -> "nearest_even"
  | RM_to_zero -> "to_zero"
  | RM_up -> "up"
  | RM_down -> "down"
  | RM_nearest_away -> "nearest_away"
  | RM_dynamic -> assert false

let select_fk s d q = function
  | Float -> s | Double -> d | LongDouble -> q | Real -> assert false

let term_rounding_mode = LVar (string_of_rounding_mode dft_fp_rounding_mode)

let term_bin_op ty1 ty2 op t1 t2 =
  match ty1.ctype_node, op, t2 with
    | (Tpointer _ | Tarray _), Badd, LConst (Prim_int "0") ->
	t1
    | Tfloat (Float | Double | LongDouble as fk), _, _ when floats ->
	let s = match op with
	  | Badd -> select_fk "add_single" "add_double" "add_quad" fk
	  | Bsub -> select_fk "sub_single" "sub_double" "sub_quad" fk
	  | Bmul -> select_fk "mul_single" "mul_double" "mul_quad" fk
	  | Bdiv -> select_fk "div_single" "div_double" "div_quad" fk
	  | _ -> assert false
	in
	LApp (s, [term_rounding_mode; t1; t2])
    | _ -> 
	LApp (interp_term_bin_op ty1 ty2 op, [t1; t2])

let interp_term_un_op ty op t = match ty.ctype_node, op with
  | (Tenum _ | Tint _), Uminus -> LApp ("neg_int", [t])
  | Tfloat (Float | Double | LongDouble as fk), Uminus when floats -> 
      let s = select_fk "neg_single" "neg_double" "neg_quad" fk in
      LApp (s, [term_rounding_mode; t])
  | Tfloat _, Uminus -> LApp ("neg_real", [t])
  | _, Uabs_real -> LApp ("abs_real", [t])
  | _, Usqrt_real -> LApp ("sqrt_real", [t])
  | _ -> assert false

let interp_var label v =
  match label with 
    | None -> LVar v 
    | Some l -> LVarAtLabel(v,l)

let zoned_name (f : string) (ty : Info.why_type) =
  match ty with
    | Pointer z -> f ^ "_" ^ (found_repr ~quote_var:false z)
    | Addr _ 
    | Info.Int -> assert false
    | Unit -> assert false
    | Why_Logic s ->  assert false
    | Memory(t,z) -> assert false
  
let term_float_conversion fk1 fk2 e = 
  if not floats then e else
  match fk1, fk2 with
    | Real, Float -> LApp ("r_to_s", [term_rounding_mode; e])
    | Real, Double -> LApp ("r_to_d", [term_rounding_mode; e])
    | Real, LongDouble -> LApp ("r_to_q", [term_rounding_mode; e])
    | Float, Real -> LApp ("s_to_r", [e])
    | Double, Real -> LApp ("d_to_r", [e])
    | LongDouble, Real -> LApp ("q_to_r", [e])
    | Float, Double -> 
	LApp ("double_of_single", [e])
    | Double, Float -> 
	LApp ("single_of_double", [term_rounding_mode; e ])
    | Float, LongDouble -> 
	LApp ("quad_of_single", [e])
    | LongDouble, Float -> 
	LApp ("single_of_quad", [term_rounding_mode; e ])
    | Double, LongDouble -> 
	LApp ("quad_of_double", [e])
    | LongDouble, Double -> 
	LApp ("double_of_quad", [term_rounding_mode; e ])
    | fk1, fk2 when fk1 = fk2 ->
	e
    | _ -> 
	assert false

let rec interp_term label old_label t =
  let f = interp_term label old_label in
  match t.nterm_node with
    | NTconstant (IntConstant c) ->
	LConst(Prim_int (try Int64.to_string (Cconst.int t.nterm_loc c)
			 with _ -> c))
    | NTconstant (RealConstant c) ->
	LConst(Prim_real c)
    | NTvar id ->
	let n = id.var_unique_name in
	if id.var_is_assigned && not id.var_is_a_formal_param then
	  interp_var label n
	else LVar n
    | NTold t -> interp_term (Some old_label) old_label t
    | NTbinop (t1, op, t2) ->
	term_bin_op t1.nterm_type t2.nterm_type op (f t1) (f t2)
    | NTbase_addr t -> 
	LApp("base_addr",[f t])
    | NToffset t -> 
	LApp("offset",[f t])
    | NTblock_length t -> 
	(* [block_length] should not be used with the 
	   arithmetic memory model *)
	assert (not arith_memory_model);
	LApp("block_length",[interp_var label "alloc"; f t])
    | NTarrlen t -> 
	LApp("arrlen",[f t])
    | NTstrlen (t,zone,var) -> 
	(* [strlen(p)] depends on the value pointed to by [p].
	   Pass an additional parameter for the memory. *)
	let te = f t in
	let var = zoned_name var.var_unique_name (Cnorm.type_why_for_term t)
	in
	LApp("strlen",[interp_var label var;te])
    | NTat (t, l) -> 
	interp_term (Some l) old_label t
    | NTif (_, _, _) -> 
	unsupported t.nterm_loc "logic if-then-else"
    | NTarrow (t,z, field) -> 
	let te = f t in
	let var = zoned_name field.var_unique_name (Cnorm.type_why_for_term t)
	in
	LApp("acc",[interp_var label var;te])
    | NTunop (Utilde, t) -> 
	LApp ("bw_compl", [f t])
    | NTunop (Ustar, _) -> 
	assert false
    | NTunop (Uamp, t1) -> 
	interp_term_address label old_label t1
    | NTunop (Uminus | Uabs_real | Usqrt_real as op, t1) -> 
	interp_term_un_op t1.nterm_type op (f t1)
    | NTunop (Ufloat_of_int, t1) ->
	let e = LApp ("real_of_int", [f t1]) in
	begin match t.nterm_type.ctype_node with
	  | Tfloat fk -> term_float_conversion Real fk e
	  | _ -> assert false
	end
    | NTunop (Uint_of_float, t1) ->
	let e = match t1.nterm_type.ctype_node with
	  | Tfloat fk -> term_float_conversion fk Real (f t1)
	  | _ -> assert false
	in
	LApp ("int_of_real", [e])
    | NTunop (Ufloat_conversion, t1) ->
	begin match t1.nterm_type.ctype_node, t.nterm_type.ctype_node with
	  | Tfloat fk1, Tfloat fk2 -> term_float_conversion fk1 fk2 (f t1)
	  | _ -> assert false
	end
    | NTunop (Uround_error, t1) ->
	begin match t1.nterm_type.ctype_node with
	  | Tfloat Float -> LApp ("single_round_error", [f t1])
	  | Tfloat Double -> LApp ("double_round_error", [f t1])
	  | Tfloat LongDouble -> LApp ("quad_round_error", [f t1])
	  | _ -> assert false
	end
    | NTunop (Utotal_error, t1) ->
	begin match t1.nterm_type.ctype_node with
	  | Tfloat Float -> LApp ("single_total_error", [f t1])
	  | Tfloat Double -> LApp ("double_total_error", [f t1])
	  | Tfloat LongDouble -> LApp ("quad_total_error", [f t1])
	  | _ -> assert false
	end
    | NTunop (Uexact, t1) ->
	begin match t1.nterm_type.ctype_node with
	  | Tfloat Float -> LApp ("s_to_exact", [f t1])
	  | Tfloat Double -> LApp ("d_to_exact", [f t1])
	  | Tfloat LongDouble -> LApp ("q_to_exact", [f t1])
	  | _ -> assert false
	end
    | NTunop (Umodel, t1) ->
	begin match t1.nterm_type.ctype_node with
	  | Tfloat Float -> LApp ("s_to_model", [f t1])
	  | Tfloat Double -> LApp ("d_to_model", [f t1])
	  | Tfloat LongDouble -> LApp ("q_to_model", [f t1])
	  | _ -> assert false
	end
    | NTapp {napp_pred = v; napp_args = tl; napp_zones_assoc = assoc} ->
	let reads = ZoneSet.fold 
	  (fun (z,s,ty) acc ->
	     let z = repr z in
	     ((try Cnorm.assoc_zone z assoc with Not_found -> z),s,ty)::acc)
	  v.logic_heap_zone [] in
	let targs = List.map f tl in
	let targs = HeapVarSet.fold 
		 (fun x acc -> (interp_var label (heap_var_name x)) :: acc) 
		 v.logic_heap_args targs in
	let targs = List.fold_right 
	  (fun (z,s,_) l -> (interp_var label (zoned_name s (Pointer z)))::l)
	  reads targs 
	in
	LApp (v.logic_name,targs)
    | NTcast({ctype_node = Tpointer _}, 
	     {nterm_node = NTconstant (IntConstant "0")}) ->
	LVar "null"
    | NTcast (ty, t) -> 
	begin match ty.ctype_node, t.nterm_type.ctype_node with
	  | (Tenum _ | Tint _), (Tenum _ | Tint _) ->
	      f t
	  | Tfloat fk1, Tfloat fk2 -> 
	      term_float_conversion fk2 fk1 (f t)
	  | Tfloat fk, (Tenum _ | Tint _) ->
	      term_float_conversion Real fk (LApp ("real_of_int", [f t]))
	  | (Tenum _ | Tint _), Tfloat fk ->
	      LApp ("int_of_real", [term_float_conversion fk Real (f t)])
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      f t
	  | _ -> 
	      unsupported t.nterm_loc "logic cast"
	end
    | NTrange _ ->
	error t.nterm_loc "range operator .. invalid here"

and interp_term_address  label old_label e = match e.nterm_node with
  | NTvar v -> 
      begin match e.nterm_type.ctype_node with
	| Tstruct _ | Tunion _ -> LVar v.var_unique_name
	| _ -> unsupported e.nterm_loc "& operator"
      end
  | NTunop (Ustar, e1) -> 
      interp_term  label old_label e1
  | NTarrow (e1,z, f) ->
      begin match e.nterm_type.ctype_node with
	| Tenum _ | Tint _ | Tfloat _ -> 
  	    interp_term  label old_label e1
	| Tstruct _ | Tunion _ | Tpointer _ | Tarray _ ->
	    let var = zoned_name f.var_unique_name (Cnorm.type_why_for_term e1)
	    in
	    LApp("acc",[interp_var label var; interp_term label old_label e1])
	| _ -> unsupported e.nterm_loc "& operator on a field"
      end
  | NTcast (_, e1) ->
      interp_term_address  label old_label e1
  | _ -> 
      assert false (* not a left value *)

let has_prefix p s = 
  let n = String.length p in String.length s >= n && String.sub s 0 n = p

let is_internal_pred s = String.length s >= 1 && String.sub s 0 1 = "%"

let rec interp_predicate label old_label p =
  let f = interp_predicate label old_label in
  let ft = interp_term label old_label in
  match p.npred_node with
    | NPtrue -> 
	LTrue
    | NPexists (l, p) -> 
	List.fold_right
	  (fun (t,x) p -> 
	     LExists(x.var_unique_name,
		     Info.output_why_type x.var_why_type,p)) l (f p)
    | NPforall (l, p) ->	
	List.fold_right
	  (fun (t,x) p -> 
	     LForall(x.var_unique_name,
		     Info.output_why_type x.var_why_type,p)) l (f p)
    | NPif (t, p1, p2) -> 
	let t = ft t in
	let zero = LConst (Prim_int "0") in
	LAnd (make_impl (LPred ("neq_int", [t; zero])) (f p1),
	      make_impl (LPred ("eq_int",  [t; zero])) (f p2))
    | NPnot p -> 
	LNot (f p)
    | NPimplies (p1, p2) -> 
	make_impl (f p1) (f p2)
    | NPiff (p1, p2) -> 
	make_equiv (f p1) (f p2)
    | NPor (p1, p2) -> 
	make_or (f p1) (f p2)
    | NPand (p1, p2) -> 
	make_and (f p1) (f p2)
    | NPrel (t1, op, t2) ->
	let t1,op,t2 = interp_rel t1 t2 op in
	LPred(op,[ft t1;ft t2])
    | NPapp {napp_pred = v; napp_args = tl} 
	when is_internal_pred v.logic_name ->
       let n = v.logic_name in
       let name,num =
	 if has_prefix "%valid_acc_range" n then "valid_acc_range", 1
	 else if has_prefix "%valid_acc" n then "valid_acc", 1
	 else if has_prefix "%separation1_range1" n then "separation1_range1",2
	 else if has_prefix "%separation1_range" n then "separation1_range", 1
	 else if has_prefix "%separation1" n then "separation1", 2
	 else if has_prefix "%separation2_range" n then "separation2_range", 2
	 else if has_prefix "%separation2" n then "separation2", 2
	 else assert false
       in
       let tl = match tl, num with
	 | [x], 2 -> [x; x]
	 | _ -> tl
       in
       LPred(name, List.map ft tl)
    | NPapp {napp_pred = v; napp_args = tl; napp_zones_assoc = assoc} ->
	let reads = ZoneSet.fold 
	  (fun (z,s,ty) acc ->
	     let z = repr z in
	     ((try Cnorm.assoc_zone z assoc with Not_found -> z),s,ty)::acc)
	  v.logic_heap_zone [] in
	let targs = List.map ft tl in
	let targs = HeapVarSet.fold 
		 (fun x acc -> (interp_var label (heap_var_name x)) :: acc) 
		 v.logic_heap_args targs in
	let targs = List.fold_right 
	  (fun (z,s,_) l -> 
	     (interp_var label (zoned_name s (Pointer z)))::l)
	  reads targs in
	LPred (v.logic_name,targs)
    | NPfalse -> 
	LFalse
    | NPold p -> 
	interp_predicate (Some old_label) old_label p
    | NPat (p, l) -> 
	interp_predicate (Some l) old_label p
    | NPfresh (t) ->
	(* [fresh] should not be used with the arithmetic memory model *)
	assert (not arith_memory_model);
	LPred("fresh",[interp_var (Some old_label) "alloc"; ft t])
    | NPvalid (t) ->
	if arith_memory_model then
	  LPred("valid",[ft t])
	else
	  LPred("valid",[interp_var label "alloc"; ft t])
    | NPvalid_index (t,a) ->
	if arith_memory_model then
	  LPred("valid_index",[ft t;ft a])
	else
	  LPred("valid_index",[interp_var label "alloc"; ft t;ft a])
    | NPvalid_range (t,a,b) ->
	begin 
	  match a.nterm_node , b.nterm_node with
	    | NTconstant (IntConstant "0"), NTconstant (IntConstant "0") -> 
		if arith_memory_model then
		  LPred("valid",[ft t])
		else
		  LPred("valid",[interp_var label "alloc"; ft t])
	    | _ ->
		if arith_memory_model then
		  LPred("valid_range",[ft t;ft a;ft b])
		else
		  LPred("valid_range",
			[interp_var label "alloc"; ft t;ft a;ft b])
	end
    | NPnamed (n, p) ->
	LNamed (n, f p)
    | NPseparated (t1,t2) ->
	if arith_memory_model then
	  LPred("separated",[ft t1;ft t2])
	else
	  LPred("separated",[interp_var label "alloc"; ft t1;ft t2])

let interp_predicate label old_label p = 
  let w = interp_predicate label old_label p in
  if p.npred_loc = Loc.dummy_position then
    w
  else
    LNamed ("\"" ^ String.escaped (Loc.string p.npred_loc) ^ "\"", w)

let interp_predicate_opt label old_label pred =
  match pred with
    | None -> LTrue
    | Some p -> interp_predicate label old_label p

let rounding_mode () = match !fp_rounding_mode with
  | RM_dynamic -> Deref "rounding_mode"
  | m -> Var (string_of_rounding_mode m)

let interp_float_of_int ft e =
  let e = make_app "real_of_int" [e] in
  if floats then match ft.Ctypes.ctype_node with
    | Tfloat Float -> make_app "r_to_s" [rounding_mode (); e]
    | Tfloat Double -> make_app "r_to_d" [rounding_mode (); e]
    | Tfloat LongDouble -> make_app "r_to_q" [rounding_mode (); e]
    | Tfloat Real -> e
    | _ -> assert false
  else
    e

let interp_int_of_float ft e =
  let e = 
    if floats then match ft.Ctypes.ctype_node with
      | Tfloat Float -> make_app "s_to_r" [e]
      | Tfloat Double -> make_app "d_to_r" [e]
      | Tfloat LongDouble -> make_app "q_to_r" [e]
      | Tfloat Real -> e
      | _ -> assert false
    else
      e
  in
  make_app "int_of_real" [e]

(* float conversion ty1 -> ty2 *)
let interp_float_conversion ty1 ty2 e = 
  if not floats then e else
  match ty1.Ctypes.ctype_node, ty2.Ctypes.ctype_node with
    | Tfloat Real, Tfloat Float -> make_app "r_to_s" [rounding_mode (); e]
    | Tfloat Real, Tfloat Double -> make_app "r_to_d" [rounding_mode (); e]
    | Tfloat Real, Tfloat LongDouble -> make_app "r_to_q" [rounding_mode (); e]
    | Tfloat Float, Tfloat Double -> 
	make_app "double_of_single" [e]
    | Tfloat Double, Tfloat Float -> 
	make_app "single_of_double" [rounding_mode (); e ]
    | Tfloat Float, Tfloat LongDouble -> 
	make_app "quad_of_single" [e]
    | Tfloat LongDouble, Tfloat Float -> 
	make_app "single_of_quad" [rounding_mode (); e ]
    | Tfloat Double, Tfloat LongDouble -> 
	make_app "quad_of_double" [e]
    | Tfloat LongDouble, Tfloat Double -> 
	make_app "double_of_quad" [rounding_mode (); e ]
    | Tfloat fk1, Tfloat fk2 when fk1 = fk2 ->
	e
    | _ -> 
	assert false

let int_size = Ctyping.int_size

let le_cinteger i1 i2 = int_size i1 <= int_size i2

let lt_cinteger i1 i2 = int_size i1 < int_size i2

let min_int = Invariant.min_int
let max_int = Invariant.max_int

let le_max_int i e = LPred ("le_int", [e; LConst (Prim_int (max_int i))])

let is_non_negative e = LPred ("le_int", [LConst (Prim_int "0"); e])

let not_zero e = LPred ("neq_int", [e; LConst (Prim_int "0")])

let within_bounds i e = 
  LAnd (LPred ("le_int", [LConst (Prim_int (min_int i)); e]), le_max_int i e)

let is_enum e t = 
  let _,info = Cenv.find_pred ("is_enum_" ^ e) in LPred (info.logic_name, [t])

let guard_1 g e =
  let v = tmp_var () in Let (v, e, Output.Assert (g (LVar v), Var v))

(* int conversion ty1 -> ty2 *)
let interp_int_conversion ty1 ty2 e = 
  if not int_overflow_check then e else
  match ty1.Ctypes.ctype_node, ty2.Ctypes.ctype_node with
    (* int -> int *)
    | Tint (Unsigned, i1), Tint (Unsigned, i2) 
    | Tint (Signed, i1), Tint (Signed, i2) when le_cinteger i1 i2 -> 
	e
    | Tint (Unsigned, i1), Tint (Signed, i2) when lt_cinteger i1 i2 -> 
	e
    | Tint (Unsigned, i1), Tint si2 ->
	guard_1 (le_max_int si2) e
    | Tint (Signed, i1), Tint (Unsigned, i2) when le_cinteger i1 i2 ->
	guard_1 is_non_negative e
    | Tint (Signed, i1), Tint si2 ->
	guard_1 (within_bounds si2) e
    (* enum -> int *)
    | Tenum _, Tint (Signed, i2) when le_cinteger Int i2 ->
	e
    | Tenum _, Tint si2 ->
	guard_1 (within_bounds si2) e
    (* enum -> enum *)
    | Tenum e1, Tenum e2 when e1 = e2 ->
	e 
    | (Tint _ | Tenum _), Tenum e2 ->
	guard_1 (is_enum e2) e
    | _ -> 
	assert false

let float_binop ~cmp fk opr ops opd opq =
  if floats then
    let op = match fk with 
      | Float -> ops
      | Double -> opd
      | LongDouble -> opq
      | Real -> opr
    in
    if cmp || fk = Real then
      Var op
    else
      App (Var (if fp_overflow_check then op ^ "_" else op), 
	   rounding_mode ())
  else
    Var opr

let float_unop fk = function
  | Cast.Uminus -> 
      if floats && fk <> Real then 
	let op = match fk with
	  | Float -> "neg_single"
	  | Double -> "neg_double"
	  | LongDouble -> "neg_quad"
	  | Real -> assert false
	in
	App (Var op, rounding_mode ())
      else 
	Var "neg_real"
  | _ -> assert false

(* arithmetic operations with overflow guards *)

(* binary operator -> its name 
   e.g. (Badd_int (Signed, Int)) -> "add_signed_int" *)
let int_ops_with_check = Hashtbl.create 17

let int_op_check op =
  try
    Hashtbl.find int_ops_with_check op 
  with Not_found ->
    let sign,kind = match op with
      | Badd_int i | Bsub_int i | Bmul_int i | Bdiv_int i | Bmod_int i -> i
      | _ ->  assert false
    in
    let ops = match op with
      | Badd_int _ -> "add"
      | Bsub_int _ -> "sub"
      | Bmul_int _ -> "mul"
      | Bdiv_int _ -> "div"
      | Bmod_int _ -> "mod"
      | _ -> assert false
    in
    let sgs = match sign with Signed -> "signed" | Unsigned -> "unsigned" in
    let tys = match kind with
      | Char -> "char"
      | Short -> "short"
      | Int -> "int"
      | Long -> "long"
      | LongLong -> "longlong"
      | Bitfield _ -> assert false (*TODO*)
    in
    let name = ops ^ "_" ^ sgs ^ "_" ^ tys in
    Hashtbl.add int_ops_with_check op name;
    name

(* buils the parameter declarations for arithmetic operations with checks *)
let make_int_ops_decls () =
  let int = Base_type ([], "int") in
  let make_one op name =
    let ope,i = match op with
      | Badd_int i -> "add_int",i | Bsub_int i -> "sub_int",i
      | Bmul_int i -> "mul_int",i | Bdiv_int i -> "div_int",i
      | Bmod_int i -> "mod_int",i | _ -> assert false
    in
    let e = LApp (ope, [LVar "x"; LVar "y"]) in
    let pre = match op with
      | Bdiv_int _ | Bmod_int _ -> not_zero (LVar "y")
      | Badd_int _ | Bsub_int _ | Bmul_int _ -> within_bounds i e
      | _ -> assert false 
    in
    let post = LPred ("eq", [LVar "result"; e]) in
    let spec = Annot_type (pre, int, [], [], post, None) in
    Param (false, name, Prod_type ("x", int, Prod_type ("y", int, spec)))
  in
  Hashtbl.fold 
    (fun op name acc -> make_one op name :: acc) int_ops_with_check []

let int_op op =
  if int_overflow_check then 
    int_op_check op
  else match op with
    | Badd_int _ -> "add_int"
    | Bsub_int _ -> "sub_int"
    | Bmul_int _ -> "mul_int"
    | Bdiv_int _ -> "div_int_"
    | Bmod_int _ -> "mod_int_"
    | _ -> assert false

open Cast

let interp_bin_op = function
  | Badd_int _ | Bsub_int _ | Bmul_int _ | Bdiv_int _ | Bmod_int _ as op ->
      Var (int_op op)
  | Blt_int -> Var "lt_int_"
  | Bgt_int -> Var "gt_int_"
  | Ble_int -> Var "le_int_"
  | Bge_int -> Var "ge_int_"
  | Beq_int -> Var "eq_int_"
  | Bneq_int -> Var "neq_int_" 
  | Badd_float fk -> 
      float_binop ~cmp:false fk "add_real" "add_single" "add_double" "add_quad"
  | Bsub_float fk -> 
      float_binop ~cmp:false fk "sub_real" "sub_single" "sub_double" "sub_quad"
  | Bmul_float fk -> 
      float_binop ~cmp:false fk "mul_real" "mul_single" "mul_double" "mul_quad"
  | Bdiv_float fk -> 
      float_binop 
	~cmp:false fk "div_real_" "div_single" "div_double" "div_quad"
  | Blt_float fk -> 
      float_binop ~cmp:true fk "lt_real_" "lt_single" "lt_double" "lt_quad"
  | Bgt_float fk -> 
      float_binop ~cmp:true fk "gt_real_" "gt_single" "gt_double" "gt_quad"
  | Ble_float fk -> 
      float_binop ~cmp:true fk "le_real_" "le_single" "le_double" "le_quad"
  | Bge_float fk -> 
      float_binop ~cmp:true fk "ge_real_" "ge_single" "ge_double" "ge_quad"
  | Beq_float fk -> 
      float_binop ~cmp:true fk "eq_real_" "eq_single" "eq_double" "eq_quad"
  | Bneq_float fk ->
      float_binop ~cmp:true fk "neq_real_" "neq_single" "neq_double" "neq_quad"
  | Blt_pointer -> Var "lt_pointer_"
  | Bgt_pointer -> Var "gt_pointer_"
  | Ble_pointer -> Var "le_pointer_"
  | Bge_pointer -> Var "ge_pointer_"
  | Beq_pointer -> Var "eq_pointer"
  | Bneq_pointer -> Var "neq_pointer" 
  | Badd_pointer_int -> Var "shift_"
  | Bsub_pointer -> Var "sub_pointer_"
  | Bbw_and -> Var "bw_and"
  | Bbw_xor -> Var "bw_xor"
  | Bbw_or -> Var "bw_or"
  | Bshift_left -> Var "lsl"
  | Bshift_right -> Var "lsr"
  (* should not happen *)
  | Badd | Bsub | Bmul | Bdiv | Bmod 
  | Blt | Bgt | Ble | Bge | Beq | Bneq | Band | Bor ->
      assert false

let any_float fk = 
  if floats then match fk with
    | Float -> "any_single"
    | Double -> "any_double"
    | LongDouble -> "any_quad"
    | Real -> "any_real"
  else 
    "any_real"

let int_one = Cte(Prim_int "1")
let int_minus_one = Cte(Prim_int "(-1)")

let float_of_real r fk = 
  if floats then match fk with
    | Float -> App (App (Var "r_to_s", rounding_mode ()), r)
    | Double  -> App (App (Var "r_to_d", rounding_mode ()), r)
    | LongDouble  -> App (App (Var "r_to_q", rounding_mode ()), r)
    | Real -> r
  else
    r

let real_zero = Cte(Prim_real "0.0")
let float_zero = float_of_real real_zero

let real_one = Cte(Prim_real "1.0")
let float_one = float_of_real real_one

let interp_incr_op ty op = match ty.Ctypes.ctype_node, op with
  | (Tenum _ | Tint _), (Upostfix_inc | Uprefix_inc) -> Var "add_int", int_one
  | (Tenum _ | Tint _), (Upostfix_dec | Uprefix_dec) -> Var "sub_int", int_one
  | Tfloat fk, (Upostfix_inc | Uprefix_inc) -> 
      interp_bin_op (Badd_float fk), float_one fk
  | Tfloat fk, (Upostfix_dec | Uprefix_dec) -> 
      interp_bin_op (Bsub_float fk), float_one fk
  | (Tpointer _ | Tarray _), 
    (Upostfix_inc | Uprefix_inc) -> Var "shift_", int_one
  | (Tpointer _ | Tarray _), 
    (Upostfix_dec | Uprefix_dec) -> Var "shift_", int_minus_one
  | _ -> assert false

type interp_lvalue =
  | LocalRef of Info.var_info
  | HeapRef of valid * string * Output.expr

let build_complex_app e args =
  let rec build n e args =
    match args with
      | [] -> e
      | [p] -> App(e,p)
      | ((Var _) | (Cte _) as p)::l ->
	  build n (App(e,p)) l
      | p::l ->
	  let v = tmp_var () in
	  Let(v,p, build (succ n) (App(e,Var(v))) l)
  in
  match args with
    | [] -> App(e,Void)
    | _ -> build 1 e args

let build_minimal_app e args =
  match args with
    | [] -> App(e,Void)
    | _ ->
	if List.for_all is_pure args then
	  List.fold_left (fun acc x -> App(acc,x)) e args
	else
	  build_complex_app e args

let bin_op op t1 t2 = match op, t1, t2 with
  | Badd_pointer_int, _, Cte (Prim_int "0") ->
      t1
  | Beq_int, Cte (Prim_int n1), Cte (Prim_int n2) ->
      Cte (Prim_bool (n1 = n2))
  | _ ->
      build_minimal_app (interp_bin_op op) [t1; t2]



let rec interp_expr e =
  match e.nexpr_node with
    | NEconstant (IntConstant c) -> 
	Cte (Prim_int (Int64.to_string (Cconst.int e.nexpr_loc c)))
    | NEconstant (RealConstant c) ->
	Cte(Prim_real c)
    | NEvar(Var_info v) -> 
	let n = heap_var_name v in
	if v.var_is_assigned then Deref n else Var n
    | NEvar(Fun_info v) -> assert false
    (* a ``boolean'' expression is [if e then 1 else 0] *)
    | NEbinary(_,(Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		 |Blt_float _ | Bgt_float _ | Ble_float _ | Bge_float _
		 |Beq_float _ | Bneq_float _
		 |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		 |Beq_pointer | Bneq_pointer 
		 |Blt | Bgt | Ble | Bge | Beq | Bneq | Band | Bor),_) 
    | NEunary (Unot, _) ->
	begin match interp_boolean_expr e with (* partial evaluation *)
	  | Cte (Prim_bool true) -> Cte (Prim_int "1")
	  | Cte (Prim_bool false) -> Cte(Prim_int "0")
	  | e -> If (e, Cte(Prim_int "1"), Cte(Prim_int "0"))
	end
    | NEbinary(e1,op,e2) ->
	bin_op op (interp_expr e1) (interp_expr e2)
    | NEassign (e,e2) ->
	begin
	  match interp_lvalue e with
	    | LocalRef(v) ->
		let n = v.var_unique_name in
		append (Assign(n,interp_expr e2)) (Deref n)
	    | HeapRef(valid,var,e1) ->
		let tmp1 = tmp_var () in
		let tmp2 = tmp_var () in
		match valid with 
		  | Valid ->  
		      Let(tmp1, e1,
			  Let(tmp2, interp_expr e2,
			      append (build_complex_app (Var "safe_upd_")
					[Var var; Var tmp1; Var tmp2])
				(Var tmp2))) 
		  | Not_valid -> 
		      Let(tmp1, e1,
			  Let(tmp2, interp_expr e2,
			      append (build_complex_app (Var "upd_")
					[Var var; Var tmp1; Var tmp2])
				(Var tmp2)))
		  | Tab n -> 
		      Let(tmp1, e1,
			  Let(tmp2, interp_expr e2,
			      append (build_complex_app (Var "upd_offset")
					[Var var; Var tmp1; Var tmp2;
					 valid_acc_offset e; 
					 Var (Int64.to_string n)])
				(Var tmp2)))
	end 
    | NEincr(op,e) -> 
	interp_incr_expr op e
    | NEassign_op(e,op,e2) ->
	begin match interp_lvalue e with
	  | LocalRef(v) ->
	      let n = v.var_unique_name in
	      append
	        (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	        (Deref n)
	  | HeapRef(valid,var,e1) -> 
	      let tmp1 = tmp_var () in
	      let tmp2 = tmp_var () in
	      match valid with 
		| Valid -> 	  
		    Let(tmp1, e1,
			Let(tmp2, 
			    bin_op op
			      (make_app "safe_acc_" [Var var; Var tmp1]) 
			      (interp_expr e2),
			    append
			      (build_complex_app (Var "safe_upd_") 
				 [Var var; Var tmp1; Var tmp2])
			      (Var tmp2))) 
		| Not_valid ->  
		    Let(tmp1, e1,
			Let(tmp2, 
			    bin_op op
			      (make_app "acc_" [Var var; Var tmp1]) 
			      (interp_expr e2),
			    append
			      (build_complex_app (Var "safe_upd_") 
				 [Var var; Var tmp1; Var tmp2])
			      (Var tmp2))) 
		| Tab n ->  
		    Let(tmp1, e1,
			Let(tmp2, 
			    bin_op op
			      (make_app "acc_offset" 
				 [Var var; Var tmp1; 
				  valid_acc_offset e; 
				  Var (Int64.to_string n)]) 
			      (interp_expr e2),
			    append
			      (build_complex_app (Var "safe_upd_") 
				 [Var var; Var tmp1; Var tmp2])
			      (Var tmp2)))
	end 
    | NEseq(e1,e2) ->
	append (interp_statement_expr e1) (interp_expr e2)
    | NEnop -> 
	Void
    | NEcond(e1,e2,e3) ->
	If(interp_boolean_expr e1, interp_expr e2, interp_expr e3)
    | NEstring_literal s -> 
	unsupported e.nexpr_loc "string literal"
    | NEarrow (e,z,s) ->
	let te = interp_expr e in
	let var = zoned_name s.var_unique_name (Cnorm.type_why e) in
	let valid = 
	  match e.nexpr_type.Ctypes.ctype_node with
	    | Tpointer (valid,_)  
	    | Tarray (valid,_,_) -> valid
	    | Tstruct _ -> Valid 
	    | _ -> assert false
	in
	begin 
	  match valid with 
	    | Valid ->  Output.make_app "safe_acc_" [Var(var);te] 
	    | Not_valid -> Output.make_app "acc_" [Var(var);te] 
	    | Tab n -> Output.make_app "acc_offset" [Var(var);te;
						     valid_acc_offset e;
						     Var (Int64.to_string n)] 
	end
    | NEunary (Ustar, e) -> assert false
    | NEunary (Uplus, e) ->
	interp_expr e
    | NEunary(Uminus, e) -> 
	begin match e.nexpr_type.Ctypes.ctype_node with
	  | Tenum _ | Tint _ -> 
	      make_app "neg_int" [interp_expr e]
	  | Tfloat fk -> 
	      build_minimal_app (float_unop fk Uminus) [interp_expr e]
	  | _ -> 
	      assert false
	end
    | NEunary (Uint_of_float, e1) ->
	interp_int_of_float e1.nexpr_type (interp_expr e1)
    | NEunary (Ufloat_of_int, e1) ->
	interp_float_of_int e.nexpr_type (interp_expr e1)
    | NEunary (Ufloat_conversion, e1) ->
	interp_float_conversion e1.nexpr_type e.nexpr_type (interp_expr e1)
     | NEunary (Uint_conversion, e1) ->
	interp_int_conversion e1.nexpr_type e.nexpr_type (interp_expr e1)
    | NEunary (Utilde, e) ->
	make_app "bw_compl" [interp_expr e]
    | NEunary (Uamp, e) ->
	interp_address e
    | NEcall{ncall_fun = e; ncall_args = args ; ncall_zones_assoc = assoc } -> 
	interp_call e args assoc
    | NEcast({Ctypes.ctype_node = Tpointer _}, 
	     {nexpr_node = NEconstant (IntConstant "0")}) ->
	Var "null"
    | NEcast(t,e1) -> 
	begin match t.Ctypes.ctype_node, e1.nexpr_type.Ctypes.ctype_node with
	  | (Tenum _ | Tint _), (Tenum _ | Tint _) ->
	      interp_expr e1
	  | Tfloat _, Tfloat _ -> 
	      interp_float_conversion e1.nexpr_type t (interp_expr e1)
	  | Tfloat _, (Tenum _ | Tint _) ->
	      let e = make_app "real_of_int" [interp_expr e1] in
	      interp_float_conversion c_real t e
	  | (Tenum _ | Tint _), Tfloat _ ->
	      interp_int_of_float e1.nexpr_type (interp_expr e1)
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      interp_expr e1
	  | _ -> 
	      unsupported e.nexpr_loc "cast"
	end
    | NEmalloc (_, e) ->
	make_app "malloc_parameter" [interp_expr e]

and interp_boolean_expr e =
  match e.nexpr_node with
    | NEbinary(e1, (Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		   |Blt_float _ | Bgt_float _ | Ble_float _ | Bge_float _ 
		   |Beq_float _ | Bneq_float _
		   |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		   |Beq_pointer | Bneq_pointer 
		   |Blt | Bgt | Ble | Bge | Beq | Bneq as op), e2) ->
	bin_op op (interp_expr e1) (interp_expr e2)
    | NEbinary (e1, Band, e2) ->
	And(interp_boolean_expr e1, interp_boolean_expr e2)
    | NEbinary (e1, Bor, e2) ->
	Or(interp_boolean_expr e1, interp_boolean_expr e2)
    | NEunary (Unot, e) ->
	Not(interp_boolean_expr e)
    (* otherwise e <> 0 *)
    | _ -> 
	let cmp,zero = match e.nexpr_type.Ctypes.ctype_node with
	  | Tenum _ | Tint _ -> "neq_int_", Cte (Prim_int "0")
	  | Tfloat fk -> "neq_real_", Cte (Prim_real "0.0")
	  | Tarray _ | Tpointer _ -> "neq_pointer", Var "null"
	  | _ -> assert false
	in
	build_complex_app (Var cmp) [interp_expr e; zero]

and interp_incr_expr op e =
  let top,one = interp_incr_op e.nexpr_type op in
  match interp_lvalue e with
    | LocalRef v ->
	begin
	  match op with
	    | Upostfix_dec | Upostfix_inc ->
		Let("caduceus",Deref(v.var_unique_name),
		    append 
		      (Assign(v.var_unique_name,
			      make_app_e top [Var "caduceus";one]))
		      (Var "caduceus"))
	    | Uprefix_dec | Uprefix_inc ->
		let n = v.var_unique_name in
		append 
		  (Assign(n,
			  App(App(top, Deref n), one)))
		  (Deref n)
	end
    | HeapRef(valid,var,e') ->
	begin
	  let acc = match valid with 
	    | Valid ->  make_app "safe_acc_" [Var var;Var "caduceus1"] 
	    | Not_valid -> make_app "acc_" [Var var;Var "caduceus1"] 
	    | Tab n -> make_app "acc_offset" [Var var;Var "caduceus1";
					      valid_acc_offset e;
					      Var (Int64.to_string n)] 
	  in
	  match op with
	    | Upostfix_dec | Upostfix_inc ->
		Let("caduceus1",e',
		    Let("caduceus2",
			acc,
			append
			  (make_app "safe_upd_" 
			     [Var var;Var "caduceus1";
			      make_app_e top [one;Var "caduceus2"]])
			  (Var "caduceus2")))
	    | Uprefix_dec | Uprefix_inc ->
		Let("caduceus1",e',
		    Let("caduceus2",
			make_app_e top
			  [acc;one],
			append
			  (make_app "safe_upd_" 
			     [Var var;Var "caduceus1";Var "caduceus2"])
			  (Var "caduceus2")))
	end		      

and interp_lvalue e =
  match e.nexpr_node with
    | NEvar (Var_info v) -> LocalRef(v)
    | NEvar (Fun_info v) -> assert false
    | NEunary(Ustar,e1) -> assert false
    | NEarrow (e1,_,f) ->
	let valid =
	  match e1.nexpr_type.Ctypes.ctype_node with
	    | Tpointer(v,_) | Tarray(v,_,_) -> v
	    | Tstruct _ -> Valid
	    | _ -> assert false
	in 
	HeapRef(valid,
		zoned_name f.var_unique_name (Cnorm.type_why e1), 
		interp_expr e1)
    | _ -> 
	assert false (* wrong typing of lvalue ??? *)

and interp_address e = match e.nexpr_node with
  | NEvar (Var_info v) -> 
      assert (v.var_is_referenced); 
       begin match e.nexpr_type.Ctypes.ctype_node with
       | Tstruct _ | Tunion _ -> Deref v.var_unique_name
       | _ -> Var v.var_unique_name
       end
  | NEvar (Fun_info v) -> unsupported e.nexpr_loc "& operator on functions"
  | NEunary (Ustar, _) -> assert false
  | NEarrow (e1,_, f) ->
      begin match e.nexpr_type.Ctypes.ctype_node with
	| Tenum _ | Tint _ | Tfloat _ -> 
  	    interp_expr e1
	| Tstruct _ | Tunion _ | Tpointer _ | Tarray _ ->
	    let var = zoned_name f.var_unique_name (Cnorm.type_why e1) in
	    let valid = 
	      match e1.nexpr_type.Ctypes.ctype_node with
		| Tpointer (valid,_)  
		| Tarray (valid,_,_) -> valid
		| Tstruct _ -> Valid 
		| _ -> assert false
	    in
	    begin 
	      match valid with 
		| Valid -> build_complex_app (Var "safe_acc_")
		    [Var var; interp_expr e1]
		| Not_valid ->build_complex_app (Var "acc_")
		    [Var var; interp_expr e1]
		| Tab n-> build_complex_app (Var "acc_offset")
		    [Var var; interp_expr e1; valid_acc_offset e1;
		     Var (Int64.to_string n)]
	    end
	| _ -> unsupported e.nexpr_loc "& operator on a field"
      end
  | _ -> 
      assert false (* not a left value *)

and interp_statement_expr e =
  match e.nexpr_node with
    | NEseq(e1,e2) ->
	append (interp_statement_expr e1) (interp_statement_expr e2)
    | NEnop -> 
	Void
    | NEassign(l,e) ->
	begin
	  match interp_lvalue l with
	    | LocalRef(v) ->
		Assign(v.var_unique_name,interp_expr e)
	    | HeapRef(valid,var,e1) ->
		begin
		  match valid with 
		    | Valid -> (build_complex_app (Var "safe_upd_")
				  [Var var;e1; interp_expr e])
		    | Not_valid -> (build_complex_app (Var "upd_" )
				      [Var var;e1; interp_expr e])
		    | Tab n-> (build_complex_app (Var "upd_offset")
				 [Var var;e1; interp_expr e; 
				  valid_acc_offset l;
				  Var (Int64.to_string n)])
		end
	end 
    | NEincr(op,e) ->
	let top,one = interp_incr_op e.nexpr_type op in
	begin
	  match interp_lvalue e with
	    | LocalRef v ->
		Assign(v.var_unique_name,
		       make_app_e top [Deref(v.var_unique_name); one])
	    | HeapRef(valid,var,e1) -> 
		let acc = match valid with 
		  | Valid -> make_app "safe_acc_" [Var var; Var "caduceus1"]
		  | Not_valid ->  make_app "acc_"[Var var; Var "caduceus1"]
		  | Tab n -> make_app  "acc_offset" [Var var; Var "caduceus1";
						   valid_acc_offset e;
						   Var (Int64.to_string n)]
		in
		Let("caduceus1",e1,
		    Let("caduceus2",
			acc,
			make_app "safe_upd_"
			  [Var var; Var "caduceus1"; 
			   make_app_e top [Var "caduceus2"; one]]))
	end
    | NEcall {ncall_fun = e1;ncall_args =  args;ncall_zones_assoc = assoc} -> 
	let app = interp_call e1 args assoc in
	if e.nexpr_type.Ctypes.ctype_node = Tvoid then
	  app
	else
	  Let (tmp_var (), app, Void)
    | NEassign_op (l, op, e) -> 
	begin
	  match interp_lvalue l with
	    | LocalRef(v) ->
		let n = v.var_unique_name in
		Assign(n, bin_op op (Deref n) (interp_expr e))
	    | HeapRef(valid,var,e1) -> 
		let acc = match valid with 
		  | Valid -> make_app "safe_acc_" [Var var;Var "caduceus1"]
		  | Not_valid -> make_app "acc_"[Var var;Var "caduceus1"]
		  | Tab n-> make_app "acc_offset"[Var var;Var "caduceus1";
						 valid_acc_offset l;
						 Var (Int64.to_string n)]
		in
		Let("caduceus1",e1,
		    Let("caduceus2",acc ,
			make_app "safe_upd_"
			  [Var var; Var "caduceus1"; 
			   bin_op op (Var "caduceus2") (interp_expr e)]))
	end 
    | NEcast (_, _)
    | NEcond (_, _, _)
    | NEbinary (_, _, _)
    | NEunary (_, _)
    | NEarrow _
    | NEvar _
    | NEstring_literal _
    | NEconstant _ 
    | NEmalloc _ -> 
	unsupported e.nexpr_loc "statement expression"

and interp_call e1 args assoc = 
  match e1.nexpr_node with
    | NEvar (Fun_info v) ->
	let reads = ZoneSet.fold 
	  (fun (z,s,ty) acc ->
	     let z = repr z in
	     (z,(try Cnorm.assoc_zone z assoc with Not_found -> z),s,ty)::acc)
	  v.function_reads [] 
	in
	let targs = List.map interp_expr args in
	let targs = List.fold_right 
	  (fun (z0,z1,s,_) l -> 
	     let z = repr z1 in
	     if z0.zone_is_var then
	       Var(zoned_name s (Pointer z))::l
	     else l)
	  reads targs 
	in
	build_complex_app (Var (v.fun_unique_name ^ "_parameter")) 
	  targs
    | _ -> 
	unsupported e1.nexpr_loc "call of a non-variable function"

and valid_acc_offset e =
  match e.nexpr_node with 
    | NEnop -> assert false
    | NEconstant _ -> assert false
    | NEstring_literal _ -> assert false
    | NEvar _ -> assert false
    | NEarrow (e,_,_)  -> valid_acc_offset e
    | NEseq _ -> assert false
    | NEassign _ -> assert false
    | NEassign_op _ -> assert false
    | NEunary _ -> assert false
    | NEincr _ -> assert false
    | NEbinary (_,Badd_pointer_int,i) -> interp_expr i    
    | NEbinary (_,_,_) -> assert false
    | NEcall _ -> assert false
    | NEcond _ -> assert false
    | NEcast _ -> assert false
    | NEmalloc _ -> assert false
 
 

module StringMap = Map.Make(String)

type mem_or_ref = Reference of bool | Memory of Output.term list

type term_loc_interp = Pset of Output.term | Term of Output.term

let collect_locations before acc loc =
  (* term_loc t interprets t either as Term t' with t' a Why term of type 
     pointer, or as Pset s with s a Why term of type pset *)
  let rec term_or_pset t = match t.nterm_node with
    | NTarrow (e,z, f) ->
	let ty = Cnorm.type_why_for_term e in
	assert (same_why_type ty (Pointer z));
	let m = 
	  interp_var (Some before) 
	    (zoned_name f.var_unique_name ty) in
	begin match term_or_pset e with
	  | Term te -> Term (LApp ("acc", [m; te]))
	  | Pset s -> Pset (LApp ("pset_star", [s; m]))
	end
    | NTrange (e, None, None, z, f) ->
	let ty = Cnorm.type_why_for_term e in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	Pset (LApp ("pset_acc_all", [pset e; interp_var (Some before) var]))
    | NTrange (e, None, Some a,z,f) ->
	let ty = Cnorm.type_why_for_term e in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	Pset (LApp ("pset_acc_range_left", 
		    [pset e; interp_var (Some before) var;
		     interp_term (Some before) before a]))
    | NTrange (e, Some a, None,z,f) ->
	let ty = Cnorm.type_why_for_term e in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	Pset (LApp ("pset_acc_range_right", 
		    [pset e; interp_var (Some before) var;
		     interp_term (Some before) before a]))
    | NTrange (e, Some a, Some b,z,f) ->
	let ty = Cnorm.type_why_for_term e in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	Pset (LApp ("pset_acc_range", 
		    [pset e; interp_var (Some before) var;
		     interp_term (Some before) before a;
		     interp_term (Some before) before b]))
    | _ ->
	Term (interp_term (Some before) before t)

  (* term_loc t interprets t as a Why term of type pset *)
  and pset t = match term_or_pset t with
    | Pset l -> l
    | Term t -> LApp ("pset_singleton", [t])
  in
  let var,iloc = match loc.nterm_node with
    | NTarrow(e,z,f) ->
	let ty = Cnorm.type_why_for_term e in
	assert (same_why_type ty (Pointer z));
	zoned_name f.var_unique_name ty, Some (pset e)
    | NTvar v ->
	v.var_unique_name, None
    | NTrange (t, None, None,z,f) -> 
	let ty = Cnorm.type_why_for_term t in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	let loc = LApp ("pset_all", [pset t]) in
	var, Some loc
    | NTrange (t, None, Some a,z,f) -> 
	let ty = Cnorm.type_why_for_term t in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	let loc = LApp ("pset_range_left", 
			[pset t; interp_term (Some before) before a]) in
	var, Some loc
    | NTrange (t, Some a, None,z,f) -> 
	let ty = Cnorm.type_why_for_term t in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	let loc = LApp ("pset_range_right", 
			[pset t; interp_term (Some before) before a]) in
	var, Some loc
    | NTrange(t1, Some t2, Some t3,z,f) -> 
	let ty = Cnorm.type_why_for_term t1 in
	assert (same_why_type ty (Pointer z));
	let var = zoned_name f.var_unique_name ty in
	let loc = 
	  LApp("pset_range",
	       [pset t1;
		interp_term (Some before) before t2;
		interp_term (Some before) before t3;])
	in
	var, Some loc
    | _ ->
	assert false
  in
  try
    let p = StringMap.find var acc in
    (match p, iloc with
       | Reference _, None -> StringMap.add var (Reference true) acc
       | Memory l, Some iloc -> StringMap.add var (Memory (iloc::l)) acc
       | Reference _,Some n -> eprintf "iloc = %a\n" fprintf_term n;assert false
       | Memory _,_ -> assert false)
  with Not_found -> 
    (match iloc with
       | None -> StringMap.add var (Reference true) acc
       | Some l -> StringMap.add var (Memory [l]) acc)

let rec make_union_loc = function
  | [] -> LVar "pset_empty"
  | [l] -> l
  | l::r -> LApp("pset_union",[l;make_union_loc r])

let interp_assigns before assigns = function
  | Some locl ->
      let m = HeapVarSet.fold
	(fun v m -> 
	   if Ceffect.is_alloc v then m 
	   else StringMap.add (heap_var_name v) (Reference false) m)
	assigns.Ceffect.assigns_var StringMap.empty 
      in
      let m = ZoneSet.fold
	(fun (z,s,ty) m -> 
	   StringMap.add (zoned_name s (Pointer z)) (Memory []) m)
	assigns.Ceffect.assigns m 
      in
      
      let l = 
	List.fold_left (collect_locations before) m locl
      in
      StringMap.fold
	(fun v p acc -> match p with
	   | Memory p ->
	       if arith_memory_model then
		 make_and acc
		   (LPred("not_assigns",
			  [LVarAtLabel(v,before);
			   LVar v; make_union_loc p]))
	       else
		 make_and acc
		   (LPred("not_assigns",
			  [LVarAtLabel("alloc",before); LVarAtLabel(v,before);
			   LVar v; make_union_loc p]))
	   | Reference false ->
	       make_and acc (LPred("eq", [LVar v; LVarAtLabel(v,before)]))
	   | Reference true ->
	       acc)
	l LTrue
  | None ->
      LTrue

(* we memoize the translation of weak invariants *)
let weak_invariant = 
  let h = Hashtbl.create 97 in
  fun id p -> 
    try 
      Hashtbl.find h id
    with Not_found -> 
      let p = interp_predicate None "" p in
      Hashtbl.add h id p;
      p

let weak_invariants_for hvs =
  Hashtbl.fold
    (fun id (p,e) acc -> 
       if Ceffect.intersect_only_alloc e hvs then acc
       else make_and (weak_invariant id p) acc) 
    Ceffect.weak_invariants LTrue

(* we memoize the translation of strong invariants *)

let strong_invariant = 
  let h = Hashtbl.create 97 in
  fun id p  -> 
    try 
      Hashtbl.find h id
    with Not_found -> 
      let p = interp_predicate None "" p in
      Hashtbl.add h id p;
      p

let interp_strong_invariants () =
  Hashtbl.fold
    (fun id (p,e,args) acc -> 
       let args = 
	 HeapVarSet.fold 
	   (fun x acc -> 
	      (heap_var_name x, 
	       Info.output_why_type x.var_why_type) :: acc) 
	   e.Ceffect.reads_var args
       in
       let args = 
	 ZoneSet.fold
	   (fun (z,s,ty) acc ->
	      (*if z.zone_is_var then*)
		(zoned_name s (Pointer z), 
		 (Info.output_why_type (Info.Memory(ty,z))))::acc
	      (*else acc*))
	   e.Ceffect.reads args in
       if args = [] then acc else
       (Predicate(false,id,args,interp_predicate None "" p))::acc)
    Ceffect.strong_invariants_2 []
    

let strong_invariant_name id reads_var reads =
  let args = 
    HeapVarSet.fold (fun x acc -> (LVar (heap_var_name x)) :: acc) reads_var []
  in
  let args = 
    ZoneSet.fold 
      (fun (z,s,ty) l -> let z = repr z in
       (LVar (zoned_name s (Pointer z)))::l)
      reads args in
  LPred(id,args)
    
let extract_var_from_effect var lf =
  List.fold_left (fun acc (zf,nf,tyf) -> 
		    if (var.var_unique_name = nf) 
		    then (zf,nf,tyf)::acc else acc)[] lf 

let add ef ep =
  let lp = (HeapVarSet.elements ep) in
  let lf = (ZoneSet.elements ef) in
  let l = List.fold_right 
    (fun var acc -> (extract_var_from_effect var lf)::acc ) lp [] in
  match l with 
    | [] -> []
    | [l] -> List.fold_left (fun acc (z,n,_) -> [(z,n)]::acc) [] l
    | [l1;l2] -> 
	List.fold_left 
	  (fun acc (zx,nx,tyx) -> 
	     List.fold_left 
	       (fun acc (zy,ny,tyy) -> 
		  if same_why_type tyx tyy && same_zone zx zy 
		  then ([(zx,nx);(zy,ny)]::acc) else acc) acc l2) [] l1 
    | _ -> assert false

let subst a p =
  let q  =
    match p.npred_node with
      | NPapp {napp_pred = f; napp_args = tl; napp_zones_assoc = assoc} -> 
	  NPapp {napp_pred = f;
		 napp_args =
	      (List.map (fun (z,n) -> 
			   { nterm_node = 
			       (NTvar (default_var_info (zoned_name n (Pointer z))));
			     nterm_loc = Loc.dummy_position;
			     nterm_type = c_void}) a)@tl;
		 napp_zones_assoc = assoc}
      | _ -> assert false 
  in
  { p with npred_node = q} 

let strong_invariants_for hvs =
  let pred =
    Hashtbl.fold
      (fun id (p,e1,e2) acc ->
	 let l = add hvs.Ceffect.reads e2.Ceffect.reads_var in
	 let rec add_pred id p l acc = 
	   match l with 
	     | [] -> acc
	     | a::l -> 
		 let p' = subst a p in 
		 let p'' = interp_predicate None "" p' in
		 make_and p'' (add_pred id p l acc)
	 in
	 add_pred id p l acc)
      Ceffect.invariants_for_struct 
      LTrue
  in
  Hashtbl.fold
    (fun id (p,e1,e2) acc ->
       if ZoneSet.subset e2.Ceffect.reads hvs.Ceffect.reads 
	 && HeapVarSet.subset e2.Ceffect.reads_var hvs.Ceffect.reads_var then
	 (make_and 
	   (if (Ceffect.mem_strong_invariant_2 id) || (Cenv.mem_pred id)
	    then
	      strong_invariant_name id e1.Ceffect.reads_var e1.Ceffect.reads
	    else
	      strong_invariant id p)  acc)
       else acc) 
    Ceffect.strong_invariants  
    pred

let alloc_extends () = 
  (* [alloc_extends] should not be used with the arithmetic memory model *)
  assert (not arith_memory_model);
  LPred ("alloc_extends", [LVar "alloc@"; LVar "alloc"])

let alloc_extends_at label = 
  (* [alloc_extends] should not be used with the arithmetic memory model *)
  assert (not arith_memory_model);
  LPred ("alloc_extends", [LVarAtLabel ("alloc", label); LVar "alloc"])

let interp_spec add_inv effect s =
  let tpre_without = 
    make_and
      (interp_predicate_opt None "" s.requires)
      (if add_inv then weak_invariants_for effect else LTrue) in
  let tpre_with = 
    make_and
      tpre_without
      (strong_invariants_for effect)
  and tpost = 
   make_and
     (interp_predicate_opt None "" s.ensures)
     (make_and 
	(interp_assigns "" effect s.assigns)
	(make_and
	   (if add_inv then weak_invariants_for effect else LTrue)
	   (if Ceffect.assigns_alloc effect then alloc_extends () else LTrue)))
  in 
  (tpre_with,tpre_without,tpost)

(***
let alloc_on_stack loc v t =
  let form = 
    Cnorm.make_and 
      (List.fold_left (fun x v2 -> Cnorm.make_and x 
			   (Cseparation.separation loc v v2)) 
	 Cnorm.nptrue !Ceffect.global_var)
      (Cseparation.valid_for_type ~fresh:true loc v.var_name t)
  in
  BlackBox(Annot_type(LTrue,base_type "pointer",["alloc"],["alloc"],
		      make_and 
			(interp_predicate None "" form)
			(LPred ("alloc_stack", 
				[LVar "result"; LVar "alloc@"; LVar "alloc"])),
		      None))
***)

let interp_decl d acc = 
  match d.node with 
    | Ntypedef _
    | Ntypedecl { Ctypes.ctype_node = Tstruct _ | Tunion _ } -> 
	acc
    | Ntypedecl { Ctypes.ctype_node = Tenum _ } -> 
	unsupported d.loc "local enum type"
    | Ntype _
    | Ndecl _
    | Ntypedecl _
    | Naxiom _
    | Ninvariant _
    | Ninvariant_strong _
    | Nlogic _ ->
	assert false


let interp_invariant label effects annot =
  let inv = match annot.invariant with
    | None -> LTrue
    | Some inv -> interp_predicate None "init" inv
  in
  (* WHY does not distinguish invariants from assumed invariants presently *)
  let assinv = match annot.assume_invariant with
    | None -> LTrue
    | Some inv -> interp_predicate None "init" inv
  in
  let inv = match inv,assinv with
    | LTrue,p | p,LTrue -> p
    | p1,p2 -> LAnd (p1,p2)
  in
  let inv = 
    make_and 
      (interp_assigns label effects annot.loop_assigns) 
      (make_and 
	 inv 
	 (if Ceffect.assigns_alloc effects 
	  then alloc_extends_at label else LTrue))
  in
  let var = match annot.variant with
    | None -> None
    | Some (var,r) -> Some (interp_term None "init" var, r)
  in
  (inv, var)

let new_label = let r = ref 0 in fun () -> incr r; "label_" ^ string_of_int !r

let try_with_void ex e = Try (e, ex, None, Void)  

let break b e = if b then try_with_void "Break" e else e

let continue b e = if b then try_with_void "Continue" e else e    

let return_exn ty = match ty.Ctypes.ctype_node with
  | Tenum _ | Tint _ -> "Return_int"
  | Tfloat _ when not floats -> "Return_real"
  | Tfloat Float -> "Return_single"
  | Tfloat Double -> "Return_double"
  | Tfloat LongDouble -> "Return_quad"
  | _ -> "Return_pointer"

(* [abrupt_return] contains the exception used for last abrupt return if any *)
let abrupt_return = ref None

let catch_return e = match !abrupt_return with
  | None -> 
      e
  | Some "Return" ->
      Try (e, "Return", None, Void)
  | Some r ->
      let tmp = tmp_var () in
      Try (e, r, Some tmp, Var tmp)

let unreachable_block = function
  | [] -> ()
  | s::_ -> warning s.nst_loc "unreachable statement"

(* Interpretation of switch *)

open Cconst

let make_switch_condition tmp l = 
  if IntMap.is_empty l 
  then assert false
  else
    let a = 
      IntMap.fold 
	(fun x n test -> 
	   make_or_expr 
	     (App(App (Var "eq_int_",Var tmp), (interp_expr n))) test) 
	l
	(Cte (Prim_bool false))
    in
    (a,l)
    
let make_switch_condition_default tmp l used_cases= 
  let fl = IntMap.fold
    (fun x e m -> if IntMap.mem x l
     then m
     else IntMap.add x e m) used_cases IntMap.empty in
  let cond =
    IntMap.fold 
      (fun x e test -> 
	 make_and_expr 
	   (App(App (Var "neq_int_",Var tmp),(interp_expr e))) test)
      fl
      (Cte (Prim_bool true))
  in
  cond,fl

let in_struct v1 v = 
  let zone = Cnorm.find_zone v1 in
  let () = Cnorm.type_why_new_zone zone v in
  { nexpr_node = NEarrow (v1,zone,  v); 
    nexpr_loc = v1.nexpr_loc;
    nexpr_type = v.var_type }

let noattr loc ty e =
  { nexpr_node = e;
    nexpr_type = ty;
    nexpr_loc  = loc
  }


let labels_table = Hashtbl.create 17

let append_block e (f,l) = (append e f,l)

(* [ab] indicates if returns are abrupt *)

let rec interp_statement ab may_break stat = match stat.nst_node with
  | NSnop -> 
      Void
  | NSexpr e ->
      interp_statement_expr e
  | NSreturn eopt ->
      if ab then match eopt with
	| None -> 
	    abrupt_return := Some "Return";
	    Raise ("Return", None)
	| Some e -> 
	    let r = return_exn e.nexpr_type in 
	    abrupt_return := Some r;
	    Raise (r, Some (interp_expr e))
      else begin match eopt with
	| None -> Void
	| Some e -> interp_expr e
      end
  | NSif(e,s1,s2) -> 
      If(interp_boolean_expr e,
	 (interp_statement ab may_break s1), 
	 (interp_statement ab may_break s2))
  | NSfor(annot,e1,e2,e3,body) ->
      let label = new_label () in
      let ef = 
	Ceffect.ef_union 
	  (Ceffect.ef_union (Ceffect.expr e1)
	     (Ceffect.expr e2))
	  (Ceffect.ef_union (Ceffect.expr e3) 
	     (Ceffect.statement body))
      in
      let (inv,dec) = interp_invariant label ef annot in
      Output.Label 
	(label,
	 append
	   (interp_statement_expr e1)
	   (break body.nst_break 
	      (make_while (interp_boolean_expr e2) inv dec 
		 (append 
		    (continue body.nst_continue
		       (interp_statement true (ref false) body))
		    (interp_statement_expr e3)))))
  | NSwhile(annot,e,s) -> 
      let label = new_label () in
      let ef = 
	Ceffect.ef_union (Ceffect.expr e) (Ceffect.statement s) 
      in
      let (inv,dec) = interp_invariant label ef annot in
      Output.Label 
	(label,
	 break s.nst_break
	    (make_while (interp_boolean_expr e) inv dec 
	       (continue s.nst_continue 
		  (interp_statement true (ref false) s))))
  | NSdowhile(annot,s,e) -> 
      let label = new_label () in
      let ef = 	Ceffect.ef_union (Ceffect.expr e) (Ceffect.statement s) 
      in
      let (inv,dec) = interp_invariant label ef annot in
      Output.Label 
	(label,
	 break true
	   (make_while (Cte (Prim_bool true)) inv dec
	      (append 
		 (continue s.nst_continue
		    (interp_statement true (ref false) s))
		 (If (Not (interp_boolean_expr e), 
		      Raise ("Break", None), Void)))))
  | NSblock(b) -> 
      interp_block ab may_break b
  | NSbreak -> 
      may_break := true;
      Raise ("Break", None)
  | NScontinue -> 
      Raise ("Continue", None)
  | NSlabel(lab,s) -> 
      Output.Label (lab, interp_statement ab may_break s)
  | NSgoto(GotoForwardOuter,lab) ->
      Hashtbl.add labels_table lab ();
      Raise ("Goto_" ^ lab, None)
  | NSgoto(GotoForwardInner,lab) ->
      unsupported stat.nst_loc "forward inner goto"
  | NSgoto(GotoBackward,lab) ->
      (* When planning to support backward gotos, add a widening node inside 
	 the induced loop in the operational graph created for various 
	 dataflow analyses in [Cabsint]. *)
      unsupported stat.nst_loc "backward goto"
  | NSswitch(e,used_cases,l) ->
      let tmp = tmp_var() in
      let switch_may_break = ref false in
      let res = 
	Output.Let(tmp, interp_expr e,
		   interp_switch tmp ab switch_may_break l 
		     IntMap.empty used_cases false)
      in
      if !switch_may_break then
	Try(res,"Break", None,Void)
      else
	res
  | NSassert(pred) -> 
      Output.Assert(interp_predicate None "init" pred, Void)
  | NSassume _ -> 
      (* WHY does not have an assume expression for the moment *)
      Void
  | NSlogic_label(l) -> 
      Output.Label (l, Void)
  | NSspec (spec,s) ->
      let eff = Ceffect.statement s in
      let pre,_,post = interp_spec false eff spec in
      Triple(true,pre,interp_statement ab may_break s,post,None)
  | NSdecl(ctype,v,init,rem) -> 
      lprintf 
	"translating local declaration of %s@." v.var_unique_name;
      let tinit,(decl,_) = match init with 
	| None | Some (Ilist [])->
	    begin match ctype.Ctypes.ctype_node with
	      | Tenum s ->    
		  if typing_predicates then  
		    App(Var("any_enum_" ^s^ "_parameter"),Var("void")) 
		  else 
		    App(Var("any_int"),Var("void"))
	      | Tint si ->
		    if typing_predicates then 
		      let n = (Invariant.function_for_int_type si) 
			^"_parameter" in
		      App(Var(n),Var("void"))
		    else 
		      App(Var("any_int"),Var("void"))
	      | Tfloat fk -> App(Var (any_float fk),Var("void"))
	      | Tarray (_,_, None) | Tpointer _ -> 
		  App(Var "any_pointer", Var "void")
	      | Tarray (_,_, Some n) ->
		  App (Var "alloca_parameter", 
		       Cte (Prim_int (Int64.to_string n)))
	      | Tstruct _ | Tunion _ ->
		  App (Var "alloca_parameter", Cte (Prim_int "1"))
	      | Tvoid | Tvar _ | Tfun _ -> assert false
	    end,([],[])
	| Some (Iexpr e)  ->   
	    interp_expr e, ([],[])
	| Some (Ilist _) ->
	    assert false
      in
      let decl = List.fold_left (fun acc x ->
				   acc@[interp_statement ab may_break x]) 
		   [] decl in
      if v.var_is_assigned then
	Let_ref(v.var_unique_name,tinit,
		Block (decl@[interp_statement ab may_break rem]))
      else
	Let(v.var_unique_name,tinit,
	    Block (decl@[interp_statement ab may_break rem]))

and interp_block ab may_break statements =
  let rec block = function
    | [] -> 
	Void,[]
    | { nst_node = NSlabel(lab,st) } :: bl ->
	let (be,bl) = block (st::bl) in
	Raise("Goto_"^lab,None),(lab,be)::bl
    | [s] ->
	interp_statement ab may_break s,[]
    | { nst_node = NSnop } :: bl ->
	block bl
    | { nst_node = NSif (e, s1, s2) } as s :: bl ->
	begin match s1.nst_term, s2.nst_term with
	  | true, true ->
	      append_block (interp_statement true may_break s) (block bl)
	  | false, false ->
	      unreachable_block bl;
	      interp_statement ab may_break s,[]
	  | true, false ->
	      let (be,bl) = block (s1::bl) in
	      If (interp_boolean_expr e, 
		  be, interp_statement ab may_break s2), bl
	  | false, true ->
	      let (be,bl) = block (s2::bl) in
	      If (interp_boolean_expr e,
		  interp_statement ab may_break s1, be), bl
	end
    | s :: bl ->
	if not s.nst_term then unreachable_block bl;
	append_block (interp_statement true may_break s) (block bl)
  in
  let be,bl = block statements in
  List.fold_left 
    (fun acc (lab,e) ->
       Try(acc,"Goto_"^lab,None,e)) be bl


and interp_switch tmp ab may_break l c used_cases post_default =
  match l with
    | (lc, i):: l ->
	if IntMap.is_empty lc
	then
	  let (a,lc) = make_switch_condition_default tmp c used_cases in
	  (* [bl] is actually unreachable *)
	  let (linstr,final) = interp_case ab may_break i in
	  if final 
	  then
	    Output.If(a,
		      Block linstr
			,
			interp_switch tmp ab may_break l lc used_cases false)
	  else
	    Block ((Output.If(a,
			      Block linstr
				,
				Void))::[interp_switch tmp ab may_break l lc 
					   used_cases true])	
	else  
	  let (a,lc) = 
	    if post_default
	    then
	      make_switch_condition_default tmp lc c
	    else
	      make_switch_condition tmp 
		(IntMap.fold 
		   ( fun x e m ->
		       IntMap.add x e m)
		   c
		   lc) 
	  in
	  let (linstr,final) = interp_case ab may_break i in
	  if final
	  then
	    Output.If(a,
		      Block linstr,
		      interp_switch tmp ab may_break l 
			IntMap.empty used_cases false)
	  else
	    Block ([Output.If(a,
			      Block linstr,
			      Void);interp_switch tmp ab may_break 
		      l lc  used_cases post_default])
    | [] -> Void

and interp_case ab may_break i =
  match i with
    | [] -> [],false
    | a::i -> 
	if a.nst_term
	then
	  let (instr,isfinal) = interp_case ab may_break i in
	  ((interp_statement ab may_break a)::instr),isfinal
	else
	  begin
	    unreachable_block i;
	    (if a.nst_node=NSbreak 
	     then [] 
	     else [interp_statement ab may_break a]),true
	  end
	  
	  

let interp_predicate_args id args =
  let args =
    List.fold_right
      (fun (id,t) args -> 
	 (id.var_unique_name,Info.output_why_type id.var_why_type)::args)
      args []
  in
  let args = 
    HeapVarSet.fold
      (fun arg t -> (heap_var_name arg,Info.output_why_type arg.var_why_type) 
	 :: t)
      id.logic_heap_args args in
  ZoneSet.fold 
    (fun (z,s,ty) l -> 
	 (zoned_name s (Pointer z), 
	  (Info.output_why_type (Info.Memory(ty,z))))::l)
    id.logic_heap_zone args

let type_to_base_type l = 
  List.map (fun (x,y) -> (x,Info.output_why_type y)) l

let cinterp_logic_symbol id ls =
  match ls with
    | NPredicate_reads(args,locs) -> 
	let args = interp_predicate_args id args in
	let ty = 
	  List.fold_right 
	    (fun (x,t) ty -> 
	       Prod_type (x, Base_type t, ty)) 
	    args 
	    (Base_type ([],"prop"))
	in
	Logic(false, id.logic_name, ty)
    | NPredicate_def(args,p) -> 
	let a = interp_predicate None "" p in
	let args = interp_predicate_args id args in
	Predicate(false,id.logic_name, args,a)
    | NFunction(args,ret,_) ->
	let ret_type =
	  match ret.Ctypes.ctype_node with
	    | Tvar s -> base_type s
	    | Tint _ -> base_type "int"
	    | Tfloat fk -> base_type (Cnorm.why_type_for_float_kind fk)
	    | _ -> assert false
	in
	let local_type =
	  List.fold_right
	    (fun (id,ty) t -> 
	       Prod_type(id.var_unique_name,
			 Base_type (Info.output_why_type id.var_why_type),t))
	    args ret_type
	in
	let final_type =
	  HeapVarSet.fold
	    (fun arg t -> 
	       let ty = arg.var_why_type in 
	       Prod_type("",Base_type (Info.output_why_type ty),t))
	    id.logic_heap_args local_type
	in
        let final_type = 
          ZoneSet.fold 
            (fun (z,_,ty) t ->
               Prod_type("",Base_type (Info.output_why_type (Info.Memory(ty,z))),t))
            id.logic_heap_zone final_type in
	Logic(false,id.logic_name,final_type)
    | NFunction_def(args,ret,e) ->
	let e = interp_term None "" e in
	let ret_type = 
	  match ret.Ctypes.ctype_node with
	    | Tvar s -> [], s
	    | Tint _ -> [], "int"
	    | Tfloat fk -> [], Cnorm.why_type_for_float_kind fk
	    | _ -> assert false
	in
	let args = interp_predicate_args id args in
	Output.Function(false,id.logic_name,args,ret_type,e)
	  
let interp_axiom p =
  let a = interp_predicate None "" p
  and e = Ceffect.predicate p in
  let a  =  
    HeapVarSet.fold
      (fun arg t -> LForall
	 (heap_var_name arg,Info.output_why_type arg.var_why_type,t))
      e.Ceffect.reads_var a in
  ZoneSet.fold 
    (fun (z,s,ty) t -> 
       let z = repr z in
       LForall (s^"_"^z.name,Info.output_why_type (Info.Memory(ty,z)),t))
    e.Ceffect.reads a 

let interp_effects e =
  HeapVarSet.fold (fun var acc -> var::acc) e []

let interp_fun_params reads params =
  let l = List.map 
    (fun id ->
       (id.var_unique_name,Base_type(Info.output_why_type id.var_why_type)))
    params  in
  let l = ZoneSet.fold
    (fun (z,s,ty) l ->
       let z = repr z in
       if z.zone_is_var then
	 (zoned_name s (Pointer z), 
	  Ref_type 
	    (Base_type 
	       (Info.output_why_type (Info.Memory(ty,z)))))::l
       else l )
    reads l in
  if l=[]
  then 
      ["tt",unit_type]
  else 
    l
let heap_var_unique_names v =
  HeapVarSet.fold (fun v l -> heap_var_name v::l) v []

let heap_var_unique v =
  ZoneSet.fold (fun (z,s,_) l -> zoned_name s (Pointer z)::l) v []
  
let interp_function_spec id sp ty pl =
  let pre_with,pre_without,post = 
    interp_spec 
      (id != Cinit.invariants_initially_established_info)
      { Ceffect.reads = id.function_reads; 
	Ceffect.assigns = id.function_writes;
	Ceffect.reads_var = id.function_reads_var; 
	Ceffect.assigns_var = id.function_writes_var;
	(* TODO: consider pointer arguments written by function *)
	Ceffect.assigns_under_pointer = HeapVarSet.empty; } 
      sp 
  in
  let tpl = interp_fun_params id.function_reads pl in   
  let r = heap_var_unique_names id.function_reads_var in
  let w = heap_var_unique_names id.function_writes_var in
  let r = (heap_var_unique id.function_reads)@r in
  let w = (heap_var_unique id.function_writes)@w in
  let annot_type = 
    Annot_type
      (pre_without, Base_type (Info.output_why_type id.type_why_fun), r, w, 
       post, None)
  in
  let ty = 
    List.fold_right 
      (fun (x,ct) ty -> Prod_type (x, ct, ty))
      tpl 
      annot_type
  in
  tpl,pre_with,post, Param (false, id.fun_unique_name ^ "_parameter", ty)

let interp_type loc ctype = match ctype.Ctypes.ctype_node with
  | Tenum e ->
      begin match Cenv.tag_type_definition e with
	| Cenv.TTEnum ((Tenum n),el) -> 
	    List.flatten
	      (List.map 
		 (fun (info,v) -> 
		    let x = info.var_unique_name in
		    let v = Int64.to_string v in
		    let a = LPred ("eq_int", [LVar x; LConst(Prim_int v)]) in
		    [Logic (false,x,Base_type ([], "int"));
		     Axiom ("enum_" ^ n ^ "_" ^ x, a)])
		 el)
	| _ -> assert false
      end
  | _ -> 
      []

let interp_located_tdecl ((why_spec,prover_decl) as why) decl =
  match decl.node with
  | Nlogic(id,ltype) -> 
      lprintf "translating logic declaration of %s@." id.logic_name;
      (cinterp_logic_symbol id ltype::why_spec,
       prover_decl)
  | Naxiom(id,p) -> 
      lprintf "translating axiom declaration %s@." id;      
      let a = interp_axiom p in
      (Axiom(id,a)::why_spec, prover_decl)
  | Ninvariant(id,p) -> 
      lprintf "translating invariant declaration %s@." id;      
      why
  | Ninvariant_strong (id,p) ->
      lprintf "translating invariant declaration %s@." id;      
      why
  | Ntypedecl ({ Ctypes.ctype_node = Tenum _ } as ctype)
  | Ntypedef (ctype,_) -> 
      let dl = interp_type decl.loc ctype in 
      dl @ why_spec, prover_decl
  | Ntypedecl { Ctypes.ctype_node = Tstruct _ | Tunion _ } -> 
      why
  | Ntypedecl _ ->
      assert false
  | Ntype _ ->
      why
  | Ndecl(ctype,v,init) -> 
      (* global initialisations already handled in cinit.ml *)
      why
(*  | Nfunspec(spec,ctype,id) -> 
      let tparams,_,_,spec = interp_function_spec id spec ctype id.args in
      (why_code, spec :: why_spec,
       prover_decl)
  | Nfundef(spec,ctype,id,block) ->
      if (id = Cinit.invariants_initially_established_info &&  
	  not !Cinit.user_invariants)
      then
	(why_code, why_spec, prover_decl)
      else
	(reset_tmp_var ();
	 let tparams,pre,post,tspec = 
	   interp_function_spec id spec ctype id.args in
	 let f = id.fun_unique_name in
	 if Coptions.verify id.fun_name then begin try
	   lprintf "translating function %s@." f;
	   abrupt_return := None;
	   let may_break = ref false in
	   let list_of_refs =
	     List.fold_right
	       (fun id bl ->
		  if id.var_is_assigned
		  then 
		 let n = id.var_unique_name in
		 set_unique_name (Var_info id) ("mutable_" ^ n); 
		 unset_formal_param id;
		 (id.var_unique_name,n) :: bl
		  else bl) 
	       id.args [] 
	in
	   let tblock = catch_return 
	     (interp_statement false may_break block) in
	   assert (not !may_break);
	   let tblock = make_label "init" tblock in
	   let tblock =
	     List.fold_right
	       (fun (mut_id,id) bl ->
		  Let_ref(mut_id,Var(id),bl)) list_of_refs tblock in
	   printf "generating Why code for function %s@." f;
	   ((f, Def(f ^ "_impl", Fun(tparams,pre,tblock,post,None)))::why_code,
	    tspec :: why_spec,
	    prover_decl)
	 with Error (_, Cerror.Unsupported s) ->
	   lprintf "unsupported feature (%s); skipping function %s@." s f;
	   eprintf "unsupported feature (%s); skipping function %s@." s f;
	   (why_code,
	    tspec :: why_spec,
	    prover_decl)
	 end else begin
	   lprintf "assuming function %s@." f;
	   (why_code, tspec :: why_spec, prover_decl)
	 end
	)
*)

let interp_c_fun fun_name (spec, ctype, id, block, loc) 
    (why_code,why_spec,prover_decl)   =
(*      let tparams,_,_,spec = interp_function_spec id spec ctype id.args in
      (why_code, spec :: why_spec,
       prover_decl)*)
  if (id = Cinit.invariants_initially_established_info &&  
      not !Cinit.user_invariants)
  then
    (why_code, why_spec, prover_decl)
  else
    (reset_tmp_var ();
     let tparams,pre,post,tspec = 
       interp_function_spec id spec ctype id.args in
     match block with 
       | None -> (why_code, tspec :: why_spec, prover_decl)
       | Some block ->
	   let f = id.fun_unique_name in
	   if Coptions.verify id.fun_name then begin try
	     lprintf "translating function %s@." f;
	     abrupt_return := None;
	     let may_break = ref false in
	     let list_of_refs =
	       List.fold_right
		 (fun id bl ->
		    if id.var_is_assigned
		    then 
		      let n = id.var_unique_name in
		      set_unique_name (Var_info id) ("mutable_" ^ n); 
		      unset_formal_param id;
		      (id.var_unique_name,n) :: bl
		    else bl) 
		 id.args [] 
	     in
	     let tblock = catch_return 
	       (interp_statement false may_break block) in
	     assert (not !may_break);
	     let tblock = make_label "init" tblock in
	     let tblock =
	       List.fold_right
		 (fun (mut_id,id) bl ->
		    Let_ref(mut_id,Var(id),bl)) list_of_refs tblock in
	     printf "generating Why code for function %s@." f;
	     ((f, Def(f ^ "_impl", 
		      Fun(tparams,pre,tblock,post,None)))::why_code,
	      tspec :: why_spec,
	      prover_decl)
	   with Error (_, Cerror.Unsupported s) ->
	     lprintf "unsupported feature (%s); skipping function %s@." s f;
	     eprintf "unsupported feature (%s); skipping function %s@." s f;
	     (why_code,
	      tspec :: why_spec,
	      prover_decl)
	   end else begin
	     lprintf "assuming function %s@." f;
	     (why_code, tspec :: why_spec, prover_decl)
	   end
    ) 
      
let interp l =
  let s = interp_strong_invariants () in
  List.fold_left interp_located_tdecl (s,[]) l

let interp_functions (why,prover) =
  let (code,spec,prover) = 
    Hashtbl.fold interp_c_fun Cenv.c_functions ([],why,prover)
  in
  let code = 
    Hashtbl.fold
      (fun lab () acc ->
	 (lab,Exception("Goto_"^lab))::acc) labels_table code
  in
  (code,spec,prover)

  


