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

(*i $Id: cinterp.ml,v 1.101 2004-10-11 15:22:48 hubert Exp $ i*)


open Format
open Coptions
open Output
open Info
open Cast
open Clogic
open Creport

let rec global_var_for_type t =
  match t.ctype_node with
    | (CTenum _ | CTint _) -> "intP"
    | CTfloat _ -> "realP"
    | CTarray (ty,_) | CTpointer ty -> global_var_for_type ty ^ "P"
    | CTstruct _ -> "pointer"
    | _ -> assert false (* TODO *)

let global_var_for_array_type t =
  match t.ctype_node with
    | CTpointer ty | CTarray(ty,_) -> global_var_for_type ty
    | _ -> assert false

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

let float_of_int t = 
  { term_type = Cltyping.c_float; 
    term_loc = Loc.dummy;
    term_node = Tunop (Ufloat_of_int, t) }

let interp_rel t1 t2 r = 
  match t1.term_type.ctype_node, t2.term_type.ctype_node with
  | (CTenum _ | CTint _), (CTenum _ | CTint _) -> 
      t1, interp_int_rel r, t2
  | CTfloat _, CTfloat _ -> 
      t1, interp_real_rel r, t2
  | (CTenum _ | CTint _), CTfloat _ -> 
      float_of_int t1, interp_real_rel r, t2
  | CTfloat _, (CTenum _ | CTint _) -> 
      t1, interp_real_rel r, float_of_int t2
  | (CTarray _|CTpointer _), (CTarray _|CTpointer _) -> 
      t1, interp_pointer_rel r, t2
  | _ ->
      (match r with Eq -> t1,"eq",t2 | Neq -> t1,"neq",t2 | _ -> assert false)

let interp_term_bin_op ty op =
  match ty.ctype_node, op with
  | (CTenum _ | CTint _), Badd -> "add_int"
  | (CTenum _ | CTint _), Bsub -> "sub_int"
  | (CTenum _ | CTint _), Bmul -> "mul_int"
  | (CTenum _ | CTint _), Bdiv -> "div_int"
  | (CTenum _ | CTint _), Bmod -> "dmod_int"
  | CTfloat _, Badd -> "add_real"
  | CTfloat _, Bsub -> "sub_real"
  | CTfloat _, Bmul -> "mul_real"
  | CTfloat _, Bdiv -> "div_real"
  | (CTpointer _ | CTarray _), Badd -> "shift"
  | (CTpointer _ | CTarray _), Bsub -> "sub_pointer"
  | _ -> assert false

let interp_term_un_op ty op = match ty.ctype_node, op with
  | (CTenum _ | CTint _), Uminus -> "neg_int"
  | CTfloat _, Uminus -> "neg_real"
  | _ -> assert false

let interp_var label v =
  match label with 
    | None -> LVar v 
    | Some l -> LVarAtLabel(v,l)
  
let rec interp_term label old_label t =
  let f = interp_term label old_label in
  match t.term_node with
    | Tconstant (IntConstant c) ->
	LConst(Prim_int(Int64.to_int (Cconst.int t.term_loc c)))
    | Tconstant (FloatConstant c) ->
	LConst(Prim_float(float_of_string c))
    | Tvar id ->
	if id.var_is_assigned then
	  interp_var label id.var_unique_name
	else LVar id.var_unique_name
    | Told t ->	interp_term (Some old_label) old_label t
    | Tbinop (t1, op, t2) ->
	LApp(interp_term_bin_op t.term_type op,[f t1;f t2])
    | Tbase_addr t -> 
	LApp("base_addr",[f t])
    | Tblock_length t -> 
	LApp("block_length",[interp_var label "alloc"; f t])
    | Tat (t, l) -> 
	interp_term (Some l) old_label t
    | Tif (_, _, _) -> 
	unsupported "logic if-then-else"
    | Tarrget (t1, t2) -> 
	let te1 = f t1 and te2 = f t2 in
	let var = global_var_for_type t.term_type in
	LApp("acc",[interp_var label var;LApp("shift",[te1;te2])])
    | Tdot ({term_node = Tunop (Ustar, t)}, field) ->
	assert false
    | Tdot (t, field)
    | Tarrow (t, field) -> 
	let te = f t in
	let var = field.field_heap_var_name in
	LApp("acc",[interp_var label var;te])
    | Tunop (Ustar, t1) -> 
	let te1 = f t1 in
	let var = global_var_for_type t.term_type in
	LApp("acc",[interp_var label var;te1])
    | Tunop (Uamp, t1) -> 
	interp_term_address label old_label t1
    | Tunop (Uminus, t1) -> 
	LApp(interp_term_un_op t1.term_type Uminus, [f t1])
    | Tunop (Ufloat_of_int, t1) ->
	LApp("real_of_int", [f t1])
    | Tapp (g, l) -> 
	LApp(g.logic_name,
	     (HeapVarSet.fold (fun x acc -> (interp_var label x)::acc) 
		g.logic_args []) 
	     @ List.map f l)
    | Tnull -> 
	LVar "null"
    | Tresult -> 
	LVar "result" 
    | Tcast({ctype_node = CTpointer _}, 
	    {term_node = Tconstant (IntConstant "0")}) ->
	LVar "null"
    | Tcast (ty, t) -> 
	begin match ty.ctype_node, t.term_type.ctype_node with
	  | (CTenum _ | CTint _), (CTenum _ | CTint _)
	  | CTfloat _, CTfloat _ -> 
	      f t
	  | CTfloat _, (CTenum _ | CTint _) ->
	      LApp ("real_of_int", [f t])
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      f t
	  | _ -> 
	      unsupported "logic cast"
	end

and interp_term_address  label old_label e = match e.term_node with
  | Tvar v -> 
      begin match e.term_type.ctype_node with
	| CTstruct _ | CTunion _ -> LVar v.var_unique_name
	| _ -> unsupported "& operator"
      end
  | Tunop (Ustar, e1) -> 
      interp_term  label old_label e1
  | Tarrget (e1, e2) ->
      LApp("shift",[interp_term  label old_label e1; 
		    interp_term  label old_label e2])
  | Tdot ({term_node = Tunop (Ustar, e1)}, f) ->
      assert false
  | Tdot (e1, f)
  | Tarrow (e1, f) ->
      begin match e.term_type.ctype_node with
	| CTenum _ | CTint _ | CTfloat _ -> 
  	    interp_term  label old_label e1
	| CTstruct _ | CTunion _ | CTpointer _ | CTarray _ ->
	    let var = f.field_heap_var_name in
	    LApp("acc",[interp_var label var; interp_term label old_label e1])
	| _ -> unsupported "& operator on a field"
      end
  | Tcast (_, e1) ->
      interp_term_address  label old_label e1
  | _ -> 
      assert false (* not a left value *)

let rec interp_predicate label old_label p =
  let f = interp_predicate label old_label in
  let ft = interp_term label old_label in
  match p with
    | Ptrue -> 
	LTrue
    | Pexists (l, p) -> 
	List.fold_right
	  (fun (t,x) p -> LExists(x,([],Ceffect.interp_type t),p)) l (f p)
    | Pforall (l, p) ->
	List.fold_right
	  (fun (t,x) p -> LForall(x,([],Ceffect.interp_type t),p))
	  l (interp_predicate label old_label p)
    | Pif (t, p1, p2) -> 
	let t = ft t in
	let zero = LConst (Prim_int 0) in
	LAnd (make_impl (LPred ("neq_int", [t; zero])) (f p1),
	      make_impl (LPred ("eq_int",  [t; zero])) (f p2))
    | Pnot p -> 
	LNot (f p)
    | Pimplies (p1, p2) -> 
	make_impl (f p1) (f p2)
    | Piff (p1, p2) -> 
	make_equiv (f p1) (f p2)
    | Por (p1, p2) -> 
	make_or (f p1) (f p2)
    | Pand (p1, p2) -> 
	make_and (f p1) (f p2)
    | Prel (t1, op, t2) ->
	let t1,op,t2 = interp_rel t1 t2 op in
	LPred(op,[ft t1;ft t2])
    | Papp (v, tl) ->
	LPred(v.logic_name, 
	      (HeapVarSet.fold (fun x acc -> (interp_var label x)::acc) 
		 v.logic_args []) 
	      @ List.map ft tl)
    | Pfalse -> 
	LFalse
    | Pold p -> 
	interp_predicate (Some old_label) old_label p
    | Pat (p, l) -> 
	interp_predicate (Some l) old_label p
    | Pfresh (t) ->
	LPred("fresh",[interp_var (Some old_label) "alloc"; ft t])
    | Pvalid (t) ->
	LPred("valid",[interp_var label "alloc"; ft t])
    | Pvalid_index (t,a) ->
	LPred("valid_index",[interp_var label "alloc"; ft t;ft a])
    | Pvalid_range (t,a,b) ->
	LPred("valid_range",[interp_var label "alloc"; ft t;ft a;ft b])
    | Palloc_extends ->
	LPred("alloc_extends", [interp_var (Some old_label) "alloc";
				interp_var label "alloc"])

let interp_predicate_opt label old_label pred =
  match pred with
    | None -> LTrue
    | Some p -> interp_predicate label old_label p

open Cast

let interp_bin_op = function
  | Badd_int -> "add_int"
  | Bsub_int -> "sub_int"
  | Bmul_int -> "mul_int"
  | Bdiv_int -> "div_int"
  | Bmod_int -> "mod_int"
  | Blt_int -> "lt_int"
  | Bgt_int -> "gt_int"
  | Ble_int -> "le_int"
  | Bge_int -> "ge_int"
  | Beq_int -> "eq_int"
  | Bneq_int -> "neq_int" 
  | Badd_float -> "add_real"
  | Bsub_float -> "sub_real"
  | Bmul_float -> "mul_real"
  | Bdiv_float -> "div_real"
  | Blt_float -> "lt_real"
  | Bgt_float -> "gt_real"
  | Ble_float -> "le_real"
  | Bge_float -> "ge_real"
  | Beq_float -> "eq_real"
  | Bneq_float -> "neq_real" 
  | Blt_pointer -> "lt_pointer_"
  | Bgt_pointer -> "gt_pointer_"
  | Ble_pointer -> "le_pointer_"
  | Bge_pointer -> "ge_pointer_"
  | Beq_pointer -> "eq_pointer"
  | Bneq_pointer -> "neq_pointer" 
  | Badd_pointer_int -> "shift_"
  | Bsub_pointer -> "sub_pointer_"
  | Bbw_and -> "bw_and"
  | Bbw_xor -> "bw_xor"
  | Bbw_or -> "bw_or"
  | Bshift_left -> "lsl"
  | Bshift_right -> "lsr"
  (* should not happen *)
  | Badd | Bsub | Bmul | Bdiv | Bmod 
  | Blt | Bgt | Ble | Bge | Beq | Bneq | Band | Bor ->
      assert false

let int_one = Cte(Prim_int 1)
let int_minus_one = Cte(Prim_int (-1))
let float_one = Cte(Prim_float 1.0)

let interp_incr_op ty op = match ty.ctype_node, op with
  | (CTenum _ | CTint _), (Upostfix_inc | Uprefix_inc) -> "add_int", int_one
  | (CTenum _ | CTint _), (Upostfix_dec | Uprefix_dec) -> "sub_int", int_one
  | CTfloat _, (Upostfix_inc | Uprefix_inc) -> "add_real", float_one
  | CTfloat _, (Upostfix_dec | Uprefix_dec) -> "sub_real", float_one
  | (CTpointer _ | CTarray _), 
    (Upostfix_inc | Uprefix_inc) -> "shift_", int_one
  | (CTpointer _ | CTarray _), 
    (Upostfix_dec | Uprefix_dec) -> "shift_", int_minus_one
  | _ -> assert false

type interp_lvalue =
  | LocalRef of Info.var_info
  | HeapRef of string * Output.expr

let tempvar_count = ref 0;;
let reset_tmp_var () = tempvar_count := 0
let tmp_var () = incr tempvar_count; "caduceus_" ^ string_of_int !tempvar_count

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


let build_minimal_app e args =
  match args with
    | [] -> App(e,Void)
    | _ ->
	if List.for_all is_pure args then
	  List.fold_left (fun acc x -> App(acc,x)) e args
	else
	  build_complex_app e args

let rec interp_expr e =
  match e.texpr_node with
    | TEconstant (IntConstant c) -> 
	Cte (Prim_int (Int64.to_int (Cconst.int e.texpr_loc c)))
    | TEconstant (FloatConstant c) ->
	Cte(Prim_float(float_of_string c))
    | TEvar(v) -> 
	let n = v.var_unique_name in
	if v.var_is_assigned then Deref n else Var n
    (* a ``boolean'' expression is [if e then 1 else 0] *)
    | TEbinary(_,(Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		 |Blt_float | Bgt_float | Ble_float | Bge_float 
		 |Beq_float | Bneq_float 
		 |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		 |Beq_pointer | Bneq_pointer 
		 |Blt | Bgt | Ble | Bge | Beq | Bneq | Band | Bor),_) 
    | TEunary (Unot, _) ->
	If(interp_boolean_expr e, Cte(Prim_int(1)), Cte(Prim_int(0)))
    | TEbinary(e1,op,e2) ->
	build_minimal_app (Var (interp_bin_op op)) 
	  [interp_expr e1;interp_expr e2]
    | TEarrget(e1,e2) ->
	let te1 = interp_expr e1 and te2 = interp_expr e2 in
	let var = global_var_for_type e.texpr_type in
	App(App(Var("acc_"),Var(var)),
	    build_complex_app (Var "shift_") [te1; te2])
    | TEassign (e1,e2) ->
	begin
	  match interp_lvalue e1 with
	    | LocalRef(v) ->
		(* v := e2; !v *)
		let n = v.var_unique_name in
		append (Assign(n,interp_expr e2)) (Deref n)
	    | HeapRef(var,e1) ->
		(* let tmp1 = e1 in 
		   let tmp2 = e2 in upd var tmp1 tmp2; tmp2 *)
		let tmp1 = tmp_var () in
		let tmp2 = tmp_var () in
		Let(tmp1, e1,
		    Let(tmp2, interp_expr e2,
			append (build_complex_app (Var "upd_")
				  [Var var; Var tmp1; Var tmp2])
			  (Var tmp2)))
	end 
    | TEincr(op,e) -> 
	interp_incr_expr op e
    | TEassign_op(e1,op,e2) ->
	begin match interp_lvalue e1 with
	  (* v := op !v e2; !v *)
	  | LocalRef(v) ->
	      let n = v.var_unique_name in
	      append
	        (Assign(n,
			make_app (interp_bin_op op) 
			  [Deref n; interp_expr e2]))
	        (Deref n)
	  | HeapRef(var,e1) -> 
	      (* let tmp1 = e1 in
		 let tmp2 = op (acc var e1) e2 in
		 upd var tmp1 tmp2; tmp2 *)
	      let tmp1 = tmp_var () in
	      let tmp2 = tmp_var () in
	      Let(tmp1, e1,
		  Let(tmp2, 
		      make_app (interp_bin_op op)
			[make_app "acc_" [Var var; Var tmp1]; interp_expr e2],
		      append
			(build_complex_app (Var "upd_") 
			   [Var var; Var tmp1; Var tmp2])
			(Var tmp2)))
	end 
    | TEseq(e1,e2) ->
	append (interp_statement_expr e1) (interp_expr e2)
    | TEnop -> 
	Void
    | TEcond(e1,e2,e3) ->
	If(interp_boolean_expr e1, interp_expr e2, interp_expr e3)
    | TEstring_literal s -> 
	unsupported "string literal"
    | TEdot ({texpr_node = TEunary (Ustar, e)}, s) ->
	assert false
    | TEdot (e,s)
    | TEarrow (e,s) ->
	let te = interp_expr e in
	let var = s.field_heap_var_name in
	Output.make_app "acc_" [Var(var);te]
    | TEunary(Ustar,e1) -> 
	let te1 = interp_expr e1 in
	let var = global_var_for_type e.texpr_type in
	make_app "acc_" [Var var;te1]
    | TEunary (Uplus, e) ->
	interp_expr e
    | TEunary(Uminus, e) -> 
	begin match e.texpr_type.ctype_node with
	  | CTenum _ | CTint _ -> make_app "neg_int" [interp_expr e]
	  | CTfloat _ -> make_app "neg_real" [interp_expr e]
	  | _ -> assert false
	end
    | TEunary (Uint_of_float, e) ->
	make_app "int_of_real" [interp_expr e]
    | TEunary (Ufloat_of_int, e) ->
	make_app "real_of_int" [interp_expr e]
    | TEunary (Utilde, e) ->
	make_app "bw_compl" [interp_expr e]
    | TEunary (Uamp, e) ->
	interp_address e
    | TEcall(e,args) -> 
	begin
	  match e.texpr_node with
	    | TEvar v ->
		let targs = match args with
		  | [] -> [Output.Var "void"]
		  | _ -> List.map interp_expr args
		in
		build_complex_app (Var (v.var_unique_name ^ "_parameter")) 
		  targs
	    | _ -> 
		unsupported "call of a non-variable function"
	end
    | TEcast({ctype_node = CTpointer _}, 
	     {texpr_node = TEconstant (IntConstant "0")}) ->
	Var "null"
    | TEcast(t,e) -> 
	begin match t.ctype_node, e.texpr_type.ctype_node with
	  | (CTenum _ | CTint _), (CTenum _ | CTint _)
	  | CTfloat _, CTfloat _ -> 
	      interp_expr e
	  | CTfloat _, (CTenum _ | CTint _) ->
	      make_app "real_of_int" [interp_expr e]
	  | (CTenum _ | CTint _), CTfloat _ ->
	      make_app "int_of_real" [interp_expr e]
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      interp_expr e
	  | _ -> 
	      unsupported "cast"
	end
    | TEsizeof(t) -> 
	Cte (Prim_int (Ctyping.sizeof t))

and interp_boolean_expr e =
  match e.texpr_node with
    | TEbinary(e1, (Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		   |Blt_float | Bgt_float | Ble_float | Bge_float 
		   |Beq_float | Bneq_float 
		   |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		   |Beq_pointer | Bneq_pointer 
		   |Blt | Bgt | Ble | Bge | Beq | Bneq as op), e2) ->
	build_minimal_app (Var (interp_bin_op op)) 
	  [interp_expr e1; interp_expr e2]
    | TEbinary (e1, Band, e2) ->
	And(interp_boolean_expr e1, interp_boolean_expr e2)
    | TEbinary (e1, Bor, e2) ->
	Or(interp_boolean_expr e1, interp_boolean_expr e2)
    | TEunary (Unot, e) ->
	Not(interp_boolean_expr e)
    (* otherwise e <> 0 *)
    | _ -> 
	let cmp,zero = match e.texpr_type.ctype_node with
	  | CTenum _ | CTint _ -> "neq_int", Cte (Prim_int 0)
	  | CTfloat _ -> "neq_real", Cte (Prim_float 0.0)
	  | CTarray _ | CTpointer _ -> "neq_pointer", Var "null"
	  | _ -> assert false
	in
	build_complex_app (Var cmp) [interp_expr e; zero]

and interp_incr_expr op e =
  let top,one = interp_incr_op e.texpr_type op in
  match interp_lvalue e with
    | LocalRef v ->
	begin
	  match op with
	    | Upostfix_dec | Upostfix_inc ->
		(* let tmp = !v in v:= op tmp 1; tmp *)
		Let("caduceus",Deref(v.var_unique_name),
		    append 
		      (Assign(v.var_unique_name,
			      make_app top [Var "caduceus";one]))
		      (Var "caduceus"))
	    | Uprefix_dec | Uprefix_inc ->
		(* v := op !v 1; !v *)
		let n = v.var_unique_name in
		append 
		  (Assign(n,
			  App(App(Var top, Deref n), one)))
		  (Deref n)
	end
    | HeapRef(var,e') ->
	begin
	  match op with
	    | Upostfix_dec | Upostfix_inc ->
		(* let tmp1 = e' in
		   let tmp2 = acc var tmp1 in
		   upd var tmp1 (tmp2+1); tmp2 *)		
		Let("caduceus1",e',
		    Let("caduceus2",
			(make_app "acc_" [Var var;Var "caduceus1"]),
			append
			  (make_app "upd_" 
			     [Var var;Var "caduceus1";
			      make_app top [one;Var "caduceus2"]])
			  (Var "caduceus2")))
	    | Uprefix_dec | Uprefix_inc ->
		(* let tmp1 = e' in
		   let tmp2 = (acc var tmp1)+1 in
		   upd var tmp1 tmp2; tmp2 *)
		Let("caduceus1",e',
		    Let("caduceus2",
			make_app top
			  [make_app "acc_" [Var var;Var "caduceus1"];one],
			append
			  (make_app "upd_" 
			     [Var var;Var "caduceus1";Var "caduceus2"])
			  (Var "caduceus2")))
	end		      

and interp_lvalue e =
  match e.texpr_node with
    | TEvar v -> LocalRef(v)
    | TEunary(Ustar,e1) ->
	let var = global_var_for_type e.texpr_type in
	HeapRef(var,interp_expr e1)
    | TEarrget(e1,e2) ->
	let te1 = interp_expr e1 and te2 = interp_expr e2 in
	let var = global_var_for_type e.texpr_type in
	HeapRef(var,build_complex_app (Var "shift_")
		  [interp_expr e1; interp_expr e2])
    | TEdot ({texpr_node = TEunary (Ustar, e1)}, f) ->
	assert false
    | TEdot (e1,f)
    | TEarrow (e1,f) ->
	HeapRef(f.field_heap_var_name, interp_expr e1)
    | _ -> 
	assert false (* wrong typing of lvalue ??? *)

and interp_address e = match e.texpr_node with
  | TEvar v -> 
      begin match e.texpr_type.ctype_node with
	| CTstruct _ | CTunion _ -> Deref v.var_unique_name
	| _ -> unsupported "& operator"
      end
  | TEunary (Ustar, e1) ->
      interp_expr e1
  | TEarrget (e1, e2) ->
      build_complex_app (Var "shift_") [interp_expr e1; interp_expr e2]
  | TEdot ({texpr_node = TEunary (Ustar, e1)}, f) ->
      assert false
  | TEdot (e1, f)
  | TEarrow (e1, f) ->
      begin match e.texpr_type.ctype_node with
	| CTenum _ | CTint _ | CTfloat _ -> 
  	    interp_expr e1
	| CTstruct _ | CTunion _ | CTpointer _ | CTarray _ ->
            build_complex_app (Var "acc_") 
	    [Var f.field_heap_var_name; interp_expr e1]
	| _ -> unsupported "& operator on a field"
      end
  | TEcast (_, e1) ->
      interp_address e1
  | _ -> 
      assert false (* not a left value *)

and interp_statement_expr e =
  match e.texpr_node with
    | TEseq(e1,e2) ->
	append (interp_statement_expr e1) (interp_statement_expr e2)
    | TEnop -> 
	Void
    | TEassign(l,e) ->
	begin
	  match interp_lvalue l with
	    | LocalRef(v) ->
		Assign(v.var_unique_name,interp_expr e)
	    | HeapRef(var,e1) ->
		(* upd var e1 e *)
		(build_complex_app (Var "upd_")
		   [Var var;e1; interp_expr e])
	end 
    | TEincr(op,e) ->
	let top,one = interp_incr_op e.texpr_type op in
	begin
	  match interp_lvalue e with
	    | LocalRef v ->
		Assign(v.var_unique_name,
		       make_app top [Deref(v.var_unique_name); one])
	    | HeapRef(var,e1) -> 
		(* let tmp1 = e1 in
		   let tmp2 = acc var tmp1 in 
		   upd var tmp1 (op tmp2 1) *)
		Let("caduceus1",e1,
		    Let("caduceus2",
			make_app "acc_" [Var var; Var "caduceus1"],
			make_app "upd_"
			  [Var var; Var "caduceus1"; 
			   make_app top [Var "caduceus2"; one]]))
	end
    | TEcall (e1,args) -> 
	begin
	  match e1.texpr_node with
	    | TEvar v ->
		let targs = match args with
		  | [] -> [Output.Var "void"]
		  | _ -> List.map interp_expr args
		in
		let app = 
		  build_complex_app (Var (v.var_unique_name ^ "_parameter")) 
		    targs
		in
		if e.texpr_type.ctype_node = CTvoid then
		  app
		else
		  Let (tmp_var (), app, Void)
	    | _ -> 
		unsupported "call of a non-variable function"
	end
    | TEassign_op (l, op, e) -> 
	begin
	  match interp_lvalue l with
	    | LocalRef(v) ->
		let n = v.var_unique_name in
		Assign(n,
		       make_app (interp_bin_op op) 
			 [Deref n; interp_expr e])
	    | HeapRef(var,e1) -> 
		(* let tmp1 = e1 in
		   let tmp2 = acc var e1
		   upd var tmp1 (op tmp2 e) *)
		Let("caduceus1",e1,
		    Let("caduceus2",make_app "acc_" [Var var;Var "caduceus1"],
			make_app "upd_"
			  [Var var; Var "caduceus1"; 
			   make_app (interp_bin_op op) 
			     [Var "caduceus2"; interp_expr e]]))
	end 
    | TEsizeof _ 
    | TEcast (_, _)
    | TEcond (_, _, _)
    | TEbinary (_, _, _)
    | TEunary (_, _)
    | TEarrget (_, _)
    | TEarrow (_, _)
    | TEdot (_, _)
    | TEvar _
    | TEstring_literal _
    | TEconstant _ -> 
	unsupported "statement expression"

module StringMap = Map.Make(String)

type mem_or_ref = Reference of bool | Memory of Output.term list

let collect_locations before acc loc =
  let var,iloc =
    match loc with
      | Lterm t -> 
	  begin
	    match t.term_node with
	      | Tdot({term_node = Tunop (Clogic.Ustar, e)}, f) ->
		  assert false
	      | Tdot(e,f)
	      | Tarrow(e,f) ->
		  let loc = 
		    LApp("pointer_loc",[interp_term (Some before) before e]) 
		  in
		  f.field_heap_var_name, Some loc
	      | Tarrget(e1,e2) -> 
		  let var = global_var_for_array_type e1.term_type in
		  let loc = 
		    LApp("pointer_loc",
			 [LApp("shift",
			       [interp_term (Some before) before e1;
				interp_term (Some before) before e2])]) 
		  in
		  var, Some loc
	      | Tunop (Clogic.Ustar, e1) -> 
		  let var = global_var_for_array_type e1.term_type in
		  let loc = 
		    LApp("pointer_loc", [interp_term (Some before) before e1])
		  in
		  var, Some loc
	      | Tvar v ->
		  v.var_unique_name, None
	      | _ ->
		  assert false
	  end
    | Lstar t -> 
	let var = global_var_for_array_type t.term_type in
	let loc = 
	  LApp("all_loc",[interp_term (Some before) before t])
	in
	var, Some loc
    | Lrange(t1,t2,t3) -> 
	let var = global_var_for_array_type t1.term_type in
	let loc = 
	  LApp("range_loc",
	       [interp_term (Some before) before t1;
		interp_term (Some before) before t2;
		interp_term (Some before) before t3;])
	in
	var, Some loc
  in
  try
    let p = StringMap.find var acc in
    (match p, iloc with
       | Reference _, None -> StringMap.add var (Reference true) acc
       | Memory l, Some iloc -> StringMap.add var (Memory (iloc::l)) acc
       | _ -> assert false)
  with Not_found -> 
    (match iloc with
       | None -> StringMap.add var (Reference true) acc
       | Some l -> StringMap.add var (Memory [l]) acc)

let rec make_union_loc = function
  | [] -> LVar "nothing_loc"
  | [l] -> l
  | l::r -> LApp("union_loc",[l;make_union_loc r])

let interp_assigns before assigns = function
  | Some locl ->
      let m = 
	HeapVarSet.fold
	  (fun v m -> 
	     let t = 
	       if Ceffect.is_memory_var v then Memory []  else Reference false
	     in
	     StringMap.add v t m)
	  assigns StringMap.empty
      in
      let l = 
	List.fold_left (collect_locations before) m locl
      in
      StringMap.fold
	(fun v p acc -> match p with
	   | Memory p ->
	       make_and acc
		 (LPred("assigns",
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
       if not (HeapVarSet.is_empty (HeapVarSet.inter e hvs)) then
	 make_and (weak_invariant id p) acc 
       else acc)
    Ceffect.weak_invariants LTrue

let interp_spec effect_reads effect_assigns s =
  let tpre = 
    make_and
      (interp_predicate_opt None "" s.requires)
      (weak_invariants_for effect_reads)
  and tpost = 
    make_and
      (interp_predicate_opt None "" s.ensures)
      (make_and 
	 (interp_assigns "" effect_assigns s.assigns)
	 (weak_invariants_for effect_assigns))
  in 
  (tpre,tpost)

let alloc_on_stack loc v t =
  let form = 
    Cltyping.make_and 
      (snd (Cltyping.separation loc v t))
      (Cltyping.make_and 
	 (Cltyping.valid_for_type ~fresh:true loc v t) Palloc_extends)
  in
  BlackBox(Annot_type(LTrue,base_type "pointer",["alloc"],["alloc"],
		      interp_predicate None "" form,None))
      
let interp_decl d acc = 
  match d.node with 
    | Tdecl(ctype,v,init) -> 
	lprintf 
	  "translating local declaration of %s@." v.var_unique_name;
	let tinit =
	  match init with 
	    | Inothing ->
		begin match ctype.ctype_node with
		  | CTenum _ | CTint _ -> App(Var("any_int"),Var("void"))
		  | CTfloat _ -> App(Var("any_real"),Var("void"))
		  | CTfun _ -> assert false
		  | CTarray _ | CTpointer _ | CTstruct _ -> 
                      let t = { term_node = Tresult; 
				term_loc = d.loc;
				term_type = ctype } in
                      alloc_on_stack d.loc v t
		  | _ -> assert false
		end
	    | Iexpr e -> interp_expr e		
	    | Ilist _ -> unsupported "structured initializer for local var"
	in
	if v.var_is_assigned then
	  Let_ref(v.var_unique_name,tinit,acc)
	else
	  Let(v.var_unique_name,tinit,acc)
    | Ttypedef _
    | Ttypedecl { ctype_node = CTstruct _ | CTunion _ } -> 
	acc
    | Ttypedecl { ctype_node = CTenum _ } -> 
	unsupported "local enum type"
    | Ttypedecl _
    | Tfunspec _
    | Taxiom _
    | Tinvariant _
    | Tlogic _
    | Tfundef _ ->
	assert false


let interp_invariant label effects annot =
  let inv = match annot.invariant with
    | None -> LTrue
    | Some inv -> interp_predicate None "init" inv
  in
  let inv = make_and (interp_assigns label effects annot.loop_assigns) inv in
  let var = match annot.variant with
    | None -> LConst (Prim_int 0), None
    | Some (var,r) -> interp_term None "init" var, r
  in
  (inv, var)

let new_label = let r = ref 0 in fun () -> incr r; "label_" ^ string_of_int !r

let try_with_void ex e = Try (e, ex, None, Void)  

let break b e = if b then try_with_void "Break" e else e

let continue b e = if b then try_with_void "Continue" e else e    

let return_exn ty = match ty.ctype_node with
  | CTenum _ | CTint _ -> "Return_int"
  | CTfloat _ -> "Return_real"
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
  | s::_ -> warning s.st_loc "unreachable statement"

(* Interpretation of switch *)

module IntMap = Map.Make(struct type t = int64 let compare = compare end)

let rec st_cases used_cases i =
  match i.st_node with 
    | TScase ( e ,i') ->
	let n =  Cltyping.eval_const_expr e in
	if IntMap.mem n used_cases 
	then
	  error i.st_loc ("duplicate case")
	else
	  let (used_cases' , l,i) = st_cases (IntMap.add n e used_cases) i' in
	  (used_cases', (IntMap.add n e l),i)
    | i' -> (used_cases , IntMap.empty , i)

let rec st_instr l =
  match l with
    | [] -> l,[]
    | i ::l' -> 
	match i .st_node with
	  | TSdefault _ -> l,[]
	  | TScase(_,_) -> l,[]
	  | _ -> let (l,instr) = st_instr l' in
	    (l,i::instr)

      
    

let rec st_case_list used_cases l =
  match l with 
    | [] -> (used_cases, [] )
    | i::l ->
	match i.st_node with 
	  | TSdefault s ->
	      begin
		match s.st_node with
		  | TScase _ -> unsupported "case following default"
		  | _ ->		 
		      let (l,instr) = st_instr l in
		      let(used_cases'', l'') = (st_case_list used_cases l) in
		      (used_cases'',(IntMap.empty,s::instr)::l'')
	      end
	  | TScase(e,i) -> 
	      let n = Cltyping.eval_const_expr e in 
	      if IntMap.mem n used_cases 
	      then
		error i.st_loc ("duplicate case")
	      else
		let (used_cases', l', i') = st_cases (used_cases) i in 
		let (l,instr) = st_instr l in
		let (used_cases'', l'') = 
		  st_case_list (IntMap.add n e used_cases') l in
		(used_cases'',((IntMap.add n e l'),i'::instr)::l'')
	  | _ ->  
	      let (used_cases', l') = st_case_list used_cases l in
	      match l' with
		| [] -> 
		    error i.st_loc 
		      ("unreachable statement at beginning of switch")
		| (lc,i')::l -> (used_cases',(lc,i'@[i])::l)
		



let st_switch i =
  match i.st_node with 
    | TSblock (_,l) -> st_case_list IntMap.empty l
    | _ -> st_case_list IntMap.empty [i]

let make_switch_condition tmp l = 
  if IntMap.is_empty l 
  then assert false
  else
    let a = 
      IntMap.fold 
	(fun x n test -> 
	   make_or_expr (App(App (Var "eq_int",Var tmp), (interp_expr n))) test) 
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
	 make_and_expr (App(App (Var "neq_int",Var tmp),(interp_expr e))) test)
      fl
      (Cte (Prim_bool true))
      (*App(App (Var "neq_int",Var tmp), (interp_expr e))*)
  in
  cond,fl

(* [ab] indicates if returns are abrupt *)

let rec interp_statement ab may_break stat = match stat.st_node with
  | TSnop -> 
      Void
  | TSexpr e ->
      interp_statement_expr e
  | TSreturn eopt ->
      if ab then match eopt with
	| None -> 
	    abrupt_return := Some "Return";
	    Raise ("Return", None)
	| Some e -> 
	    let r = return_exn e.texpr_type in 
	    abrupt_return := Some r;
	    Raise (r, Some (interp_expr e))
      else begin match eopt with
	| None -> Void
	| Some e -> interp_expr e
      end
  | TSif(e,s1,s2) -> 
      If(interp_boolean_expr e,
	 interp_statement ab may_break s1, interp_statement ab may_break s2)
  | TSfor(annot,e1,e2,e3,body) ->
      let label = new_label () in
      let ef = 
	HeapVarSet.union 
	  (HeapVarSet.union (Ceffect.expr e1).Ceffect.assigns
	     (Ceffect.expr e2).Ceffect.assigns)
	  (HeapVarSet.union (Ceffect.expr e3).Ceffect.assigns 
	     (Ceffect.statement body).Ceffect.assigns)
      in
      let (inv,dec) = interp_invariant label ef annot in
      append
	(Output.Label label)
	(append
	   (interp_statement_expr e1)
	   (break body.st_break 
	      (make_while (interp_boolean_expr e2) inv dec 
		 (continue body.st_continue
		    (append 
		       (interp_statement true (ref false) body) 
		       (interp_statement_expr e3))))))
  | TSwhile(annot,e,s) -> 
      let label = new_label () in
      let ef = 
	HeapVarSet.union (Ceffect.expr e).Ceffect.assigns
	  (Ceffect.statement s).Ceffect.assigns 
      in
      let (inv,dec) = interp_invariant label ef annot in
      append (Output.Label label)
	(break s.st_break
	   (make_while (interp_boolean_expr e) inv dec 
	      (continue s.st_continue (interp_statement true (ref false) s))))
  | TSdowhile(annot,s,e) -> 
      let label = new_label () in
      let ef = 
	HeapVarSet.union (Ceffect.expr e).Ceffect.assigns
	  (Ceffect.statement s).Ceffect.assigns 
      in
      let (inv,dec) = interp_invariant label ef annot in
      append (Output.Label label)
	(break true
	   (make_while (Cte (Prim_bool true)) inv dec
	      (continue s.st_continue
		 (append (interp_statement true (ref false) s)
		    (If (Not (interp_boolean_expr e), 
			 Raise ("Break", None), Void))))))
  | TSblock(b) -> 
      interp_block ab may_break b 
  | TSbreak -> 
      may_break := true;
      Raise ("Break", None)
  | TScontinue -> 
      Raise ("Continue", None)
  | TSlabel(lab,s) -> 
      append (Output.Label lab) (interp_statement ab may_break s)
  | TSswitch(e,s) -> 
      let (used_cases,l) = st_switch s in
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
  | TScase(e,s) -> 
      unsupported "case"
  | TSdefault(s) -> 
      unsupported "default"
  | TSgoto(lab) -> 
      unsupported "goto"
  | TSassert(pred) -> 
      Output.Assert(interp_predicate None "init" pred)
  | TSlogic_label(l) -> 
      Output.Label l
  | TSspec (spec,s) ->
      let eff = Ceffect.statement s in
      let pre,post = interp_spec eff.Ceffect.reads eff.Ceffect.assigns spec in
      Triple(pre,interp_statement ab may_break s,post,None)

and interp_block ab may_break (decls,stats) =
  let rec block = function
    | [] -> 
	Void
    | [s] ->
	interp_statement ab may_break s
    | { st_node = TSnop } :: bl ->
	block bl
    | { st_node = TSif (e, s1, s2) } as s :: bl ->
	begin match s1.st_term, s2.st_term with
	  | true, true ->
	      append (interp_statement true may_break s) (block bl)
	  | false, false ->
	      unreachable_block bl;
	      interp_statement ab may_break s
	  | true, false ->
	      If (interp_boolean_expr e, 
		  block (s1 :: bl), interp_statement ab may_break s2)
	  | false, true ->
	      If (interp_boolean_expr e,
		  interp_statement ab may_break s1, block (s2 :: bl))
	end
    | s :: bl ->
	if not s.st_term then unreachable_block bl;
	append (interp_statement true may_break s) (block bl)
  in
  List.fold_right interp_decl decls (block stats)

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
	if a.st_term
	then
	  let (instr,isfinal) = interp_case ab may_break i in
	  ((interp_statement ab may_break a)::instr),isfinal
	else
	  begin
	    unreachable_block i;
	    (if a.st_node=TSbreak 
	     then [] 
	     else [interp_statement ab may_break a]),true
	  end
	  
	  

let interp_predicate_args id args =
  let args =
    List.fold_right
      (fun (id,t) args -> (id,([],Ceffect.interp_type t))::args)
      args []
  in
  HeapVarSet.fold
    (fun arg t -> (arg,Ceffect.heap_var_type arg)::t)
    id.logic_args args

let cinterp_logic_symbol id ls =
  match ls with
    | Predicate_reads(args,locs) -> 
	let args = interp_predicate_args id args in
	let ty = 
	  List.fold_right (fun (x,t) ty -> Prod_type (x, Base_type t, ty)) 
	    args (Base_type ([],"prop"))
	in
	Logic(false, id.logic_name, ty)
    | Predicate_def(args,p) -> 
	let a = interp_predicate None "" p in
	let args = interp_predicate_args id args in
	Predicate(false,id.logic_name,args,a)
    | Function(args,ret,_) ->
	let local_type =
	  List.fold_right
	    (fun (id,ty) t -> 
	       Prod_type(id,base_type (Ceffect.interp_type ty),t))
	    args (base_type (Ceffect.interp_type ret))
	in
	let final_type =
	  HeapVarSet.fold
	    (fun arg t -> 
	       let ty = Ceffect.heap_var_type arg in 
	       Prod_type("",Base_type ty,t))
	    id.logic_args local_type
	in
	Logic(false,id.logic_name,final_type)
	  
let interp_axiom p =
  let a = interp_predicate None "" p
  and e = Ceffect.predicate p in
  HeapVarSet.fold
    (fun arg t -> LForall(arg,Ceffect.heap_var_type arg,t))
    e a

let interp_effects e =
  HeapVarSet.fold (fun var acc -> var::acc) e []

(*
let interp_param pre (t,id) =
  (* TODO : tester si param is assigned *)
  let tt = Ceffect.interp_type t in
  (if tt="pointer" then make_and (LNot(LPred("fresh",[LVar id]))) pre
			 else pre),
  (id,base_type tt)
*)

let interp_fun_params params =
  if params=[]
  then ["tt",unit_type]
  else List.fold_right 
    (fun (t,id) tpl ->
       let tt = Ceffect.interp_type t in
       (id.var_unique_name,base_type tt)::tpl)
 params []


let interp_function_spec id sp ty pl =
  let tpl = interp_fun_params pl in
  let pre,post = interp_spec id.function_reads id.function_writes sp in
  let r = HeapVarSet.elements id.function_reads in
  let w = HeapVarSet.elements id.function_writes in
  let annot_type = 
    Annot_type
      (pre, Base_type ([], Ceffect.interp_type ty), r, w, post, None)
  in
  let ty = 
    List.fold_right 
      (fun (x,ct) ty -> Prod_type (x, ct, ty))
      tpl 
      annot_type
  in
  tpl,pre,post, Param (false, id.var_unique_name ^ "_parameter", ty)

let interp_type loc ctype = match ctype.ctype_node with
  | CTenum (e, _) ->
      begin match Cenv.tag_type_definition e with
	| Cenv.Defined (CTenum (_, Decl el)) -> 
	    if List.exists (fun (_,i) -> i <> None) el then
	      warning loc ("ignoring initializer(s) for enum " ^ e);
	    List.map (fun (x,_) -> Param (false,x,Base_type ([], "int"))) el
	| _ -> assert false
      end
  | _ -> 
      []

let interp_located_tdecl ((why_code,why_spec,prover_decl) as why) decl =
  match decl.node with
  | Tlogic(id,ltype) -> 
      lprintf "translating logic declaration of %s@." id.logic_name;
      (why_code, cinterp_logic_symbol id ltype::why_spec,
       prover_decl)
  | Taxiom(id,p) -> 
      lprintf "translating axiom declaration %s@." id;      
      let a = interp_axiom p in
      (why_code, Axiom(id,a)::why_spec, prover_decl)
  | Tinvariant(id,p) -> 
      lprintf "translating invariant declaration %s@." id;      
      why
  | Ttypedecl ({ ctype_node = CTenum _ } as ctype)
  | Ttypedef (ctype,_) -> 
      let dl = interp_type decl.loc ctype in 
      why_code, dl @ why_spec, prover_decl
  | Ttypedecl { ctype_node = CTstruct _ | CTunion _ } -> 
      why
  | Ttypedecl _ ->
      assert false
  | Tdecl(ctype,v,init) -> 
      lprintf "translating global declaration of %s@." v.var_unique_name;
      begin match init with 
	| Inothing ->
	    ()
	| _ -> 
	    warning decl.loc ("ignoring initializer for " ^ v.var_unique_name);
      end;
      why
  | Tfunspec(spec,ctype,id,params) -> 
      let _,_,_,spec = interp_function_spec id spec ctype params in
      (why_code, spec :: why_spec,
       prover_decl)
  | Tfundef(spec,ctype,id,params,block) ->      
      reset_tmp_var ();
      let tparams,pre,post,tspec = 
	interp_function_spec id spec ctype params in
      let f = id.var_unique_name in
      lprintf "translating function %s@." f;
      begin try
	abrupt_return := None;
	let may_break = ref false in
	let list_of_refs =
	  List.fold_right
	    (fun (ty,id) bl ->
	       if id.var_is_assigned
	       then 
		 let n = id.var_unique_name in
		 id.var_unique_name <- "mutable_" ^ n; 
		 [id.var_unique_name,n]
	       else bl) params [] in
	let tblock = catch_return (interp_statement false may_break block) in
	assert (not !may_break);
	let tblock =
	  List.fold_right
	    (fun (mut_id,id) bl ->
	       Let_ref(mut_id,Var(id),bl)) list_of_refs tblock in
	let tblock = make_label "init" tblock in
	printf "generating Why code for function %s@." f;
	((Def(f ^ "_impl", Fun(tparams,pre,tblock,post,None)))::why_code,
	 tspec :: why_spec,
	 prover_decl)
      with Error (_, Cerror.Unsupported s) ->
	lprintf "unsupported feature (%s); skipping function %s@." s f;
	eprintf "unsupported feature (%s); skipping function %s@." s f;
	(why_code,
	 tspec :: why_spec,
	 prover_decl)
      end

let interp l =
  List.fold_left interp_located_tdecl ([],[],[]) l

