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

(*i $Id: cinterp.ml,v 1.119 2004-12-06 14:16:02 filliatr Exp $ i*)


open Format
open Coptions
open Output
open Info
open Cast
open Clogic
open Creport
open Ctypes

let rec global_var_for_type t =
  match t.ctype_node with
    | (Tenum _ | Tint _) -> "intP"
    | Tfloat _ -> "realP"
    | Tarray (ty,_) | Tpointer ty -> global_var_for_type ty ^ "P"
    | Tstruct _ -> "pointer"
    | _ -> assert false (* TODO *)

let global_var_for_array_type t =
  match t.ctype_node with
    | Tpointer ty | Tarray(ty,_) -> global_var_for_type ty
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

open Ctypes

let float_of_int (t : nctype nterm) = 
  { nterm_type = c_float; 
    nterm_loc = Loc.dummy;
    nterm_node = NTunop (Ufloat_of_int, t) }

let interp_rel (t1 : nctype nterm) t2 r = 
  match t1.nterm_type.ctype_node, t2.nterm_type.ctype_node with
  | (Tenum _ | Tint _), (Tenum _ | Tint _) -> 
      t1, interp_int_rel r, t2
  | Tfloat _, Tfloat _ -> 
      t1, interp_real_rel r, t2
  | (Tenum _ | Tint _), Tfloat _ -> 
      float_of_int t1, interp_real_rel r, t2
  | Tfloat _, (Tenum _ | Tint _) -> 
      t1, interp_real_rel r, float_of_int t2
  | (Tarray _|Tpointer _), (Tarray _|Tpointer _) -> 
      t1, interp_pointer_rel r, t2
  | _ ->
      (match r with Eq -> t1,"eq",t2 | Neq -> t1,"neq",t2 | _ -> assert false)

let interp_term_bin_op ty op =
  match ty.ctype_node, op with
  | (Tenum _ | Tint _), Badd -> "add_int"
  | (Tenum _ | Tint _), Bsub -> "sub_int"
  | (Tenum _ | Tint _), Bmul -> "mul_int"
  | (Tenum _ | Tint _), Bdiv -> "div_int"
  | (Tenum _ | Tint _), Bmod -> "dmod_int"
  | Tfloat _, Badd -> "add_real"
  | Tfloat _, Bsub -> "sub_real"
  | Tfloat _, Bmul -> "mul_real"
  | Tfloat _, Bdiv -> "div_real"
  | (Tpointer _ | Tarray _), Badd -> "shift"
  | (Tpointer _ | Tarray _), Bsub -> "sub_pointer"
  | _ -> assert false

let interp_term_un_op ty op = match ty.ctype_node, op with
  | (Tenum _ | Tint _), Uminus -> "neg_int"
  | Tfloat _, Uminus -> "neg_real"
  | _ -> assert false

let interp_var label v =
  match label with 
    | None -> LVar v 
    | Some l -> LVarAtLabel(v,l)
  
let rec interp_term label old_label t =
  let f = interp_term label old_label in
  match t.nterm_node with
    | NTconstant (IntConstant c) ->
	LConst(Prim_int (Cconst.int t.nterm_loc c))
    | NTconstant (FloatConstant c) ->
	LConst(Prim_float c)
    | NTvar id ->
	let n = id.var_unique_name in
	if id.var_is_referenced then
	  begin match t.nterm_type.ctype_node with
	    | Tstruct _ | Tunion _ -> 
		if id.var_is_assigned && not id.var_is_a_formal_param then
		  interp_var label n
		else LVar n 		  
	    | _ -> 
		let var = global_var_for_type t.nterm_type in
		LApp("acc",[LVar var; LVar n])
	  end
	else 
	  if id.var_is_assigned && not id.var_is_a_formal_param then
	    interp_var label n
	  else LVar n
    | NTold t ->	interp_term (Some old_label) old_label t
    | NTbinop (t1, op, t2) ->
	LApp(interp_term_bin_op t.nterm_type op,[f t1;f t2])
    | NTbase_addr t -> 
	LApp("base_addr",[f t])
    | NTblock_length t -> 
	LApp("block_length",[interp_var label "alloc"; f t])
    | NTat (t, l) -> 
	interp_term (Some l) old_label t
    | NTif (_, _, _) -> 
	unsupported t.nterm_loc "logic if-then-else"
    | NTarrow (t, field) -> 
	let te = f t in
	let var = field.var_unique_name in
	LApp("acc",[interp_var label var;te])
    | NTstar t1 -> 
	let te1 = f t1 in
	let var = global_var_for_type t.nterm_type in
	LApp("acc",[interp_var label var;te1])
    | NTunop (Ustar, _) -> assert false
    | NTunop (Uamp, t1) -> 
	interp_term_address label old_label t1
    | NTunop (Uminus, t1) -> 
	LApp(interp_term_un_op t1.nterm_type Uminus, [f t1])
    | NTunop (Ufloat_of_int, t1) ->
	LApp("real_of_int", [f t1])
    | NTunop (Uint_of_float, t1) ->
	LApp("int_of_real", [f t1])
    | NTapp (g, l) -> 
	LApp(g.logic_name,
	     (HeapVarSet.fold 
		(fun x acc -> (interp_var label x.var_unique_name)::acc) 
		g.logic_args []) 
	     @ List.map f l)
    | NTnull -> 
	LVar "null"
    | NTresult -> 
	LVar "result" 
    | NTcast({ctype_node = Tpointer _}, 
	    {nterm_node = NTconstant (IntConstant "0")}) ->
	LVar "null"
    | NTcast (ty, t) -> 
	begin match ty.ctype_node, t.nterm_type.ctype_node with
	  | (Tenum _ | Tint _), (Tenum _ | Tint _)
	  | Tfloat _, Tfloat _ -> 
	      f t
	  | Tfloat _, (Tenum _ | Tint _) ->
	      LApp ("real_of_int", [f t])
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      f t
	  | _ -> 
	      unsupported t.nterm_loc "logic cast"
	end

and interp_term_address  label old_label e = match e.nterm_node with
  | NTvar v -> 
      begin match e.nterm_type.ctype_node with
	| Tstruct _ | Tunion _ -> LVar v.var_unique_name
	| _ -> unsupported e.nterm_loc "& operator"
      end
  | NTunop (Ustar, e1) -> 
      interp_term  label old_label e1
  | NTarrow (e1, f) ->
      begin match e.nterm_type.ctype_node with
	| Tenum _ | Tint _ | Tfloat _ -> 
  	    interp_term  label old_label e1
	| Tstruct _ | Tunion _ | Tpointer _ | Tarray _ ->
	    let var = f.var_unique_name in
	    LApp("acc",[interp_var label var; interp_term label old_label e1])
	| _ -> unsupported e.nterm_loc "& operator on a field"
      end
  | NTcast (_, e1) ->
      interp_term_address  label old_label e1
  | _ -> 
      assert false (* not a left value *)

let rec interp_predicate label old_label p =
  let f = interp_predicate label old_label in
  let ft = interp_term label old_label in
  match p with
    | NPtrue -> 
	LTrue
    | NPexists (l, p) -> 
	let l = List.fold_right(fun (t,x) l->(t,x.var_unique_name)::l) l [] in		     
	List.fold_right
	  (fun (t,x) p -> LExists(x,([],Ceffect.interp_type t),p)) l (f p)
    | NPforall (l, p) ->	
	let l = List.fold_right(fun (t,x) l->(t,x.var_unique_name)::l) l [] in
	List.fold_right
	  (fun (t,x) p -> LForall(x,([],Ceffect.interp_type t),p))
	  l (interp_predicate label old_label p)
    | NPif (t, p1, p2) -> 
	let t = ft t in
	let zero = LConst (Prim_int Int64.zero) in
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
    | NPapp (v, tl) ->
	LPred(v.logic_name, 
	      (HeapVarSet.fold 
		 (fun x acc -> (interp_var label x.var_unique_name)::acc) 
		 v.logic_args []) 
	      @ List.map ft tl)
    | NPfalse -> 
	LFalse
    | NPold p -> 
	interp_predicate (Some old_label) old_label p
    | NPat (p, l) -> 
	interp_predicate (Some l) old_label p
    | NPfresh (t) ->
	LPred("fresh",[interp_var (Some old_label) "alloc"; ft t])
    | NPvalid (t) ->
	LPred("valid",[interp_var label "alloc"; ft t])
    | NPvalid_index (t,a) ->
	LPred("valid_index",[interp_var label "alloc"; ft t;ft a])
    | NPvalid_range (t,a,b) ->
	LPred("valid_range",[interp_var label "alloc"; ft t;ft a;ft b])
    | NPnamed (n, p) ->
	LNamed (n, f p)

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

let int_one = Cte(Prim_int Int64.one)
let int_minus_one = Cte(Prim_int Int64.minus_one)
let float_one = Cte(Prim_float "1.0")

let interp_incr_op ty op = match ty.Ctypes.ctype_node, op with
  | (Tenum _ | Tint _), (Upostfix_inc | Uprefix_inc) -> "add_int", int_one
  | (Tenum _ | Tint _), (Upostfix_dec | Uprefix_dec) -> "sub_int", int_one
  | Tfloat _, (Upostfix_inc | Uprefix_inc) -> "add_real", float_one
  | Tfloat _, (Upostfix_dec | Uprefix_dec) -> "sub_real", float_one
  | (Tpointer _ | Tarray _), 
    (Upostfix_inc | Uprefix_inc) -> "shift_", int_one
  | (Tpointer _ | Tarray _), 
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
  match e.nexpr_node with
    | NEconstant (IntConstant c) -> 
	Cte (Prim_int (Cconst.int e.nexpr_loc c))
    | NEconstant (FloatConstant c) ->
	Cte(Prim_float c)
    | NEvar(Var_info v) -> 
	let n = v.var_unique_name in
	(*if v.var_is_referenced then
	  begin match e.nexpr_type.ctype_node with
	    | CTstruct _ | CTunion _ -> 
		if v.var_is_assigned then Deref n else Var n
	    | _ -> 
		let var = global_var_for_type e.nexpr_type in
		make_app "acc_" [Var var; Var n]
	  end
	else*) if v.var_is_assigned then Deref n else Var n
    | NEvar(Fun_info v) -> assert false
    (* a ``boolean'' expression is [if e then 1 else 0] *)
    | NEbinary(_,(Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		 |Blt_float | Bgt_float | Ble_float | Bge_float 
		 |Beq_float | Bneq_float 
		 |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		 |Beq_pointer | Bneq_pointer 
		 |Blt | Bgt | Ble | Bge | Beq | Bneq | Band | Bor),_) 
    | NEunary (Unot, _) ->
	If(interp_boolean_expr e, 
	   Cte(Prim_int Int64.one), Cte(Prim_int Int64.zero))
    | NEbinary(e1,op,e2) ->
	build_minimal_app (Var (interp_bin_op op)) 
	  [interp_expr e1;interp_expr e2]
    | NEassign (e1,e2) ->
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
    | NEincr(op,e) -> 
	interp_incr_expr op e
    | NEassign_op(e1,op,e2) ->
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
    | NEseq(e1,e2) ->
	append (interp_statement_expr e1) (interp_expr e2)
    | NEnop -> 
	Void
    | NEcond(e1,e2,e3) ->
	If(interp_boolean_expr e1, interp_expr e2, interp_expr e3)
    | NEstring_literal s -> 
	unsupported e.nexpr_loc "string literal"
    | NEarrow (e,s) ->
	let te = interp_expr e in
	let var = s.var_unique_name in
	Output.make_app "acc_" [Var(var);te]
    | NEstar e1 -> 
	let te1 = interp_expr e1 in
	let var = global_var_for_type e.nexpr_type in
	make_app "acc_" [Var var;te1]
    | NEunary (Ustar, e) -> assert false
    | NEunary (Uplus, e) ->
	interp_expr e
    | NEunary(Uminus, e) -> 
	begin match e.nexpr_type.Ctypes.ctype_node with
	  | Tenum _ | Tint _ -> make_app "neg_int" [interp_expr e]
	  | Tfloat _ -> make_app "neg_real" [interp_expr e]
	  | _ -> assert false
	end
    | NEunary (Uint_of_float, e) ->
	make_app "int_of_real" [interp_expr e]
    | NEunary (Ufloat_of_int, e) ->
	make_app "real_of_int" [interp_expr e]
    | NEunary (Utilde, e) ->
	make_app "bw_compl" [interp_expr e]
    | NEunary (Uamp, e) ->
	interp_address e
    | NEcall(e,args) -> 
	begin
	  match e.nexpr_node with
	    | NEvar (Fun_info v) ->
		let targs = match args with
		  | [] -> [Output.Var "void"]
		  | _ -> List.map interp_expr args
		in
		build_complex_app (Var (v.fun_unique_name ^ "_parameter")) 
		  targs
	    | _ -> 
		unsupported e.nexpr_loc "call of a non-variable function"
	end
    | NEcast({Ctypes.ctype_node = Tpointer _}, 
	     {nexpr_node = NEconstant (IntConstant "0")}) ->
	Var "null"
    | NEcast(t,e1) -> 
	begin match t.Ctypes.ctype_node, e1.nexpr_type.Ctypes.ctype_node with
	  | (Tenum _ | Tint _), (Tenum _ | Tint _)
	  | Tfloat _, Tfloat _ -> 
	      interp_expr e1
	  | Tfloat _, (Tenum _ | Tint _) ->
	      make_app "real_of_int" [interp_expr e1]
	  | (Tenum _ | Tint _), Tfloat _ ->
	      make_app "int_of_real" [interp_expr e1]
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      interp_expr e1
	  | _ -> 
	      unsupported e.nexpr_loc "cast"
	end
(*
    | NEsizeof(t) -> 
	Cte (Prim_int (Int64.to_int (Cltyping.sizeof e.nexpr_loc t)))
*)

and interp_boolean_expr e =
  match e.nexpr_node with
    | NEbinary(e1, (Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		   |Blt_float | Bgt_float | Ble_float | Bge_float 
		   |Beq_float | Bneq_float 
		   |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		   |Beq_pointer | Bneq_pointer 
		   |Blt | Bgt | Ble | Bge | Beq | Bneq as op), e2) ->
	build_minimal_app (Var (interp_bin_op op)) 
	  [interp_expr e1; interp_expr e2]
    | NEbinary (e1, Band, e2) ->
	And(interp_boolean_expr e1, interp_boolean_expr e2)
    | NEbinary (e1, Bor, e2) ->
	Or(interp_boolean_expr e1, interp_boolean_expr e2)
    | NEunary (Unot, e) ->
	Not(interp_boolean_expr e)
    (* otherwise e <> 0 *)
    | _ -> 
	let cmp,zero = match e.nexpr_type.Ctypes.ctype_node with
	  | Tenum _ | Tint _ -> "neq_int", Cte (Prim_int Int64.zero)
	  | Tfloat _ -> "neq_real", Cte (Prim_float "0.0")
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
  match e.nexpr_node with
    | NEvar (Var_info v) -> LocalRef(v)
    | NEvar (Fun_info v) -> assert false
    | NEunary(Ustar,e1) -> assert false
    | NEstar(e1) ->
	let var = global_var_for_type e.nexpr_type in
	HeapRef(var,interp_expr e1)
(*
    | NEarrget(e1,e2) ->
	let te1 = interp_expr e1 and te2 = interp_expr e2 in
	let var = global_var_for_type e.nexpr_type in
	HeapRef(var,build_complex_app (Var "shift_")
		  [interp_expr e1; interp_expr e2])
*)
(*
    | NEdot ({texpr_node = NEunary (Ustar, e1)}, f) ->
	assert false
    | NEdot (e1,f)
*)
    | NEarrow (e1,f) ->
	HeapRef(f.var_unique_name, interp_expr e1)
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
  | NEstar(e1) ->
      interp_expr e1
(*
  | NEarrget (e1, e2) ->
      build_complex_app (Var "shift_") [interp_expr e1; interp_expr e2]
  | NEdot ({texpr_node = NEunary (Ustar, e1)}, f) ->
      assert false
  | NEdot (e1, f)
*)
  | NEarrow (e1, f) ->
      begin match e.nexpr_type.Ctypes.ctype_node with
	| Tenum _ | Tint _ | Tfloat _ -> 
  	    interp_expr e1
	| Tstruct _ | Tunion _ | Tpointer _ | Tarray _ ->
            build_complex_app (Var "acc_") 
	    [Var f.var_unique_name; interp_expr e1]
	| _ -> unsupported e.nexpr_loc "& operator on a field"
      end
(*
  | NEcast (_, e1) ->
      interp_address e1
*)
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
	    | HeapRef(var,e1) ->
		(* upd var e1 e *)
		(build_complex_app (Var "upd_")
		   [Var var;e1; interp_expr e])
	end 
    | NEincr(op,e) ->
	let top,one = interp_incr_op e.nexpr_type op in
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
    | NEcall (e1,args) -> 
	begin
	  match e1.nexpr_node with
	    | NEvar (Fun_info v) ->
		let targs = match args with
		  | [] -> [Output.Var "void"]
		  | _ -> List.map interp_expr args
		in
		let app = 
		  build_complex_app (Var (v.fun_unique_name ^ "_parameter")) 
		    targs
		in
		if e.nexpr_type.Ctypes.ctype_node = Tvoid then
		  app
		else
		  Let (tmp_var (), app, Void)
	    | _ -> 
		unsupported e.nexpr_loc "call of a non-variable function"
	end
    | NEassign_op (l, op, e) -> 
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
(*
    | NEsizeof _ 
*)
    | NEcast (_, _)
    | NEcond (_, _, _)
    | NEbinary (_, _, _)
    | NEunary (_, _)
    | NEstar _ 
(*
    | NEarrget (_, _)
*)
    | NEarrow (_, _)
(*
    | NEdot (_, _)
*)
    | NEvar _
    | NEstring_literal _
    | NEconstant _ -> 
	unsupported e.nexpr_loc "statement expression"

module StringMap = Map.Make(String)

type mem_or_ref = Reference of bool | Memory of Output.term list

let collect_locations before acc loc =
  let var,iloc =
    match loc with
      | Lterm t -> 
	  begin
	    match t.nterm_node with
	      | NTarrow(e,f) ->
		  let loc = 
		    LApp("pointer_loc",[interp_term (Some before) before e]) 
		  in
		  f.var_unique_name, Some loc
	      | NTstar e1 -> 
		  let var = global_var_for_array_type e1.nterm_type in
		  let loc = 
		    LApp("pointer_loc", [interp_term (Some before) before e1])
		  in
		  var, Some loc
	      | NTvar v ->
		  v.var_unique_name, None
	      | _ ->
		  assert false
	  end
    | Lstar t -> 
	let var = global_var_for_array_type t.nterm_type in
	let loc = 
	  LApp("all_loc",[interp_term (Some before) before t])
	in
	var, Some loc
    | Lrange(t1,t2,t3) -> 
	let var = global_var_for_array_type t1.nterm_type in
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
	     StringMap.add v.var_unique_name t m)
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
       if Ceffect.intersect_only_alloc e hvs then acc
       else make_and (weak_invariant id p) acc) 
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
    Cnorm.make_and 
      (snd (Cnorm.separation loc v t))
      (Cnorm.valid_for_type ~fresh:true loc v t)
  in
  BlackBox(Annot_type(LTrue,base_type "pointer",["alloc"],["alloc"],
		      make_and 
			(interp_predicate None "" form)
			(LPred ("alloc_stack", 
				[LVar "result"; LVar "alloc@"; LVar "alloc"])), 
		      None))
      
let interp_decl d acc = 
  match d.node with 
    | Ndecl(ctype,v,init) -> 
	lprintf 
	  "translating local declaration of %s@." v.var_unique_name;
	if v.var_is_referenced then
	  let t = { nterm_node = NTresult; 
		    nterm_loc = d.loc;
		    nterm_type = Ctypes.c_pointer ctype } in
	  Let(v.var_unique_name, alloc_on_stack d.loc v t, acc)
	else
	  let tinit = match init with 
	    | None ->
		begin match ctype.Ctypes.ctype_node with
		  | Tenum _ | Tint _ -> App(Var("any_int"),Var("void"))
		  | Tfloat _ -> App(Var("any_real"),Var("void"))
		  | Tarray (_, None) | Tpointer _ -> 
		      App(Var "any_pointer", Var "void")
		  | Tarray _ | Tstruct _ | Tunion _ -> 
                      let t = { nterm_node = NTresult; 
				nterm_loc = d.loc;
				nterm_type = ctype } in
                      alloc_on_stack d.loc v t
		  | Tvoid | Tvar _ | Tfun _ -> assert false
		end
	    | Some (Iexpr e) -> interp_expr e		
	    | Some (Ilist _) -> 
		unsupported d.loc "structured initializer for local var"
	  in
	  if v.var_is_assigned then
	    Let_ref(v.var_unique_name,tinit,acc)
	  else
	    Let(v.var_unique_name,tinit,acc)
    | Ntypedef _
    | Ntypedecl { Ctypes.ctype_node = Tstruct _ | Tunion _ } -> 
	acc
    | Ntypedecl { Ctypes.ctype_node = Tenum _ } -> 
	unsupported d.loc "local enum type"
    | Ntypedecl _
    | Nfunspec _
    | Naxiom _
    | Ninvariant _
    | Nlogic _
    | Nfundef _ ->
	assert false


let interp_invariant label effects annot =
  let inv = match annot.invariant with
    | None -> LTrue
    | Some inv -> interp_predicate None "init" inv
  in
  let inv = make_and (interp_assigns label effects annot.loop_assigns) inv in
  let var = match annot.variant with
    | None -> LConst (Prim_int Int64.zero), None
    | Some (var,r) -> interp_term None "init" var, r
  in
  (inv, var)

let new_label = let r = ref 0 in fun () -> incr r; "label_" ^ string_of_int !r

let try_with_void ex e = Try (e, ex, None, Void)  

let break b e = if b then try_with_void "Break" e else e

let continue b e = if b then try_with_void "Continue" e else e    

let return_exn ty = match ty.Ctypes.ctype_node with
  | Tenum _ | Tint _ -> "Return_int"
  | Tfloat _ -> "Return_real"
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
	 interp_statement ab may_break s1, interp_statement ab may_break s2)
  | NSfor(annot,e1,e2,e3,body) ->
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
	   (break body.nst_break 
	      (make_while (interp_boolean_expr e2) inv dec 
		 (append 
		    (continue body.nst_continue
		       (interp_statement true (ref false) body))
		    (interp_statement_expr e3)))))
  | NSwhile(annot,e,s) -> 
      let label = new_label () in
      let ef = 
	HeapVarSet.union (Ceffect.expr e).Ceffect.assigns
	  (Ceffect.statement s).Ceffect.assigns 
      in
      let (inv,dec) = interp_invariant label ef annot in
      append (Output.Label label)
	(break s.nst_break
	   (make_while (interp_boolean_expr e) inv dec 
	      (continue s.nst_continue (interp_statement true (ref false) s))))
  | NSdowhile(annot,s,e) -> 
      let label = new_label () in
      let ef = 
	HeapVarSet.union (Ceffect.expr e).Ceffect.assigns
	  (Ceffect.statement s).Ceffect.assigns 
      in
      let (inv,dec) = interp_invariant label ef annot in
      append (Output.Label label)
	(break true
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
      append (Output.Label lab) (interp_statement ab may_break s)
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
(*
  | NScase(e,s) -> 
      unsupported "case"
  | NSdefault(s) -> 
      unsupported "default"
  | NSgoto(lab) -> 
      unsupported "goto"
*)
  | NSassert(pred) -> 
      Output.Assert(interp_predicate None "init" pred)
  | NSlogic_label(l) -> 
      Output.Label l
  | NSspec (spec,s) ->
      let eff = Ceffect.statement s in
      let pre,post = interp_spec eff.Ceffect.reads eff.Ceffect.assigns spec in
      Triple(pre,interp_statement ab may_break s,post,None)

and interp_block ab may_break (decls,stats) =
  let rec block = function
    | [] -> 
	Void
    | [s] ->
	interp_statement ab may_break s
    | { nst_node = NSnop } :: bl ->
	block bl
    | { nst_node = NSif (e, s1, s2) } as s :: bl ->
	begin match s1.nst_term, s2.nst_term with
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
	if not s.nst_term then unreachable_block bl;
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
	 (id.var_unique_name,([],Ceffect.interp_type t))::args)
      args []
  in
  HeapVarSet.fold
    (fun arg t -> (arg.var_unique_name,Ceffect.heap_var_type arg)::t)
    id.logic_args args

let cinterp_logic_symbol id ls =
  match ls with
    | NPredicate_reads(args,locs) -> 
	let args = interp_predicate_args id args in
	let ty = 
	  List.fold_right 
	    (fun (x,t) ty -> 
	       Prod_type (x, Base_type t, ty)) 
	    args (Base_type ([],"prop"))
	in
	Logic(false, id.logic_name, ty)
    | NPredicate_def(args,p) -> 
	let a = interp_predicate None "" p in
	let args = interp_predicate_args id args in
	Predicate(false,id.logic_name,args,a)
    | NFunction(args,ret,_) ->
	let local_type =
	  List.fold_right
	    (fun (id,ty) t -> 
	       Prod_type(id.var_unique_name,base_type (Ceffect.interp_type ty),t))
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
    (fun arg t -> LForall(arg.var_unique_name,Ceffect.heap_var_type arg,t))
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

let heap_var_unique_names v =
  HeapVarSet.fold (fun v l -> v.var_unique_name::l) v []
  

let interp_function_spec id sp ty pl =
  let tpl = interp_fun_params pl in
  let pre,post = interp_spec id.function_reads id.function_writes sp in
  let r = heap_var_unique_names id.function_reads in
  let w = heap_var_unique_names id.function_writes in
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
  tpl,pre,post, Param (false, id.fun_unique_name ^ "_parameter", ty)

let interp_type loc ctype = match ctype.Ctypes.ctype_node with
  | Tenum e ->
      begin match Cenv.tag_type_definition e with
	| Cenv.TTEnum ((Tenum n),el) -> 
	    List.flatten
	      (List.map 
		 (fun (x,v) -> 
		    let a = LPred ("eq_int", [LVar x; LConst(Prim_int v)]) in
		    [Param (false,x,Base_type ([], "int"));
		     Axiom ("enum_" ^ n ^ "_" ^ x, a)])
		 el)
	| _ -> assert false
      end
  | _ -> 
      []

let interp_located_tdecl ((why_code,why_spec,prover_decl) as why) decl =
  match decl.node with
  | Nlogic(id,ltype) -> 
      lprintf "translating logic declaration of %s@." id.logic_name;
      (why_code, cinterp_logic_symbol id ltype::why_spec,
       prover_decl)
  | Naxiom(id,p) -> 
      lprintf "translating axiom declaration %s@." id;      
      let a = interp_axiom p in
      (why_code, Axiom(id,a)::why_spec, prover_decl)
  | Ninvariant(id,p) -> 
      lprintf "translating invariant declaration %s@." id;      
      why
  | Ntypedecl ({ Ctypes.ctype_node = Tenum _ } as ctype)
  | Ntypedef (ctype,_) -> 
      let dl = interp_type decl.loc ctype in 
      why_code, dl @ why_spec, prover_decl
  | Ntypedecl { Ctypes.ctype_node = Tstruct _ | Tunion _ } -> 
      why
  | Ntypedecl _ ->
      assert false
  | Ndecl(ctype,v,init) -> 
      lprintf "translating global declaration of %s@." v.var_unique_name;
      begin match init with 
	| None ->
	    ()
	| _ -> 
	    warning decl.loc ("ignoring initializer for " ^ v.var_unique_name);
      end;
      why
  | Nfunspec(spec,ctype,id,params) -> 
      let _,_,_,spec = interp_function_spec id spec ctype params in
      (why_code, spec :: why_spec,
       prover_decl)
  | Nfundef(spec,ctype,id,params,block) ->      
      reset_tmp_var ();
      let tparams,pre,post,tspec = 
	interp_function_spec id spec ctype params in
      let f = id.fun_unique_name in
      if Coptions.verify id.fun_name then begin try
	lprintf "translating function %s@." f;
	abrupt_return := None;
	let may_break = ref false in
	let list_of_refs =
	  List.fold_right
	    (fun (ty,id) bl ->
	       if id.var_is_assigned
	       then 
		 let n = id.var_unique_name in
		 set_unique_name (Var_info id) ("mutable_" ^ n); 
		 unset_formal_param id;
		 (id.var_unique_name,n) :: bl
	       else bl) 
	    params [] 
	in
	let tblock = catch_return (interp_statement false may_break block) in
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

let interp l =
  List.fold_left interp_located_tdecl ([],[],[]) l

