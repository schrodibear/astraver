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

(*i $Id: cinterp.ml,v 1.76 2004-04-22 13:24:13 filliatr Exp $ i*)


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
    | CTarray (ty,_) | CTpointer ty -> global_var_for_type ty ^ "P"
    | CTstruct _ -> "pointer"
    | _ -> assert false (* TODO *)

let global_var_for_array_type t =
  match t.ctype_node with
    | CTpointer ty | CTarray(ty,_) -> global_var_for_type ty
    | _ -> assert false

let interp_rel t1 t2 r = match t1.ctype_node, t2.ctype_node, r with
  | (CTenum _ | CTint _), (CTenum _ | CTint _), Lt -> "lt_int"
  | (CTenum _ | CTint _), (CTenum _ | CTint _), Gt -> "gt_int"
  | (CTenum _ | CTint _), (CTenum _ | CTint _), Le -> "le_int"
  | (CTenum _ | CTint _), (CTenum _ | CTint _), Ge -> "ge_int"
  | (CTenum _ | CTint _), (CTenum _ | CTint _), Eq -> "eq_int"
  | (CTenum _ | CTint _), (CTenum _ | CTint _), Neq -> "neq_int"
  | CTfloat _, CTfloat _, Lt -> "lt_float"
  | CTfloat _, CTfloat _, Gt -> "gt_float"
  | CTfloat _, CTfloat _, Le -> "le_float"
  | CTfloat _, CTfloat _, Ge -> "ge_float"
  | CTfloat _, CTfloat _, Eq -> "eq_float"
  | CTfloat _, CTfloat _, Neq -> "neq_float"
  | (CTarray _ | CTpointer _), (CTarray _ | CTpointer _), Lt -> "lt_pointer"
  | (CTarray _ | CTpointer _), (CTarray _ | CTpointer _), Le -> "le_pointer"
  | (CTarray _ | CTpointer _), (CTarray _ | CTpointer _), Gt -> "gt_pointer"
  | (CTarray _ | CTpointer _), (CTarray _ | CTpointer _), Ge -> "ge_pointer"
  | _, _, Eq -> "eq"
  | _, _, Neq -> "neq"
  | _ -> assert false

let interp_term_bin_op ty op =
  match ty.ctype_node, op with
  | (CTenum _ | CTint _), Badd -> "add_int"
  | (CTenum _ | CTint _), Bsub -> "sub_int"
  | (CTenum _ | CTint _), Bmul -> "mul_int"
  | (CTenum _ | CTint _), Bdiv -> "div_int"
  | (CTenum _ | CTint _), Bmod -> "dmod_int"
  | CTfloat _, Badd -> "add_float"
  | CTfloat _, Bsub -> "sub_float"
  | CTfloat _, Bmul -> "mul_float"
  | CTfloat _, Bdiv -> "div_float"
  | (CTpointer _ | CTarray _), Badd -> "shift"
  | (CTpointer _ | CTarray _), Bsub -> "sub_pointer"
  | _ -> assert false

let interp_term_un_op ty op = match ty.ctype_node, op with
  | (CTenum _ | CTint _), Uminus -> "neg_int"
  | CTfloat _, Uminus -> "neg_float"
  | _ -> assert false

let interp_var label v =
  match label with 
    | None -> LVar v 
    | Some l -> LVarAtLabel(v,l)
  
let rec interp_term label old_label t =
  let f = interp_term label old_label in
  match t.term_node with
    | Tconstant c ->
	begin
	  try
	    LConst(Prim_int(int_of_string c))
	  with Failure "int_of_string" -> 
	    LConst(Prim_float(float_of_string c))
	end  
    | Tvar { var_name = v ; var_is_assigned = true } -> 
	interp_var label v
    | Tvar { var_name = v ; var_is_assigned = false } -> 
	LVar v
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
	let var = field in
	LApp("acc",[interp_var label var;te])
    | Tunop (Ustar, t1) -> 
	let te1 = f t1 in
	let var = global_var_for_type t.term_type in
	LApp("acc",[interp_var label var;te1])
    | Tunop (Uminus, t1) -> 
	LApp(interp_term_un_op t1.term_type Uminus, [f t1])
    | Tapp (g, l) -> 
	LApp(g.logic_name,
	     (HeapVarSet.fold (fun x acc -> (interp_var label x)::acc) 
		g.logic_args []) 
	     @ List.map f l)
    | Tnull -> 
	LVar "null"
    | Tresult -> 
	LVar "result" 
    | Tcast({ctype_node = CTpointer _}, {term_node = Tconstant "0"}) ->
	LVar "null"
    | Tcast (ty, t) -> 
	begin match ty.ctype_node, t.term_type.ctype_node with
	  | (CTenum _ | CTint _), (CTenum _ | CTint _)
	  | CTfloat _, CTfloat _ -> 
	      f t
	  | CTfloat _, (CTenum _ | CTint _) ->
	      LApp ("float_of_int", [f t])
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      f t
	  | _ -> 
	      unsupported "logic cast"
	end

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
    | Pif (_, _, _) -> 
	unsupported "logic if-then-else predicate"
    | Pnot p -> 
	LNot (f p)
    | Pimplies (p1, p2) -> 
	make_impl (f p1) (f p2)
    | Por (p1, p2) -> 
	make_or (f p1) (f p2)
    | Pand (p1, p2) -> 
	make_and (f p1) (f p2)
    | Prel (t1, op, t2) ->
	LPred(interp_rel t1.term_type t2.term_type op,[ft t1;ft t2])
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
  | Badd_float -> "add_float"
  | Bsub_float -> "sub_float"
  | Bmul_float -> "mul_float"
  | Bdiv_float -> "div_float"
  | Blt_float -> "lt_float"
  | Bgt_float -> "gt_float"
  | Ble_float -> "le_float"
  | Bge_float -> "ge_float"
  | Beq_float -> "eq_float"
  | Bneq_float -> "neq_float" 
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
  | CTfloat _, (Upostfix_inc | Uprefix_inc) -> "add_float", float_one
  | CTfloat _, (Upostfix_dec | Uprefix_dec) -> "sub_float", float_one
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
    | TEconstant(c) -> 
	begin
	  try
	    Cte(Prim_int(int_of_string c))
	  with Failure "int_of_string" -> 
	    Cte(Prim_float(float_of_string c))
	end
    | TEvar(v) -> 
        if v.var_name = "t"
	then begin
	  Loc.report Coptions.log e.texpr_loc;
	  lprintf "translating var t: is_assigned = %b@."
	    v.var_is_assigned;
	end;
	if v.var_is_assigned then Deref(v.var_name) else Var(v.var_name)
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
		append (Assign(v.var_name,interp_expr e2)) (Deref v.var_name)
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
	      append
	        (Assign(v.var_name,
			make_app (interp_bin_op op) 
			  [Deref(v.var_name); interp_expr e2]))
	        (Deref v.var_name)
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
	let var = s in
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
	  | CTfloat _ -> make_app "neg_float" [interp_expr e]
	  | _ -> assert false
	end
    | TEunary (Uint_of_float, e) ->
	unsupported "int_of_float"
    | TEunary (Ufloat_of_int, e) ->
	make_app "float_of_int" [interp_expr e]
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
		build_complex_app (Var (v.var_name ^ "_parameter")) targs
	    | _ -> 
		unsupported "call of a non-variable function"
	end
    | TEcast({ctype_node = CTpointer _}, {texpr_node = TEconstant "0"}) ->
	Var "null"
    | TEcast(t,e) -> 
	begin match t.ctype_node, e.texpr_type.ctype_node with
	  | (CTenum _ | CTint _), (CTenum _ | CTint _)
	  | CTfloat _, CTfloat _ -> 
	      interp_expr e
	  | CTfloat _, (CTenum _ | CTint _) ->
	      make_app "float_of_int" [interp_expr e]
	  | ty1, ty2 when Cenv.eq_type_node ty1 ty2 -> 
	      interp_expr e
	  | _ -> 
	      unsupported "cast"
	end
    | TEsizeof_expr(e) -> 
	unsupported "sizeof_expr"
    | TEsizeof(t) -> 
	unsupported "sizeof"

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
	  | CTfloat _ -> "neq_float", Cte (Prim_float 0.0)
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
		Let("caduceus",Deref(v.var_name),
		    append 
		      (Assign(v.var_name,
			      make_app top [Var "caduceus";one]))
		      (Var "caduceus"))
	    | Uprefix_dec | Uprefix_inc ->
		(* v := op !v 1; !v *)
		append 
		  (Assign(v.var_name,
			  App(App(Var top, Deref(v.var_name)), one)))
		  (Deref v.var_name)
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
	HeapRef(f,interp_expr e1)
    | _ -> 
	assert false (* wrong typing of lvalue ??? *)

and interp_address e = match e.texpr_node with
  | TEvar v -> 
      begin match e.texpr_type.ctype_node with
	| CTstruct _ | CTunion _ -> Deref v.var_name
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
            build_complex_app (Var "acc_") [Var f; interp_expr e1]
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
		Assign(v.var_name,interp_expr e)
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
		Assign(v.var_name,
		       make_app top [Deref(v.var_name); one])
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
		  build_complex_app (Var (v.var_name ^ "_parameter")) targs
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
		Assign(v.var_name,
		       make_app (interp_bin_op op) 
			 [Deref(v.var_name); interp_expr e])
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
    | TEsizeof_expr _
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

let collect_locations acc loc =
  let var,iloc =
    match loc with
      | Lterm t -> 
	  begin
	    match t.term_node with
	      | Tdot({term_node = Tunop (Clogic.Ustar, e)}, f) ->
		  assert false
	      | Tdot(e,f)
	      | Tarrow(e,f) ->
		  f,LApp("pointer_loc",[interp_term (Some "") "" e])
	      | Tarrget(e1,e2) -> 
		  let var = global_var_for_array_type e1.term_type in
		  let loc = 
		    LApp("pointer_loc",
			 [LApp("shift",
			       [interp_term (Some "") "" e1;
				interp_term (Some "") "" e2])]) 
		  in
		  var,loc
	      | Tunop (Clogic.Ustar, e1) -> 
		  let var = global_var_for_array_type e1.term_type in
		  let loc = 
		    LApp("pointer_loc", [interp_term (Some "") "" e1])
		  in
		  var,loc
	      | _ ->
		  assert false
	  end
    | Lstar t -> 
	let var = global_var_for_array_type t.term_type in
	let loc = 
	  LApp("all_loc",[interp_term (Some "") "" t])
	in
	var,loc
	
    | Lrange(t1,t2,t3) -> 
	let var = global_var_for_array_type t1.term_type in
	let loc = 
	  LApp("range_loc",
	       [interp_term (Some "") "" t1;
		interp_term (Some "") "" t2;
		interp_term (Some "") "" t3;])
	in
	var,loc


  in
  try
    let p = StringMap.find var acc in
    StringMap.add var (iloc::p) acc
  with
      Not_found -> 
	assert false (* it is a real assert false *)
	(* old was: StringMap.add var iloc acc *)



let map_of_assigns assigns =
  HeapVarSet.fold 
    (fun v acc -> StringMap.add v [] acc) assigns StringMap.empty 

let rec make_union_loc = function
  | [] -> LVar "nothing_loc"
  | [l] -> l
  | l::r -> LApp("union_loc",[l;make_union_loc r])

let interp_assigns assigns = function
  | Some locl ->
      let l = List.fold_left collect_locations (map_of_assigns assigns) locl in
      StringMap.fold
	(fun v p acc ->
	   make_and acc
	     (LPred("assigns",
		    [LVarAtLabel("alloc",""); LVarAtLabel(v,"");LVar v; 
		     make_union_loc p])))
	l LTrue
  | None ->
      LTrue

(* table for weak invariants *)
let weak_invariants = Hashtbl.create 97

let add_weak_invariant id p =
  let e = Ceffect.predicate p in
  Hashtbl.add weak_invariants id (interp_predicate None "" p, e)

let weak_invariants_for hvs =
  Hashtbl.fold
    (fun _ (p,e) acc -> 
       if not (HeapVarSet.is_empty (HeapVarSet.inter e hvs)) then
	 make_and p acc 
       else acc)
    weak_invariants LTrue

let interp_spec effect_reads effect_assigns s =
  let tpre = 
    make_and
      (interp_predicate_opt None "" s.requires)
      (weak_invariants_for effect_reads)
  and tpost = 
    make_and
      (interp_predicate_opt None "" s.ensures)
      (make_and 
	 (interp_assigns effect_assigns s.assigns)
	 (weak_invariants_for effect_assigns))
  in 
  (tpre,tpost)


let interp_decl d acc = 
  match d.node with 
    | Tdecl(ctype,v,init) -> 
	lprintf 
	  "translating local declaration of %s@." v.var_name;
	let tinit =
	  match init with 
	    | Inothing ->
		begin match ctype.ctype_node with
		  | CTenum _ | CTint _ -> App(Var("any_int"),Var("void"))
		  | CTfloat _ -> App(Var("any_float"),Var("void"))
		  | CTfun _ -> assert false
		  | _ -> App(Var("any_pointer"),Var("void"))
		end
	    | Iexpr e -> interp_expr e		
	    | Ilist _ -> unsupported "structured initializer for local var"
	in
	if v.var_is_assigned then
	  Let_ref(v.var_name,tinit,acc)
	else
	  Let(v.var_name,tinit,acc)
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


let interp_invariant annot =
  match annot with
    | { invariant = None; variant = None } -> 
	(LTrue, (LConst (Prim_int 0), None))
    | { invariant = Some inv; variant = Some (var,r) } -> 
	(interp_predicate None "init" inv, (interp_term None "" var, r))
    | { invariant = None; variant = Some (var,r) } -> 
	(LTrue, (interp_term None "" var, r))
    | { invariant = Some inv; variant = None } -> 
	(interp_predicate None "init" inv, (LConst (Prim_int 0), None))

let try_with_void ex e = Try (e, ex, None, Void)  

let break b e = if b then try_with_void "Break" e else e

let continue b e = if b then try_with_void "Continue" e else e    

let return_exn ty = match ty.ctype_node with
  | CTenum _ | CTint _ -> "Return_int"
  | CTfloat _ -> "Return_float"
  | _ -> "Return_pointer"

(* [abrupt_return] contains the exception used for last abrupt return if any *)
let abrupt_return = ref None

let catch_return e = match !abrupt_return with
  | None -> 
      e
  | Some "Return" ->
      Try (e, "Return", None, Void)
  | Some r ->
      Try (e, r, Some "result", Var "result")

(* [ab] indicates if returns are abrupt *)

let rec interp_statement ab stat = match stat.st_node with
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
      If(interp_boolean_expr e,interp_statement ab s1,interp_statement ab s2)
  | TSfor(annot,e1,e2,e3,body) ->
      let (inv,dec) = interp_invariant annot in
      append
	(interp_statement_expr e1)
	(break body.st_break 
	   (make_while (interp_boolean_expr e2) inv dec 
	      (continue body.st_continue
		 (append 
		    (interp_statement true body) 
		    (interp_statement_expr e3)))))
  | TSwhile(annot,e,s) -> 
      let (inv,dec) = interp_invariant annot in
      break s.st_break
	(make_while (interp_boolean_expr e) inv dec 
	   (continue s.st_continue (interp_statement true s)))
  | TSdowhile(annot,s,e) -> 
      let (inv,dec) = interp_invariant annot in
      break true
	(make_while (Cte (Prim_bool true)) inv dec
	   (continue s.st_continue
	      (append (interp_statement true s)
		 (If (Not (interp_boolean_expr e), 
		      Raise ("Break", None), Void)))))
  | TSblock(b) -> 
      interp_block ab b 
  | TSbreak -> 
      Raise ("Break", None)
  | TScontinue -> 
      Raise ("Continue", None)
  | TSlabel(lab,s) -> 
      append (Output.Label lab) (interp_statement ab s)
  | TSswitch(e,s) -> 
      unsupported "switch"
  | TScase(e,s) -> 
      unsupported "case"
  | TSgoto(lab) -> 
      unsupported "goto"
  | TSassert(pred) -> 
      Output.Assert(interp_predicate None "init" pred)
  | TSlogic_label(l) -> 
      Output.Label l
  | TSspec (spec,s) ->
      let eff = Ceffect.statement s in
      let pre,post = interp_spec eff.Ceffect.reads eff.Ceffect.assigns spec in
      Triple(pre,interp_statement ab s,post,None)

and interp_block ab (decls,stats) =
  let rec block = function
    | [] -> 
	Void
    | [s] ->
	interp_statement ab s
    | { st_node = TSnop } :: bl ->
	block bl
    | { st_node = TSif (e, s1, s2) } as s :: bl ->
	begin match s1.st_term, s2.st_term with
	  | true, true ->
	      append (interp_statement true s) (block bl)
	  | false, false ->
	      (* [bl] is actually unreachable *)
	      interp_statement ab s
	  | true, false ->
	      If (interp_boolean_expr e, 
		  block (s1 :: bl), interp_statement ab s2)
	  | false, true ->
	      If (interp_boolean_expr e,
		  interp_statement ab s1, block (s2 :: bl))
	end
    | s :: bl ->
	append (interp_statement true s) (block bl)
  in
  List.fold_right interp_decl decls (block stats)

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

let interp_fun_params pre params =
  if params=[]
  then pre, ["tt",unit_type]
  else List.fold_right 
    (fun (t,id) (pre,tpl) ->
       let tt = Ceffect.interp_type t in
       (((*if tt="pointer" 
	 then make_and (LNot(LPred("fresh",[LVar "alloc";LVar id]))) pre
	 else*) pre),
	(id,base_type tt)::tpl))
 params (pre,[])


let interp_function_spec id sp ty pl =
  let pre,post = interp_spec id.function_reads id.function_writes sp in
  let pre,tpl = interp_fun_params pre pl in
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
  Param (false, id.var_name ^ "_parameter", ty)

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
      add_weak_invariant id p;
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
      lprintf "translating global declaration of %s@." v.var_name;
      begin match ctype.ctype_node with
	| CTstruct _ -> 
	    let id = "valid_" ^ v.var_name in
	    add_weak_invariant id (Cltyping.valid_var v ctype)
	| _ -> 
	    ()
      end;
      begin match init with 
	| Inothing ->
	    ()
	| _ -> 
	    warning decl.loc ("ignoring initializer for " ^ v.var_name);
      end;
      why
  | Tfunspec(spec,ctype,id,params) -> 
      (why_code, interp_function_spec id spec ctype params :: why_spec,
       prover_decl)
  | Tfundef(spec,ctype,id,params,block) ->      
      reset_tmp_var ();
      let f = id.var_name in
      lprintf "translating function %s@." f;
      begin try
	let pre,post = interp_spec id.function_reads id.function_writes spec in
	let pre,tparams = interp_fun_params pre params in
	abrupt_return := None;
	let tblock = catch_return (interp_statement false block) in
	let tspec = interp_function_spec id spec ctype params in
	printf "generating Why code for function %s@." f;
	((Def(f ^ "_impl", Fun(tparams,pre,tblock,post,None)))::why_code,
	 tspec :: why_spec,
	 prover_decl)
      with Error (_, Cerror.Unsupported s) ->
	lprintf "unsupported feature (%s); skipping function %s@." s f;
	eprintf "unsupported feature (%s); skipping function %s@." s f;
	(why_code,
	 interp_function_spec id spec ctype params :: why_spec,
	 prover_decl)
      end

let interp l =
  List.fold_left interp_located_tdecl ([],[],[]) l

