(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: cinterp.ml,v 1.41 2004-03-22 13:46:05 filliatr Exp $ i*)


open Format
open Coptions
open Output
open Info
open Cast
open Clogic

let global_var_for_type t =
  match t.ctype_node with
    | CTint _ -> "intP"
    | _ -> assert false (* TODO *)

let interp_param (t,id) =
  (* TODO : tester si param is assigned *)
  (id,base_type (Ceffect.interp_type t))

let interp_rel = function
  | Lt -> "lt_int"
  | Gt -> "gt_int"
  | Le -> "le_int"
  | Ge -> "ge_int"
  | Eq -> "eq"
  | Neq -> "neq"

let interp_term_bin_op op =
  match op with
  | Badd -> "add_int"
  | Bsub -> "sub_int"
  | Bmul -> "mul_int"
  | _ -> assert false (* TODO *)

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
	  with Failure "int_of_string" -> assert false (* TODO *)
	end  
    | Tvar { var_name = v ; var_is_assigned = true } -> 
	interp_var label v
    | Tvar { var_name = v ; var_is_assigned = false } -> 
	LVar v
    | Told t ->	interp_term (Some old_label) old_label t
    | Tbinop (t1, op, t2) ->
	LApp(interp_term_bin_op op,[f t1;f t2])
    | Tblock_length t -> 
	LApp("block_length",[f t])
    | Tat (t, l) -> 
	interp_term (Some l) old_label t
    | Tif (_, _, _) -> assert false (* TODO *)
    | Tarrget (t1, t2) -> 
	let te1 = f t1 and te2 = f t2 in
	let var = global_var_for_type t.term_type in
	LApp("acc",[interp_var label var;LApp("shift",[te1;te2])])
    | Tarrow (t, field) -> 
	let te = f t in
	let var = field in
	LApp("acc",[interp_var label var;te])
    | Tdot (_, _) -> 
	assert false (* TODO *)
    | Tunop (Ustar, t1) -> 
	let te1 = f t1 in
	let var = global_var_for_type t.term_type in
	LApp("acc",[interp_var label var;te1])
    | Tunop (_, _) -> 
	assert false (* TODO *)
    | Tapp (g, l) -> 
	LApp(g.logic_name,
	     (HeapVarSet.fold (fun x acc -> (interp_var label x)::acc) 
		g.logic_args []) 
	     @ List.map f l)
    | Tnull -> LVar "null"
    | Tresult -> LVar "result"
    | Tcast (ty, t) -> assert false (* TODO *)


let rec interp_predicate label old_label p =
  let f = interp_predicate label old_label in
  let ft = interp_term label old_label in
  match p with
    | Ptrue -> LTrue
    | Pexists (_, _) -> assert false (* TODO *)
    | Pforall (l, p) ->
	List.fold_right
	  (fun (t,x) p -> LForall(x,([],Ceffect.interp_type t),p))
	  l (interp_predicate label old_label p)
    | Pif (_, _, _)
    | Pnot _ -> assert false (* TODO *)
    | Pimplies (p1, p2) -> make_impl (f p1) (f p2)
    | Por (p1, p2) -> make_or (f p1) (f p2)
    | Pand (p1, p2) -> make_and (f p1) (f p2)
    | Prel (t1, op, t2) ->
	LPred(interp_rel op,[ft t1;ft t2])
    | Papp (v, tl) ->
	LPred(v.logic_name, 
	      (HeapVarSet.fold (fun x acc -> (interp_var label x)::acc) 
		 v.logic_args []) 
	      @ List.map ft tl)
    | Pfalse -> LFalse
    | Pold p -> interp_predicate (Some old_label) old_label p
    | Pat (p, l) -> interp_predicate (Some l) old_label p
    | Pfresh (t) ->
	LPred("fresh",[interp_var label "alloc"; ft t])
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

let interp_bin_op op =
  match op with
  | Badd_int -> "add_int"
  | Bsub_int -> "sub_int"
  | Bmul_int -> "mul_int"
  | Blt -> "lt_int"
  | Bgt -> "gt_int"
  | Ble -> "le_int"
  | Bge -> "ge_int"
  | Beq -> "eq_int"
  | Bneq -> "neq_int" 
  | _ -> assert false (* TODO *)

let interp_incr_op op =
  match op with
    | Upostfix_inc | Uprefix_inc -> "add_int"
    | Upostfix_dec | Uprefix_dec -> "sub_int"


let one = Cte(Prim_int 1)

type interp_lvalue =
  | LocalRef of Info.var_info
  | HeapRef of string * Output.expr

let tempvar_count = ref 0;;

let build_complex_app e args =
  let rec build n e args =
    match args with
      | [] -> e
      | [p] -> App(e,p)
      | ((Var _) | (Cte _) as p)::l ->
	  build n (App(e,p)) l
      | p::l ->
	  incr tempvar_count;
	  let v = "caduceus"^(string_of_int !tempvar_count) in
	  Let(v,p,
	    build (succ n) (App(e,Var(v))) l)
  in
  match args with
    | [] -> App(e,Void)
    | _ -> build 1 e args

(*
let is_pure e =
  match e with
    | 
let rec build_app1 e args =
  if List.for_all is_pure args then
    List.fold_left (fun acc x -> App(acc,x)) e args
  else
    build_complex_app e args

and build_app e args =
  match args with
    | [] -> App(e,Void)
    | _ -> build_app1 e args
*)



let rec interp_expr e =
  match e.texpr_node with
    | TEconstant(c) -> 
	begin
	  try
	    Cte(Prim_int(int_of_string c))
	  with Failure "int_of_string" -> assert false (* TODO *)
	end
    | TEvar(v) -> 
        if v.var_name = "t"
	then begin
	  Loc.report Coptions.log e.texpr_loc;
	  lprintf "translating var t: is_assigned = %b@."
	    v.var_is_assigned;
	end;
	if v.var_is_assigned then Deref(v.var_name) else Var(v.var_name)
    | TEbinary(_,(Blt | Bgt | Ble | Bge | Beq | Bneq | Band | Bor),_) 
    | TEunary (Unot, _) ->
	If(interp_boolean_expr e, Cte(Prim_int(1)), Cte(Prim_int(0)))
    | TEbinary(e1,op,e2) ->
	build_complex_app (Var (interp_bin_op op))
	  [interp_expr e1;interp_expr e2]
    | TEarrget(e1,e2) ->
	let te1 = interp_expr e1 and te2 = interp_expr e2 in
	let var = global_var_for_type e.texpr_type in
	App(App(Var("acc_"),Var(var)),App(App(Var("shift_"),te1),te2))
    | TEassign (e1,e2) ->
	assert false (* TODO *)
    | TEincr(op,e) -> interp_incr_expr op e
    | TEassign_op(e1,op,e2) ->
	assert false (* TODO *)
    | TEseq(e1,e2) ->
	assert false (* TODO *)
    | TEnop -> 
	assert false (* TODO *)
    | TEcond(e1,e2,e3) ->
	If(interp_boolean_expr e1,interp_expr e2,interp_expr e3)
    | TEstring_literal s -> assert false (* TODO *)
    | TEdot(e,s) -> assert false (* TODO *)
    | TEarrow(e,s) ->
	let te = interp_expr e in
	let var = s in
	Output.make_app "acc_" [Var(var);te]
    | TEunary(Ustar,e1) -> 
	let te1 = interp_expr e1 in
	let var = global_var_for_type e.texpr_type in
	make_app "acc_" [Var var;te1]
    | TEunary(_,_) -> assert false (* TODO *)	
    | TEcall(e,args) -> 
	begin
	  match e.texpr_node with
	    | TEvar v ->
		let targs = match args with
		  | [] -> [Output.Var "void"]
		  | _ -> List.map interp_expr args
		in
		make_app (v.var_name ^ "_parameter") targs
	    | _ -> assert false
	end
    | TEcast(t,e)
      -> assert false (* TODO *)
    | TEsizeof_expr(e)
      -> assert false (* TODO *)
    | TEsizeof(t)
      -> assert false (* TODO *)

and interp_boolean_expr e =
  match e.texpr_node with
    | TEbinary(e1, (Blt | Bgt | Ble | Bge | Beq | Bneq as op), e2) ->
	build_complex_app (Var (interp_bin_op op))
	  [interp_expr e1;interp_expr e2]
    | TEbinary (e1, Band, e2) ->
	And(interp_boolean_expr e1, interp_boolean_expr e2)
    | TEbinary (e1, Bor, e2) ->
	Or(interp_boolean_expr e1, interp_boolean_expr e2)
    | TEunary (Unot, e) ->
	Not(interp_boolean_expr e)
    (* otherwise e <> 0 *)
    | _ -> build_complex_app (Var "neq_int") [interp_expr e; Cte(Prim_int(0))]

and interp_incr_expr op e =
  match interp_lvalue e with
    | LocalRef v ->
	begin
	  match op with
	    | Upostfix_dec | Upostfix_inc ->
		(* let tmp = !v in v:= op tmp 1; tmp *)
		Let("caduceus",Deref(v.var_name),
		    append 
		      (Assign(v.var_name,
			      make_app (interp_incr_op op)
				[Var "caduceus";one]))
		      (Var "caduceus"))
	    | Uprefix_dec | Uprefix_inc ->
		(* v := op !v 1; !v *)
		append 
		  (Assign(v.var_name,
			App(App(Var(interp_incr_op op),Deref(v.var_name)),
			    one)))
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
			      make_app (interp_incr_op op) 
				[one;Var "caduceus2"]])
			  (Var "caduceus2")))
	    | Uprefix_dec | Uprefix_inc ->
		(* let tmp1 = e' in
		   let tmp2 = (acc var tmp1)+1 in
		   upd var tmp1 tmp2; tmp2 *)
		Let("caduceus1",e',
		    Let("caduceus2",
			make_app (interp_incr_op op)
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
    | TEdot(e1,f) ->
	assert false
    | TEarrow(e1,f) ->
	HeapRef(f,interp_expr e1)
    | _ -> assert false (* wrong typing of lvalue ??? *)
	  

let interp_spec s =
  let tpre = interp_predicate_opt None "" s.requires
  and tpost = interp_predicate_opt None "" s.ensures
  in (tpre,tpost)




let interp_decl d acc = 
  match d.node with 
    | Tdecl(ctype,v,init) -> 
	lprintf 
	  "translating local declaration of %s@." v.var_name;
	let tinit =
	  match init with 
	    | Inothing ->
(*
		if ctype = c_int then TODO
*)
		  App(Var("any_int"),Var("void"))
	    | Iexpr e -> interp_expr e		
	    | Ilist _ -> assert false (* TODO *)
	in
	if v.var_is_assigned then
	  Let_ref(v.var_name,tinit,acc)
	else
	  Let(v.var_name,tinit,acc)
    | _ -> assert false (* TODO *)

let rec interp_statement_expr e =
  match e.texpr_node with
    | TEseq(e1,e2) ->
	append (interp_statement_expr e1) (interp_statement_expr e2)
    | TEnop -> 
	assert false (* TODO *)
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
	begin
	  match interp_lvalue e with
	    | LocalRef v ->
		Assign(v.var_name,
		       make_app (interp_incr_op op) [Deref(v.var_name); one])
	    | HeapRef(var,e1) -> 
		(* let tmp1 = e1 in
		   upd var tmp1 (op tmp1 1) *)
		Let("caduceus1",e1,
		    make_app "upd_"
		      [Var var; Var "caduceus1"; 
		       make_app (interp_incr_op op) [Var "caduceus1"; one]])
	end
    | TEsizeof _ -> assert false (* TODO *)
    | TEsizeof_expr _ -> assert false (* TODO *)
    | TEcast (_, _) -> assert false (* TODO *)
    | TEcond (_, _, _) -> assert false (* TODO *)
    | TEcall (e,args) -> 
	begin
	  match e.texpr_node with
	    | TEvar v ->
		make_app v.var_name (List.map interp_expr args)
	    | _ -> assert false
	end
    | TEbinary (_, _, _) -> assert false (* TODO *)
    | TEunary (_, _) -> assert false (* TODO *)
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
    | TEarrget (_, _) -> assert false (* TODO *)
    | TEarrow (_, _) -> assert false (* TODO *)
    | TEdot (_, _) -> assert false (* TODO *)
    | TEvar _ -> assert false (* TODO *)
    | TEstring_literal _ -> assert false (* TODO *)
    | TEconstant _ -> assert false (* TODO *)

let interp_invariant annot =
  match annot with
    | { invariant = None; variant = None } -> 
	(LTrue,LConst (Prim_int 0))
    | { invariant = Some inv; variant = Some (var,_) } -> 
	(interp_predicate None "init" inv,interp_term None "" var)
    | _ -> 
	assert false (* TODO *)

let try_with_void ex e = Try (e, ex, None, Void)  

let break b e = if b then try_with_void "Break" e else e

let continue b e = if b then try_with_void "Continue" e else e    

let rec interp_statement stat = match stat.st_node with
  | TSnop -> 
      Void
  | TSexpr e ->
      interp_statement_expr e
  | TSreturn eopt ->
      (* TODO: abrupt return *)
      begin
	match eopt with
	  | None -> Void
	  | Some e -> interp_expr e
      end
  | TSfor(annot,e1,e2,e3,body) ->
      let (inv,dec) = interp_invariant annot in
      append
	(interp_statement_expr e1)
	(break stat.st_break 
	   (make_while (interp_expr e2) inv dec 
	      (continue stat.st_continue
		 (append 
		    (interp_statement body) 
		    (interp_statement_expr e3)))))
  | TSif(e,s1,s2) -> 
      If(interp_boolean_expr e,interp_statement s1,interp_statement s2)
  | TSwhile(annot,e,s) -> 
      let (inv,dec) = interp_invariant annot in
      make_while (interp_expr e) inv dec (interp_statement s)
  | TSdowhile(annot,s,e) -> 
      assert false (* TODO *)
  | TSblock(b) -> 
      interp_block b 
  | TSbreak -> 
      Raise ("Break", None)
  | TScontinue -> 
      Raise ("Continue", None)
  | TSlabel(lab,s) -> 
      append (Output.Label lab) (interp_statement s)
  | TSswitch(e,s) -> 
      assert false (* TODO *)
  | TScase(e,s) -> 
      assert false (* TODO *)
  | TSgoto(lab) -> 
      assert false (* TODO *)
  | TSassert(pred) -> 
      Output.Assert(interp_predicate None "init" pred)
  | TSlogic_label(l) -> 
      assert false (* TODO *)
  | TSspec (spec,s) ->
      let (pre,post) = interp_spec spec in
      Triple(pre,interp_statement s,post,None)

and interp_block (decls,stats) =
  let b = 
    List.fold_right 
      (fun s acc -> append (interp_statement s) acc) stats Void in
  List.fold_right interp_decl decls b 

let no_spec = 
  { requires = None; 
    assigns = []; 
    ensures = None; 
    decreases = None }

let interp_spec_option = function
  | None -> interp_spec no_spec
  | Some s -> interp_spec s

let cinterp_logic_symbol id ls =
  match ls with
    | Predicate_reads(args,locs) -> assert false (* TODO *)
    | Predicate_def(args,p) -> 
	let a = interp_predicate None "" p
	and e = Ceffect.predicate p in
	let args =
	  List.fold_right
	    (fun (id,t) args -> (id,([],Ceffect.interp_type t))::args)
	    args []
	in
	let args =
	  HeapVarSet.fold
	  (fun arg t -> (arg,Ceffect.heap_var_type arg)::t)
	    e args
	in
	Predicate(false,id.logic_name,args,a)
    | Function(args,ret,_) ->
	let local_type =
	  List.fold_right
	    (fun (id,ty) t -> Prod_type(id,base_type (Ceffect.interp_type ty),t))
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

let interp_fun_params params =
  if params=[]
  then ["tt",unit_type]
  else List.map interp_param params 

let interp_function_spec id sp ty pl =
  let tpl = interp_fun_params pl in
  let pre,post = interp_spec_option sp in
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

let interp_located_tdecl ((why_code,why_spec,prover_decl) as why) decl =
  match decl.node with
  | Tlogic(id,ltype) -> 
      lprintf 
      "translating logic declaration of %s@." id.logic_name;
      (why_code, cinterp_logic_symbol id ltype::why_spec,
       prover_decl)
  | Taxiom(id,p) -> 
      lprintf 
      "translating axiom declaration %s@." id;      
      let a = interp_axiom p in
      (why_code, Axiom(id,a)::why_spec, prover_decl)
  | Ttypedef(ctype,id) -> 
      why
  | Ttypedecl(ctype) -> 
      assert false (* TODO *)
  | Tdecl(ctype,v,init) -> 
      lprintf 
        "translating global declaration of %s@." v.var_name;
      let t = base_type (Ceffect.interp_type ctype) in
      begin
	match init with 
	  | Inothing ->
	      (why_code,
	       (Param(false,v.var_name,Ref_type(t)))::why_spec,
	       prover_decl)
	  | _ -> 
	      assert false (* TODO *)
      end
  | Tfunspec(spec,ctype,id,params) -> 
      (why_code, interp_function_spec id (Some spec) ctype params :: why_spec,
       prover_decl)
  | Tfundef(spec,ctype,id,params,block) ->      
      lprintf "translating function %s@." id.var_name;
      let tparams = interp_fun_params params in
      let pre,post = interp_spec_option spec in
      let tblock = interp_statement block in
      ((Def(id.var_name,Fun(tparams,pre,tblock,post,None)))::why_code,
       interp_function_spec id spec ctype params :: why_spec,
       prover_decl)


let interp l =
  List.fold_left interp_located_tdecl ([],[],[]) l

