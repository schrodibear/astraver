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

(*i $Id: cinterp.ml,v 1.19 2004-03-02 15:13:53 filliatr Exp $ i*)


open Format
open Output
open Info
open Cast


let global_var_for_type t =
  match t.ctype_node with
    | CTint _ -> "intP"
    | _ -> assert false (* TODO *)

let interp_param (t,id) =
  (* TODO : tester si param is assigned *)
  (id,base_type (Ceffect.interp_type t))

let interp_rel = function
  | Clogic.Lt -> "lt_int"
  | Clogic.Gt -> "gt_int"
  | Clogic.Le -> "le_int"
  | Clogic.Ge -> "ge_int"
  | Clogic.Eq -> "eq"
  | Clogic.Neq -> "neq"

let interp_term_bin_op op =
  match op with
  | Clogic.Badd -> "add_int"
  | Clogic.Bsub -> "sub_int"
  | Clogic.Bmul -> "mul_int"
  | _ -> assert false (* TODO *)

let rec interp_term label old_label t =
  let f = interp_term label old_label in
  match t.Clogic.term_node with
    | Clogic.Tconstant c ->
	begin
	  try
	    LConst(Prim_int(int_of_string c))
	  with Failure "int_of_string" -> assert false (* TODO *)
	end  
    | Clogic.Tvar { var_name = v ; var_is_assigned = true } -> 
	(match label with None -> LVar v 
	   | Some l -> LVarAtLabel(v,l))
    | Clogic.Tvar { var_name = v ; var_is_assigned = false } -> 
	LVar v
    | Clogic.Told t ->	interp_term (Some old_label) old_label t
    | Clogic.Tbinop (t1, op, t2) ->
	LApp(interp_term_bin_op op,[f t1;f t2])
    | Clogic.Tlength t -> 
	LApp("length",[f t])
    | Clogic.Tat (t, l) -> 
	interp_term (Some l) old_label t
    | Clogic.Tif (_, _, _) -> assert false (* TODO *)
    | Clogic.Tarrget (t1, t2) -> 
	let te1 = f t1 and te2 = f t2 in
	let var = global_var_for_type t.Clogic.term_type in
	LApp("acc",[LVar var;LApp("shift",[te1;te2])])

    | Clogic.Tarrow (_, _) -> assert false (* TODO *)
    | Clogic.Tdot (_, _) -> assert false (* TODO *)
    | Clogic.Tunop (_, _) -> assert false (* TODO *)
    | Clogic.Tapp (g, l) -> 
	LApp(g.logic_name,
	     (List.map (fun (x,_) -> LVar x) g.logic_args) @ List.map f l)
    | Clogic.Tnull -> LVar "null"
    | Clogic.Tresult -> LVar "result"
    | Clogic.Tcast (ty, t) -> assert false (* TODO *)


let rec interp_predicate label old_label p =
  let f = interp_predicate label old_label in
  let ft = interp_term label old_label in
  match p with
    | Clogic.Ptrue -> LTrue
    | Clogic.Pexists (_, _) -> assert false (* TODO *)
    | Clogic.Pforall (l, p) ->
	List.fold_right
	  (fun (t,x) p -> LForall(x,([],Ceffect.interp_type t),p))
	  l (interp_predicate label old_label p)
    | Clogic.Pif (_, _, _)
    | Clogic.Pnot _ -> assert false (* TODO *)
    | Clogic.Pimplies (p1, p2) -> make_impl (f p1) (f p2)
    | Clogic.Por (p1, p2) -> make_or (f p1) (f p2)
    | Clogic.Pand (p1, p2) -> make_and (f p1) (f p2)
    | Clogic.Prel (t1, op, t2) ->
	LPred(interp_rel op,[ft t1;ft t2])
    | Clogic.Papp (_, _)
    | Clogic.Pfalse -> LFalse
    | Clogic.Pvalid (t,a,b) ->
	LPred("valid",[ft t;ft a;ft b])

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
  | Beq -> "eq"
  | Bneq -> "neq" 
  | _ -> assert false (* TODO *)

let interp_incr_op op =
  match op with
    | Upostfix_inc | Uprefix_inc -> "add_int"
    | Upostfix_dec | Uprefix_dec -> "sub_int"


let rec interp_expr e =
  match e.texpr_node with
    | TEconstant(c) -> 
	begin
	  try
	    Cte(Prim_int(int_of_string c))
	  with Failure "int_of_string" -> assert false (* TODO *)
	end
    | TEvar(v) -> 
	if v.var_is_assigned then Deref(v.var_name) else Var(v.var_name)
    | TEbinary(e1,op,e2) ->
	App(App(Var(interp_bin_op op),interp_expr e1),interp_expr e2)
    | TEarrget(e1,e2) ->
	let te1 = interp_expr e1 and te2 = interp_expr e2 in
	let var = global_var_for_type e.texpr_type in
	App(App(Var("acc_"),Var(var)),App(App(Var("shift_"),te1),te2))
    | TEassign (e1,e2) ->
	assert false (* TODO *)
	(*begin
	  match op with
	    | Aequal ->
		begin
		  match e1.texpr_node with
		    | TEvar(v) ->
			Assign(v.var_name,interp_expr e2)
		    | _ -> assert false (* TODO *)
		end
	    | _ -> assert false (* TODO *)
	end*)	
    | TEincr(op,e) -> interp_incr_expr op e
    | TEassign_op(e1,op,e2) ->
	assert false (* TODO *)
    | TEseq(e1,e2) ->
	assert false (* TODO *)
    | TEnop -> 
	assert false (* TODO *)
    | TEcond(e1,e2,e3) ->
	If(interp_expr e1,interp_expr e2,interp_expr e3)
    | TEstring_literal s
	-> assert false (* TODO *)
    | TEdot(e,s)
      -> assert false (* TODO *)
    | TEarrow(e,s)
      -> assert false (* TODO *)
    | TEunary(op,e)
      -> assert false (* TODO *)
    | TEcall(e,args)
      -> assert false (* TODO *)
    | TEcast(t,e)
      -> assert false (* TODO *)
    | TEsizeof_expr(e)
      -> assert false (* TODO *)
    | TEsizeof(t)
      -> assert false (* TODO *)

and interp_incr_expr op e =
  match e.texpr_node with
    | TEvar v ->
	begin
	  match op with
	    | Upostfix_dec | Upostfix_inc ->
		assert false (* TODO *)
	    | Uprefix_dec | Uprefix_inc ->
		append 
		(Assign(v.var_name,
			App(App(Var(interp_incr_op op),Deref(v.var_name)),
			    Cte(Prim_int 1))))
		(Deref v.var_name)
	end
    | TEunary(Ustar,e') ->
	begin
	  match e'.texpr_node with
	    | TEvar v ->
		begin
		  match op with
		    | Upostfix_dec | Upostfix_inc ->
			(* let tmp = (acc intP v) in
			   upd intP v (tmp+1); tmp *)
			assert false (* TODO *)
		    | Uprefix_dec | Uprefix_inc ->
			(* let tmp = (acc intP v)+1 in
			   upd intP v tmp; tmp *)
			assert false (* TODO *)
		end		      
	    | _ -> assert false (* TODO *)
	end
    | _ -> assert false (* TODO *)





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


let interp_decl d acc = 
  match d.node with 
    | Tdecl(ctype,v,init) -> 
	fprintf Coptions.log 
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
	  match l.texpr_node with
	    | TEvar(v) ->
		Assign(v.var_name,interp_expr e)
	    | TEarrget(e1,e2) ->
		(* P := (upd !P (shift e1 e2) e) *)
		let var = global_var_for_type e.texpr_type in
		(build_complex_app (Var "upd_")
		   [Var var;
		    build_complex_app (Var "shift_")
		      [interp_expr e1; interp_expr e2];
		    interp_expr e])
	    | _ -> assert false (* TODO *)
	end 
    | TEincr(op,e) ->
	begin
	  match e.texpr_node with
	    | TEvar v ->
		Assign(v.var_name,
			App(App(Var(interp_incr_op op),Deref(v.var_name)),
			    Cte(Prim_int 1)))
	    | _ -> assert false (* TODO *)
	end
    | TEsizeof _ -> assert false (* TODO *)
    | TEsizeof_expr _ -> assert false (* TODO *)
    | TEcast (_, _) -> assert false (* TODO *)
    | TEcond (_, _, _) -> assert false (* TODO *)
    | TEcall (_, _) -> assert false (* TODO *)
    | TEbinary (_, _, _) -> assert false (* TODO *)
    | TEunary (_, _) -> assert false (* TODO *)
    | TEassign_op (l, op, e) -> assert false (* TODO *)
    | TEarrget (_, _) -> assert false (* TODO *)
    | TEarrow (_, _) -> assert false (* TODO *)
    | TEdot (_, _) -> assert false (* TODO *)
    | TEvar _ -> assert false (* TODO *)
    | TEstring_literal _ -> assert false (* TODO *)
    | TEconstant _ -> assert false (* TODO *)

let rec interp_statement stat =
  match stat.st_node with
    | TSexpr e ->
	interp_statement_expr e
    | TSreturn eopt ->
	(* TODO: abrupt return *)
	begin
	  match eopt with
	    | None -> Void
	    | Some e -> interp_expr e
	end
    | TSfor(annot,e1,e2,e3,body,info) ->
	let (inv,dec) =
	  match annot with
	    | { Clogic.invariant = None; Clogic.variant = None } -> 
		(LTrue,LConst (Prim_int 0))
	    | { Clogic.invariant = Some inv; Clogic.variant = Some (var,_) } -> 
		(interp_predicate None "init" inv,interp_term None "" var)
	    | _ -> 
		assert false (* TODO *)
	in
	append
	  (interp_statement_expr e1)
	  (make_while (interp_expr e2) inv dec 
	     (append 
		(interp_statement body) 
		(interp_statement_expr e3)))
  | TSnop
      -> assert false (* TODO *)
  | TSif(e,s1,s2)
      -> assert false (* TODO *)
  | TSwhile(e,s,info,annot)
      -> assert false (* TODO *)
  | TSdowhile(s,e,info,annot)
      -> assert false (* TODO *)
  | TSblock(b) -> 
      interp_block b 
  | TSbreak
      -> assert false (* TODO *)
  | TScontinue
      -> assert false (* TODO *)
  | TSlabel(lab,s)
      -> append (Output.Label lab) (interp_statement s)
  | TSswitch(e,s)
      -> assert false (* TODO *)
  | TScase(e,s)
      -> assert false (* TODO *)
  | TSgoto(lab)
      -> assert false (* TODO *)
  | TSassert(pred)
      -> assert false (* TODO *)
  | TSlogic_label(l)
      -> assert false (* TODO *)

and interp_block (decls,stats) =
  let b = 
    List.fold_right 
      (fun s acc -> append (interp_statement s) acc) stats Void in
  List.fold_right interp_decl decls b 

let interp_spec s =
  let tpre = interp_predicate_opt None "" s.Clogic.requires
  and tpost = interp_predicate_opt None "" s.Clogic.ensures
  in (tpre,tpost)

let no_spec = 
  { Clogic.requires = None; 
    Clogic.assigns = []; 
    Clogic.ensures = None; 
    Clogic.decreases = None }

let interp_spec_option = function
  | None -> interp_spec no_spec
  | Some s -> interp_spec s

let cinterp_logic_symbol id ls =
  match ls with
    | Clogic.Predicate_reads(args,locs) -> assert false (* TODO *)
    | Clogic.Predicate_def(args,pred) -> assert false (* TODO *)
    | Clogic.Function(args,ret,_) ->
	let local_type =
	  List.fold_right
	    (fun arg t -> Prod_type("",base_type (Ceffect.interp_type arg),t))
	    args (base_type (Ceffect.interp_type ret))
	in
	List.fold_right
	  (fun (arg,ty) t -> Prod_type("",Base_type ty,t))
	  id.logic_args local_type



let interp_located_tdecl (why_decls,prover_decl) decl =
  match decl.node with
  | Tlogic(id,ltype) -> 
      fprintf Coptions.log 
      "translating logic declaration of %s@." id.logic_name;
      ((Logic(id.logic_name,cinterp_logic_symbol id ltype))::why_decls,
       prover_decl)
  | Taxiom(id,p) -> 
      fprintf Coptions.log 
      "translating axiom declaration %s@." id;
      ((Axiom(id,interp_predicate None "" p))::why_decls,
       prover_decl)
  | Ttypedef(ctype,id) -> assert false (* TODO *)
  | Ttypedecl(ctype) -> assert false (* TODO *)
  | Tdecl(ctype,v,init) -> 
      fprintf Coptions.log 
        "translating global declaration of %s@." v.var_name;
      let t = base_type (Ceffect.interp_type ctype) in
      begin
	match init with 
	  | Inothing ->
	      ((Param(v.var_name,Ref_type(t)))::why_decls,prover_decl)
	  | _ -> assert false (* TODO *)
      end
  | Tfunspec(spec,ctype,id,params) -> assert false (* TODO *)
  | Tfundef(spec,ctype,id,params,block,info) ->      
      fprintf Coptions.log "translating function %s@." id;
      let tparams = List.map interp_param params in
      let pre,post = interp_spec_option spec in
      let tblock = interp_block block in
      ((Def(id,Fun(tparams,pre,tblock,post,None)))::why_decls,
       prover_decl)


let interp l =
  List.fold_left interp_located_tdecl ([],[]) l


