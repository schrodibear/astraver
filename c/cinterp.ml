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

(*i $Id: cinterp.ml,v 1.46 2004-03-23 09:44:08 marche Exp $ i*)


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
    | Pexists (l, p) -> 
	List.fold_right
	  (fun (t,x) p -> LExists(x,([],Ceffect.interp_type t),p)) l (f p)
    | Pforall (l, p) ->
	List.fold_right
	  (fun (t,x) p -> LForall(x,([],Ceffect.interp_type t),p))
	  l (interp_predicate label old_label p)
    | Pif (_, _, _) -> assert false (* TODO *)
    | Pnot p -> LNot (f p)
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
  | Blt_int -> "lt_int"
  | Bgt_int -> "gt_int"
  | Ble_int -> "le_int"
  | Bge_int -> "ge_int"
  | Beq_int -> "eq_int"
  | Bneq_int -> "neq_int" 
  | Blt_float -> "lt_float"
  | Bgt_float -> "gt_float"
  | Ble_float -> "le_float"
  | Bge_float -> "ge_float"
  | Beq_float -> "eq_float"
  | Bneq_float -> "neq_float" 
  | Blt_pointer -> "lt_pointer"
  | Bgt_pointer -> "gt_pointer"
  | Ble_pointer -> "le_pointer"
  | Bge_pointer -> "ge_pointer"
  | Beq_pointer -> "eq_pointer"
  | Bneq_pointer -> "neq_pointer" 
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
    | TEbinary(_,(Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		 |Blt_float | Bgt_float | Ble_float | Bge_float 
		 |Beq_float | Bneq_float 
		 |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		 |Beq_pointer | Bneq_pointer 
		 |Blt | Bgt | Ble | Bge | Beq | Bneq | Band | Bor),_) 
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
		build_complex_app (Var (v.var_name ^ "_parameter")) targs
	    | _ -> assert false
	end
    | TEcast({ctype_node = CTpointer {ctype_node = CTvoid}}, 
	     {texpr_node = TEconstant "0"}) ->
	Var "null"
    | TEcast(t,e) -> 
	assert false (* TODO *)
    | TEsizeof_expr(e) -> 
	assert false (* TODO *)
    | TEsizeof(t) -> 
	assert false (* TODO *)

and interp_boolean_expr e =
  match e.texpr_node with
    | TEbinary(e1, (Blt_int | Bgt_int | Ble_int | Bge_int | Beq_int | Bneq_int 
		   |Blt_float | Bgt_float | Ble_float | Bge_float 
		   |Beq_float | Bneq_float 
		   |Blt_pointer | Bgt_pointer | Ble_pointer | Bge_pointer 
		   |Beq_pointer | Bneq_pointer 
		   |Blt | Bgt | Ble | Bge | Beq | Bneq as op), e2) ->
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
	  


module StringMap = Map.Make(String)

let collect_locations acc loc =
  match loc with
    | Lterm t -> 
	begin
	  match t.term_node with
	    | Tarrow(e,f) ->
		let loc = LApp("pointer_loc",[interp_term (Some "") "" e]) in
		begin
		  try
		    let p = StringMap.find f acc in
		    StringMap.add f (LApp("union_loc",[loc;p])) acc
		  with
		      Not_found -> StringMap.add f loc acc
		end
	    | _ -> assert false (* TODO *)
	end
    | Lstar t -> assert false (* TODO *)
    | Lrange(t1,t2,t3) -> assert false (* TODO *)


let interp_assigns locl =
  let l = List.fold_left collect_locations StringMap.empty locl in
  StringMap.fold
    (fun v p acc ->
       make_and acc
	 (LPred("assigns",
		[LVarAtLabel("alloc",""); LVarAtLabel(v,"");LVar v; p])))
    l LTrue

	 


let interp_spec s =
  let tpre = interp_predicate_opt None "" s.requires
  and tpost = 
    make_and
      (interp_predicate_opt None "" s.ensures)
      (interp_assigns s.assigns)
  in (tpre,tpost)




let interp_decl d acc = 
  match d.node with 
    | Tdecl(ctype,v,init) -> 
	lprintf 
	  "translating local declaration of %s@." v.var_name;
	let tinit =
	  match init with 
	    | Inothing ->
		begin match ctype.ctype_node with
		  | CTint _ -> App(Var("any_int"),Var("void"))
		  | CTfloat _ -> App(Var("any_float"),Var("void"))
		  | CTfun _ -> assert false (* TODO *)
		  | _ -> App(Var("any_pointer"),Var("void"))
		end
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
		let targs = match args with
		  | [] -> [Output.Var "void"]
		  | _ -> List.map interp_expr args
		in
		build_complex_app (Var v.var_name) targs
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

let return_exn ty = match ty.ctype_node with
  | CTint _ -> "Return_int"
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

let no_spec = 
  { requires = None; 
    assigns = []; 
    ensures = None; 
    decreases = None }

let interp_spec_option = function
  | None -> interp_spec no_spec
  | Some s -> interp_spec s

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
  let pre,post = interp_spec_option sp in
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
	      why
	      (*** already done when translating heap variables
	      (why_code,
	       (Param(false,v.var_name,Ref_type(t)))::why_spec,
	       prover_decl)
              ***)
	  | _ -> 
	      assert false (* TODO *)
      end
  | Tfunspec(spec,ctype,id,params) -> 
      (why_code, interp_function_spec id (Some spec) ctype params :: why_spec,
       prover_decl)
  | Tfundef(spec,ctype,id,params,block) ->      
      lprintf "translating function %s@." id.var_name;
      let pre,post = interp_spec_option spec in
      let pre,tparams = interp_fun_params pre params in
      abrupt_return := None;
      let tblock = catch_return (interp_statement false block) in
      ((Def(id.var_name,Fun(tparams,pre,tblock,post,None)))::why_code,
       interp_function_spec id spec ctype params :: why_spec,
       prover_decl)


let interp l =
  List.fold_left interp_located_tdecl ([],[],[]) l

