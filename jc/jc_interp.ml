(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Output


let const c =
  match c with
    | JCCnull -> assert false
    | JCCreal s -> Prim_real s
    | JCCinteger s -> Prim_int s
    | JCCboolean b -> Prim_bool b

let tr_native_type t =
  match t with
    | Tunit -> "unit"
    | Tboolean -> "bool"
    | Tinteger -> "int"
    | Treal -> "real"

let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }
  
let tr_base_type t =
  match t with
    | JCTnative t -> simple_logic_type (tr_native_type t)
    | JCTlogic s -> simple_logic_type s
    | JCTpointer (st, a, b) -> 
	let ti = simple_logic_type (st.jc_struct_info_root) in
	{ logic_type_name = "pointer";
	  logic_type_args = [ ti ] }

let tr_type t =
  match t with
    | JCTnative _ | JCTlogic _ -> Base_type(tr_base_type t)
    | JCTpointer _ -> Base_type(tr_base_type t)	

(**************************

terms and assertions 

*************************)

let lvar ?(assigned=true) label v =
  if assigned then
    match label with 
      | None -> LVar v 
      | Some l -> LVarAtLabel(v,l)
  else LVar v

let lvar_info label v = 
  lvar ~assigned:v.jc_var_info_assigned label v.jc_var_info_final_name

let logic_params li l =
  let l =
    FieldSet.fold
      (fun fi acc -> (LVar fi.jc_field_info_name)::acc)
      li.jc_logic_info_effects.jc_effect_memories
      l	    
  in
  StringSet.fold
    (fun v acc -> (LVar (v ^ "_alloc_table"))::acc)
    li.jc_logic_info_effects.jc_effect_alloc_table
    l	    

let make_logic_fun_call li l =
  let params = logic_params li l in
  LApp(li.jc_logic_info_name,params)

let make_logic_pred_call li l =
  let params = logic_params li l in
  LPred(li.jc_logic_info_name,params)

let rec term label oldlabel t =
  let ft = term label oldlabel in
  match t.jc_term_node with
    | JCTconst JCCnull -> LVar "null"
    | JCTvar v -> lvar_info label v
    | JCTconst c -> LConst(const c)
    | JCTshift(t1,t2) -> LApp("shift",[ft t1; ft t2])
    | JCTif(t1,t2,t3) -> assert false (* TODO *)
    | JCTderef(t,f) -> LApp("select",[lvar label f.jc_field_info_name;ft t])
    | JCTapp(f,l) -> make_logic_fun_call f (List.map ft l)	    
    | JCTold(t) -> term (Some oldlabel) oldlabel t
    | JCToffset_max(t) -> 
	assert false
	  (* LApp("offset_max",[alloc; ft t]) *)
    | JCToffset_min(t) -> 
	assert false
	  (* LApp("offset_min",[ft t]) *)
    | JCTinstanceof(t,ty) ->
	let alloc = ty.jc_struct_info_root ^ "_alloc_table" in
	LApp("instanceof_bool",
	     [lvar label alloc; ft t;LVar ty.jc_struct_info_name])
    | JCTcast(t,ty) ->
	let alloc = ty.jc_struct_info_root ^ "_alloc_table" in
	LApp("downcast",
	     [lvar label alloc; ft t;LVar ty.jc_struct_info_name])

let rec assertion label oldlabel a =
  let fa = assertion label oldlabel 
  and ft = term label oldlabel
  in
  match a.jc_assertion_node with
    | JCAtrue -> LTrue
    | JCAfalse -> LFalse
    | JCAif(t1,p2,p3) -> LIf(ft t1,fa p2,fa p3)
    | JCAand l -> make_and_list (List.map fa l)
    | JCAimplies(a1,a2) -> make_impl (fa a1) (fa a2)
    | JCAiff(a1,a2) -> make_equiv (fa a1) (fa a2)
    | JCAnot(a) -> LNot(fa a)
    | JCAapp(f,l) -> 
	make_logic_pred_call f (List.map ft l)	    
    | JCAforall(v,p) -> 
	LForall(v.jc_var_info_final_name,
		tr_base_type v.jc_var_info_type,
		fa p)
    | JCAold a -> assertion (Some oldlabel) oldlabel a
    | JCAbool_term(t) -> 
	LPred("eq",[ft t;LConst(Prim_bool true)])
    | JCAinstanceof(t,ty) -> 
	let alloc = ty.jc_struct_info_root ^ "_alloc_table" in
	LPred("instanceof",
	      [lvar label alloc; ft t; LVar ty.jc_struct_info_name])

(****************************

logic functions

****************************)

let memory_type t v =
  { logic_type_name = "memory";
    logic_type_args = [t;v] }

let memory_field fi =
  memory_type 
    (simple_logic_type fi.jc_field_info_root)
    (tr_base_type fi.jc_field_info_type)
	 
let tr_logic_fun li ta acc =
  let params =
    List.map
      (fun vi ->
	 (vi.jc_var_info_final_name,
	   tr_base_type vi.jc_var_info_type))
      li.jc_logic_info_parameters
  in
  let params_reads =
    FieldSet.fold
      (fun fi acc -> 
	 (fi.jc_field_info_name, memory_field fi)::acc)
      li.jc_logic_info_effects.jc_effect_memories
      params
  in
  let params_reads =
    StringSet.fold
      (fun v acc -> 
	 let t = { logic_type_args = [simple_logic_type v];
		   logic_type_name = "alloc_table" }
	 in
	 (v ^ "_alloc_table", t)::acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      params_reads
  in
  let decl =
    match li.jc_logic_info_result_type,ta with
      | None,JCAssertion a -> 
	  let a = assertion None "" a in
	  Predicate(false,li.jc_logic_info_name,params_reads, a) 
      | Some ty,JCTerm t -> 
	  let ret = tr_base_type ty in
	  let t = term None "" t in
	  Function(false,li.jc_logic_info_name,params_reads, ret, t) 
      | _ -> assert false
  in decl :: acc
  
let tr_predicate li p acc =
  let params =
    List.map
      (fun vi ->
	 (vi.jc_var_info_final_name,
	   tr_base_type vi.jc_var_info_type))
      li.jc_logic_info_parameters
  in
  Predicate(false,li.jc_logic_info_name,params,
	    assertion None "" p) :: acc
  
(****************************

expressions and statements

****************************)

type interp_lvalue =
  | LocalRef of var_info
  | HeapRef of field_info * expr

let tempvar_count = ref 0
let reset_tmp_var () = tempvar_count := 0
let tmp_why_var () = incr tempvar_count; "jessie_" ^ string_of_int !tempvar_count

let const_un = Cte(Prim_int "1")

let incr_call op =
  match op with
    | Prefix_inc | Postfix_inc -> Jc_pervasives.add_int_.jc_fun_info_name
    | Prefix_dec | Postfix_dec -> Jc_pervasives.sub_int_.jc_fun_info_name

let make_acc fi e =
  make_app "acc_"
    [ Var (fi.jc_field_info_root ^ "_alloc_table") ;
      Var fi.jc_field_info_name ; e ]

let make_upd fi e1 e2 =
  make_app "upd_"
    [ Var (fi.jc_field_info_root ^ "_alloc_table") ;
      Var fi.jc_field_info_name ; e1 ; e2 ]
    

let rec expr e : (string * Output.expr) list * expr =
  match e.jc_expr_node with
    | JCEconst JCCnull -> [],Var "null"
    | JCEconst c -> [],Cte(const c)
    | JCEvar v ->
	if v.jc_var_info_assigned 
	then [],Deref v.jc_var_info_final_name
	else [],Var v.jc_var_info_final_name
    | JCEif(e1,e2,e3) -> 
	let l1,e1 = expr e1 in
	let l2,e2 = expr e2 in
	let l3,e3 = expr e3 in
	(l1@l2@l3),If(e1,e2,e3)
    | JCEshift(e1,e2) -> 
	let l1,e1 = expr e1 in
	let l2,e2 = expr e2 in
	(l1@l2,make_app "shift" [e1; e2])
    | JCEinstanceof(e,t) ->
	let l,e = expr e in
	let alloc = t.jc_struct_info_root ^ "_alloc_table" in
	l,make_app "instanceof_" [Deref alloc; e; Var t.jc_struct_info_name]
    | JCEcast(e,t) ->
	let l,e = expr e in
	let alloc = t.jc_struct_info_root ^ "_alloc_table" in
	l,make_app "downcast_" [Deref alloc; e; Var t.jc_struct_info_name]
    | JCEderef(e,f) -> 
	let l,e = expr e in
	l,make_acc f e
    | JCEincr_local(op, vi) -> assert false
    | JCEincr_heap _ -> assert false
    | JCEassign_local (vi, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_heap(e1,fi,e2) -> 
	let l1,e1 = expr e1 in
	let l2,e2 = expr e2 in
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	(l1@l2@[ (tmp1, e1) ; (tmp2, e2) ],
	 append
	   (make_upd fi (Var tmp1) (Var tmp2))
	   (Var tmp2)) 
    | JCEassign_op_local (vi, op, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_op_heap(e1,fi,op,e2) -> 
	let l1,e1 = expr e1 in
	let l2,e2 = expr e2 in
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	(l1@l2@[ (tmp1, e1) ; 
		 (tmp2, make_app op.jc_fun_info_name
		    [ make_acc fi (Var tmp1) ; e2 ]) ],
	 append
	   (make_app "safe_upd_"
	      [Var memory; Var tmp1; Var tmp2])
	   (Var tmp2)) 
    | JCEcall(f,l) -> 
	if f==Jc_pervasives.and_ then
	  begin
	    match l with
	      | [e1;e2] -> 
		  let l1,e1 = expr e1 in
		  let l2,e2 = expr e2 in
		  (l1@l2,And(e1,e2))
	      | _ -> assert false
	  end
	else
	  let l,el =
	    List.fold_right
	      (fun (l,e) (ll,el) -> (l@ll,e::el))
	      (List.map expr l)
	      ([],[])
	  in
	  l,make_app f.jc_fun_info_name el

let rec make_lets l e =
  match l with
    | [] -> e
    | (tmp,a)::l -> Let(tmp,a,make_lets l e)

let statement_expr e =
  match e.jc_expr_node with
    | JCEconst JCCnull -> assert false
    | JCEconst c -> assert false
    | JCEif(e1,e2,e3) -> assert false (* If(expr e1,expr e2,expr e3) *)
    | JCEvar v -> assert false
    | JCEshift(e1,e2) -> assert false
    | JCEderef(e,f) -> assert false
    | JCEinstanceof _ -> assert false
    | JCEcast _ -> assert false
    | JCEincr_local(op, vi) ->
	(* let tmp = !v in v <- tmp+-1 *)
	let tmp = tmp_why_var () in
	let v = vi.jc_var_info_name in
	Let(tmp, Deref(v), 
	    Assign(v,make_app (incr_call op) [Var tmp; const_un]))
    | JCEincr_heap _ -> assert false
    | JCEassign_local (vi, e2) -> 
	let l,e2 = expr e2 in
	let n = vi.jc_var_info_final_name in
	make_lets l (Assign(n, e2))
    | JCEassign_heap(e1,fi,e2) -> 
	let l1,e1 = expr e1 in
	let l2,e2 = expr e2 in
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	make_lets 
	  (l1@l2@[ (tmp1, e1) ; (tmp2, e2) ])
	  (make_upd fi (Var tmp1) (Var tmp2))
    | JCEassign_op_local (vi, op, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_op_heap(e1,fi,op,e2) -> 
	let l1,e1 = expr e1 in
	let l2,e2 = expr e2 in
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	make_lets 
	  (l1@l2@[ (tmp1, e1) ; 
		   (tmp2, make_app op.jc_fun_info_name
		      [ make_acc fi (Var tmp1) ; e2 ]) ])
	  (make_app "safe_upd_"
		  [Var memory; Var tmp1; Var tmp2])
    | JCEcall(f,l) -> 
	let l,el =
	  List.fold_right
	    (fun (l,e) (ll,el) -> (l@ll,e::el))
	    (List.map expr l)
	    ([],[])
	in
	make_lets l (make_app f.jc_fun_info_name el)

let invariant_for_struct this st =
  let (_,invs) = 
    Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name 
  in
  make_and_list 
    (List.map (fun (li,_) -> make_logic_pred_call li [this]) invs)
  
let rec statement s = 
  reset_tmp_var();
  match s.jc_statement_node with
    | JCSblock l -> statement_list l
    | JCSexpr e -> statement_expr e
    | JCSif (e, s1, s2) -> 
	let l,e = expr e in
	make_lets l (If(e, statement s1, statement s2))
    | JCSwhile (e, la, s) -> 
	let l,e = expr e in
	While(make_lets l e, assertion None "" la.jc_loop_invariant,
	      Some (term None "" la.jc_loop_variant,None), [statement s])
    | JCSassert _ -> assert false (* TODO *)
    | JCSdecl(vi,e,s) -> 
	begin
	  match e with
	    | None -> assert false
	    | Some e ->
		let l,e = expr e in
		make_lets l
		(if vi.jc_var_info_assigned then 
		  Let_ref(vi.jc_var_info_final_name,e, statement s)
		else 
		  Let(vi.jc_var_info_final_name,e, statement s))
	end
    | JCSreturn e -> 
	let l,e = expr e in make_lets l e
    | JCSunpack(_,e) -> 
	let l,e = expr e in make_lets l (make_app "unpack_" [e])
    | JCSpack(st,e) -> 
	let l,e = expr e in
	let tmp = tmp_why_var() in
	make_lets (l@[(tmp,e)])
	  (Assert(invariant_for_struct (LVar tmp) st, 
		  make_app "pack_" [Var tmp]))
    | JCSbreak l -> assert false
    | JCScontinue l -> assert false
    | JCSgoto l -> assert false
    | JCSthrow (_, _) -> assert false
    | JCStry (_, _, _) -> assert false

and statement_list l = 
  List.fold_right 
    (fun s acc -> append (statement s) acc) l Void

(******************
 structures
******************)

let tr_struct st acc =
  (* declarations of field memories *)
  let acc = 
    List.fold_left
      (fun acc (_,fi) ->
	 let mem = memory_field fi in
	 Param(false,
	       fi.jc_field_info_name,
	       Ref_type(Base_type mem))::acc)
      acc st.jc_struct_info_fields
  in 
  (* declaration of the struct_id *)
  let struct_id_type = 
    { logic_type_name = "struct_id" ;
      logic_type_args = [simple_logic_type st.jc_struct_info_root] }
  in
  let acc =
    Logic(false,st.jc_struct_info_name,[],struct_id_type)::acc
  in
  (* the invariants *)
(*
  let tmp = "this" in
  let i = invariant_for_struct (LVar tmp) st in
  let a =
    LImpl(LPred("instanceof",
		[LVar "a";
		 LVar tmp;
		 LVar st.jc_struct_info_name]),
	  LOr(LPred("eq",
		    [LApp("select",[LVar "mutable"; LVar tmp]);
		     LConst (Prim_bool true)])
		,i))
  in
  let (_,invs) = 
    Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name 
  in
  let params =
    List.fold_left
      (fun acc (li,_) -> 
	 FieldSet.union li.jc_logic_info_effects.jc_reads_fields acc)
      FieldSet.empty
      invs
  in
  let a =
    FieldSet.fold
      (fun fi a ->
	 LForall(fi.jc_field_info_name, memory_field fi,
		 a))
      params a
  in 
  let a =
    LForall("a",simple_logic_type "alloc_table",
	    LForall("mutable",memory_type (simple_logic_type "bool"),
		    LForall(tmp,simple_logic_type "pointer",a)))
  in
  let acc =
    Axiom("global_invariant_for_" ^ st.jc_struct_info_name, a) :: acc
  in
*)
  match st.jc_struct_info_parent with
    | None ->
	(* declaration of root type and the allocation table *)
	let r = st.jc_struct_info_name in
	let alloc_type =
	  Ref_type (Base_type { logic_type_name = "alloc_table";
				logic_type_args = [simple_logic_type r] } )
	in
	Type(r,[]) ::
	  Param(false,r ^ "_alloc_table",alloc_type) :: acc
    | Some p ->
	(* axiom for instance_of *)
	let name = 
	  st.jc_struct_info_name ^ "_instanceof_" ^ p.jc_struct_info_name
	in
	let root = simple_logic_type st.jc_struct_info_root in
	let root_alloc_table = 
	  { logic_type_name = "alloc_table";
	    logic_type_args = [root] }
	in
	let root_pointer = 
	  { logic_type_name = "pointer";
	    logic_type_args = [root] }
	in
	let f =
	  LForall("a",root_alloc_table,
		  LForall("p",root_pointer,
			  LImpl(LPred("instanceof",
				      [LVar "a";
				       LVar "p";
				       LVar st.jc_struct_info_name]),
				LPred("instanceof",
				      [LVar "a";
				       LVar "p";
				       LVar p.jc_struct_info_name]))))
	in
	Axiom(name,f)::acc

       
(*************
locations
*********)

let rec pset before loc = 
  match loc with
    | JCLderef(e,fi) ->
	let m = lvar (Some before) fi.jc_field_info_name in
	LApp("pset_deref", [pset before e; m])
    | JCLvar vi -> 
	let m = lvar_info (Some before) vi in
	LApp("pset_singleton", [m])

let collect_locations before (refs,mems) loc =
  match loc with
    | JCLderef(e,fi) -> 
	let iloc = pset before e in
	let l =
	  try
	    let l = FieldMap.find fi mems in
	    iloc::l
	  with Not_found -> [iloc]
	in
	(refs, FieldMap.add fi l mems)
    | JCLvar vi -> 
	let var = vi.jc_var_info_final_name in
	(StringMap.add var true refs,mems)

let rec make_union_loc = function
  | [] -> LVar "pset_empty"
  | [l] -> l
  | l::r -> LApp("pset_union",[l;make_union_loc r])

let assigns before ef locs =
  match locs with
    | None -> LTrue	
    | Some locs ->
  let refs = 
    (* HeapVarSet.fold
	    (fun v m -> 
	       if Ceffect.is_alloc v then m 
	       else StringMap.add (heap_var_name v) (Reference false) m)
	    assigns.Ceffect.assigns_var 
    *) StringMap.empty 
  in
  let mems = 
    FieldSet.fold
      (fun fi m -> 
	 FieldMap.add fi [] m)
      ef.jc_writes.jc_effect_memories FieldMap.empty 
  in
  let refs,mems = 
    List.fold_left (collect_locations before) (refs,mems) locs
  in
  let a =
  StringMap.fold
    (fun v p acc -> 
       if p then acc else
	 make_and acc (LPred("eq", [LVar v; LVarAtLabel(v,before)])))
    refs LTrue
  in
  FieldMap.fold
    (fun fi p acc -> 
       let v = fi.jc_field_info_name in
       let alloc = fi.jc_field_info_root ^ "_alloc_table" in
       make_and acc
	 (LPred("not_assigns",
		[LVarAtLabel(alloc,before); 
		 LVarAtLabel(v,before);
		 LVar v; make_union_loc p])))
    mems a

(*****************
 functions
**************)

let parameter v =
  (v.jc_var_info_final_name,tr_type v.jc_var_info_type)

let tr_fun f spec body acc = 
  let requires = 
    List.fold_right
      (fun v acc ->
	 match v.jc_var_info_type with
	   | JCTpointer(st,a,b) ->
	       let alloc =
		 st.jc_struct_info_root ^ "_alloc_table"
	       in
	       let validity = 
		 make_and 
		   (LPred("le_int",
			  [LApp("offset_min",
				[LVar alloc;
				 LVar v.jc_var_info_final_name]);
			   LConst (Prim_int (string_of_int a))]))
		   (LPred("ge_int",
			  [LApp("offset_max",
				[LVar alloc;
				 LVar v.jc_var_info_final_name]);
			   LConst (Prim_int (string_of_int b))]))
	       in
	       make_and 
		 (make_and validity 
		    (LPred("instanceof",
			   [LVar alloc;
			    LVar v.jc_var_info_final_name;
			    LVar st.jc_struct_info_name])))
		 acc
	   | JCTnative _ -> acc
	   | _ -> assert false
      )
      f.jc_fun_info_parameters
      (assertion None "" spec.jc_fun_requires)
  in
  let all_behaviors =
    List.map
      (fun (id,b) ->
	 let post = 
	   make_and 
	   (assertion None "" b.jc_behavior_ensures)
	   (assigns "" f.jc_fun_info_effects b.jc_behavior_assigns)
	 in
	 let a =
	   match b.jc_behavior_assumes with
	     | None -> post
	     | Some e -> 
		 make_impl (assertion (Some "") "" e) post
	 in
	 (id,b,a))
      spec.jc_fun_behavior
  in
  let global_ensures =
    List.fold_right
      (fun (_,_,e) acc -> make_and e acc)
      all_behaviors LTrue
  in
  let reads =
    FieldSet.fold
      (fun f acc -> f.jc_field_info_name::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_memories
      []
  in
  let reads =
    StringSet.fold
      (fun v acc -> (v ^ "_alloc_table")::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_alloc_table
      reads
  in
  let writes =
    FieldSet.fold
      (fun f acc -> f.jc_field_info_name::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_memories
      []
  in
  let why_param = 
    let annot_type =
      Annot_type(requires,tr_type f.jc_fun_info_return_type,
		 reads,writes, global_ensures,[])
    in
    let fun_type =
      List.fold_right
	(fun v acc ->
	   Prod_type(v.jc_var_info_final_name,tr_type v.jc_var_info_type,acc))
	f.jc_fun_info_parameters
	annot_type
    in
    Param(false,f.jc_fun_info_name,fun_type)
  in
  let params = List.map parameter f.jc_fun_info_parameters in
  let acc =
    List.fold_right
      (fun (id,b,e) acc ->
	 let d =
	   Def(f.jc_fun_info_name ^ "_ensures_" ^ id,
	       Fun(params,
		   requires,statement_list body,
		   e,[]))
	 in d::acc)
      all_behaviors acc
  in why_param::acc


let tr_axiom id p acc = Axiom(id,assertion None "" p)::acc
  
(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
