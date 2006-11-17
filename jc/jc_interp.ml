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
    | `Tunit -> "unit"
    | `Tboolean -> "bool"
    | `Tinteger -> "int"
    | `Treal -> "real"

let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }
  
let tr_base_type t =
  match t with
    | JCTnative t -> simple_logic_type (tr_native_type t)
    | JCTlogic s -> simple_logic_type s
    | JCTvalidpointer (st, a, b) -> 
	let ti = simple_logic_type (st.jc_struct_info_root) in
	{ logic_type_name = "pointer";
	  logic_type_args = [ti] }
    | JCTpointer _ -> assert false

let tr_type t =
  match t with
    | JCTnative _ | JCTlogic _ -> Base_type(tr_base_type t)
    | JCTvalidpointer _ -> Base_type(tr_base_type t)	
    | JCTpointer _ -> assert false

let lvar ?(assigned=true) label v =
  if assigned then
    match label with 
      | None -> LVar v 
      | Some l -> LVarAtLabel(v,l)
  else LVar v

let lvar_info label v = 
  lvar ~assigned:v.jc_var_info_assigned label v.jc_var_info_final_name

let rec term label oldlabel t =
  let ft = term label oldlabel in
  match t.jc_term_node with
    | JCTconst JCCnull -> LVar "null"
    | JCTvar v -> lvar_info label v
    | JCTconst c -> LConst(const c)
    | JCTshift(t1,t2) -> LApp("shift",[ft t1; ft t2])
    | JCTif(t1,t2,t3) -> assert false
    | JCTderef(t,f) -> LApp("select",[lvar label f.jc_field_info_name;ft t])
    | JCTapp(f,l) -> 
	LApp(f.jc_logic_info_name,List.map ft l)
    | JCTold(t) -> term (Some oldlabel) oldlabel t
    | JCTinstanceof(t,ty) ->
	LApp("instanceof_bool",
	     [lvar label "alloc"; ft t;LVar ty.jc_struct_info_name])
    | JCTcast(t,ty) ->
	LApp("downcast",
	     [lvar label "alloc"; ft t;LVar ty.jc_struct_info_name])

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
    | JCAapp(f,l) -> LPred(f.jc_logic_info_name,List.map ft l)
    | JCAforall(v,p) -> 
	LForall(v.jc_var_info_final_name,
		tr_base_type v.jc_var_info_type,
		fa p)
    | JCAold a -> assertion (Some oldlabel) oldlabel a
    | JCAinstanceof(t,ty) -> 
	LPred("instanceof",
	      [lvar label "alloc"; ft t; LVar ty.jc_struct_info_name])

type interp_lvalue =
  | LocalRef of var_info
  | HeapRef of field_info * expr

let tempvar_count = ref 0
let reset_tmp_var () = tempvar_count := 0
let tmp_why_var () = incr tempvar_count; "jessie_" ^ string_of_int !tempvar_count

let rec expr e =
  match e.jc_expr_node with
    | JCEconst JCCnull -> Var "null"
    | JCEconst c -> Cte(const c)
    | JCEvar v -> Var v.jc_var_info_final_name
    | JCEif(e1,e2,e3) -> If(expr e1,expr e2,expr e3)
    | JCEshift(e1,e2) -> make_app "shift" [expr e1; expr e2]
    | JCEinstanceof(e,t) ->
	make_app "instanceof_" [Deref "alloc"; expr e; Var t.jc_struct_info_name]
    | JCEcast(e,t) ->
	make_app "downcast_" [Deref "alloc"; expr e; Var t.jc_struct_info_name]
    | JCEderef(e,f) -> make_app "acc_" [Var f.jc_field_info_name; expr e]
    | JCEassign_local (vi, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_heap(e1,fi,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, expr e2,
		append
		  (make_app "upd_"
		     [Var memory; Var tmp1; Var tmp2])
		  (Var tmp2))) 
    | JCEassign_op_local (vi, op, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_op_heap(e1,fi,op,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, 
		make_app op.jc_fun_info_name
		  [ make_app "acc_" [Var memory; Var tmp1] ;
		    expr e2 ],
		append
		  (make_app "safe_upd_"
		     [Var memory; Var tmp1; Var tmp2])
		  (Var tmp2))) 
    | JCEcall(f,l) -> 
	if f==Jc_pervasives.and_ then
	  begin
	    match l with
	      | [e1;e2] -> And(expr e1, expr e2)
	      | _ -> assert false
	  end
	else
	  make_app f.jc_fun_info_name (List.map expr l)

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
    | JCEassign_local (vi, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_heap(e1,fi,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, expr e2,
		make_app "upd_"
		   [Var memory; Var tmp1; Var tmp2]))
    | JCEassign_op_local (vi, op, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_op_heap(e1,fi,op,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, 
		make_app op.jc_fun_info_name
		  [ make_app "acc_" [Var memory; Var tmp1] ;
		    expr e2 ],
		make_app "safe_upd_"
		  [Var memory; Var tmp1; Var tmp2]))
    | JCEcall(f,l) -> 
	make_app f.jc_fun_info_name (List.map expr l)

let rec statement s = 
  match s.jc_statement_node with
    | JCSskip -> Void
    | JCSblock l -> statement_list l
    | JCSexpr e -> statement_expr e
    | JCSif (e, s1, s2) -> 
	If(expr e, statement s1, statement s2)
    | JCSwhile (_, _, _) -> assert false
    | JCSassert _ -> assert false
    | JCSdecl _ -> assert false
    | JCSreturn e -> 
	expr e
    | JCSbreak l -> assert false
    | JCScontinue l -> assert false
    | JCSgoto l -> assert false
    | JCSthrow (_, _) -> assert false
    | JCStry (_, _, _) -> assert false

and statement_list l =
  match l with
    | [] -> Void
    | [i] -> statement i
    | i::r -> append (statement i) (statement_list r)

(******************
 structures
******************)

let tr_struct st acc =
  let acc = 
    List.fold_left
      (fun acc (_,fi) ->
	 let mem =
	   { logic_type_name = "memory";
	     logic_type_args = 
	       [simple_logic_type (st.jc_struct_info_root);
		tr_base_type fi.jc_field_info_type] }
	 in
	 Param(false,
	       fi.jc_field_info_name,
	       Ref_type(Base_type mem))::acc)
      acc st.jc_struct_info_fields
  in 
  let acc =
    Logic(false,st.jc_struct_info_name,[],simple_logic_type "struct_id")::acc
  in
  match st.jc_struct_info_parent with
    | None ->
	Type(st.jc_struct_info_name,[])::acc
    | Some p ->
	let name = 
	  st.jc_struct_info_name ^ "_instanceof_" ^ p.jc_struct_info_name
	in
	let root = 
	  { logic_type_name = "pointer";
	    logic_type_args = [simple_logic_type (st.jc_struct_info_root)] }
	in
	let f =
	  LForall("a",simple_logic_type "alloc_table",
		  LForall("p",root,
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
	let m = lvar before fi.jc_field_info_name in
	LApp("pset_deref", [pset before e; m])
    | JCLvar vi -> 
	let m = lvar_info before vi in
	LApp("pset_singleton", [m])

module StringMap = Map.Make(String)


type mem_or_ref = 
  | Reference of bool 
      (* a global reference, boolean indicates whether it 
	 is given in assigns ckause, thus is modified ;
	 or not given, thus is not modified. *)
  | Memory of term list
      (* a memory heap reference, argument is the set of pointers 
	 to parts which are given in assigns clause *)

let collect_locations before acc loc =
  let var,iloc = match loc with
    | JCLderef(e,fi) -> fi.jc_field_info_name, Some (pset before e)
    | JCLvar vi -> vi.jc_var_info_final_name, None
  in
  try
    let p = StringMap.find var acc in
    match p, iloc with
       | Reference _, None -> StringMap.add var (Reference true) acc
       | Memory l, Some iloc -> StringMap.add var (Memory (iloc::l)) acc
       | Reference _,Some n -> assert false
       | Memory _,None -> assert false
  with Not_found -> 
    (match iloc with
       | None -> StringMap.add var (Reference true) acc
       | Some l -> StringMap.add var (Memory [l]) acc)

let rec make_union_loc = function
  | [] -> LVar "pset_empty"
  | [l] -> l
  | l::r -> LApp("pset_union",[l;make_union_loc r])

let assigns before ef locs =
  match locs with
    | None -> LTrue	
    | Some locs ->
  let m = 
    (* HeapVarSet.fold
	    (fun v m -> 
	       if Ceffect.is_alloc v then m 
	       else StringMap.add (heap_var_name v) (Reference false) m)
	    assigns.Ceffect.assigns_var 
    *) StringMap.empty 
  in
  let m = 
    FieldSet.fold
      (fun fi m -> 
	 StringMap.add fi.jc_field_info_name (Memory []) m)
      ef.jc_writes_fields m 
  in
  let l = 
    List.fold_left (collect_locations (Some before)) m locs
  in
  StringMap.fold
    (fun v p acc -> match p with
       | Memory p ->
	   make_and acc
	     (LPred("not_assigns",
		    [LVarAtLabel("alloc",before); 
		     LVarAtLabel(v,before);
		     LVar v; make_union_loc p]))
       | Reference false ->
	   make_and acc (LPred("eq", [LVar v; LVarAtLabel(v,before)]))
       | Reference true -> acc)
    l LTrue

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
	   | JCTvalidpointer(t,a,b) ->
	       let validity = 
		 make_and 
		   (LPred("le_int",
			  [LApp("offset_min",
				[LVar "alloc";
				 LVar v.jc_var_info_final_name]);
			   LConst (Prim_int (string_of_int a))]))
		   (LPred("ge_int",
			  [LApp("offset_max",
				[LVar "alloc";
				 LVar v.jc_var_info_final_name]);
			   LConst (Prim_int (string_of_int b))]))
	       in
	       make_and 
		 (make_and validity 
		    (LPred("instanceof",
			   [LVar "alloc";
			    LVar v.jc_var_info_final_name;
			    LVar t.jc_struct_info_name])))
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
	 (id,b,make_and 
	   (assertion None "" b.jc_behavior_ensures)
	   (assigns "" f.jc_fun_info_effects b.jc_behavior_assigns)))
      spec.jc_fun_behavior
  in
  let global_ensures =
    List.fold_right
      (fun (_,_,e) acc -> make_and e acc)
      all_behaviors LTrue
  in
  let writes =
    FieldSet.fold
      (fun f acc -> f.jc_field_info_name::acc)
      f.jc_fun_info_effects.jc_writes_fields
      []
  in
  let why_param = 
    let annot_type =
      Annot_type(requires,tr_type f.jc_fun_info_return_type,
		 [],writes, global_ensures,[])
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

  
(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
