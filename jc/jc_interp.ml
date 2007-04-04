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
    | JCCvoid -> Prim_void
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
    | JCTrange ri -> simple_logic_type ri.jc_range_info_name
    | JCTpointer (st, a, b) -> 
	let ti = simple_logic_type (st.jc_struct_info_root) in
	{ logic_type_name = "pointer";
	  logic_type_args = [ ti ] }

let tr_type t = Base_type(tr_base_type t)
(*
  match t with
    | JCTnative _ | JCTlogic _ -> Base_type(tr_base_type t)
    | JCTpointer _ -> Base_type(tr_base_type t)	
*)

(**************************

terms and assertions 

*************************)

let tag_name st = st.jc_struct_info_name ^ "_tag"

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
  let l = 
    StringSet.fold
      (fun v acc -> (LVar (v ^ "_alloc_table"))::acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      l	    
  in
  StringSet.fold
    (fun v acc -> (LVar (v ^ "_tag_table"))::acc)
    li.jc_logic_info_effects.jc_effect_tag_table
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
    | JCToffset_max(t,st) -> 
	let alloc =
	  st.jc_struct_info_root ^ "_alloc_table"
	in
	LApp("offset_max",[LVar alloc; ft t]) 
    | JCToffset_min(t,st) -> 
	let alloc =
	  st.jc_struct_info_root ^ "_alloc_table"
	in
	LApp("offset_min",[LVar alloc; ft t]) 
    | JCTinstanceof(t,ty) ->
	let tag = ty.jc_struct_info_root ^ "_tag_table" in
	LApp("instanceof_bool",
	     [lvar label tag; ft t;LVar (tag_name ty)])
    | JCTcast(t,ty) ->
	let tag = ty.jc_struct_info_root ^ "_tag_table" in
	LApp("downcast",
	     [lvar label tag; ft t;LVar (tag_name ty)])

let rec assertion label oldlabel a =
  let fa = assertion label oldlabel 
  and ft = term label oldlabel
  in
  match a.jc_assertion_node with
    | JCAtrue -> LTrue
    | JCAfalse -> LFalse
    | JCAif(t1,p2,p3) -> LIf(ft t1,fa p2,fa p3)
    | JCAand l -> make_and_list (List.map fa l)
    | JCAor l -> make_or_list (List.map fa l)
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
	let tag = ty.jc_struct_info_root ^ "_tag_table" in
	LPred("instanceof",
	      [lvar label tag; ft t; LVar (tag_name ty)])

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
  let params_reads =
    StringSet.fold
      (fun v acc -> 
	 let t = { logic_type_args = [simple_logic_type v];
		   logic_type_name = "tag_table" }
	 in
	 (v ^ "_tag_table", t)::acc)
      li.jc_logic_info_effects.jc_effect_tag_table
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

let const_un = Cte(Prim_int "1")

let incr_call op =
  match op with
    | Stat_inc -> Jc_pervasives.add_int_.jc_fun_info_name
    | Stat_dec -> Jc_pervasives.sub_int_.jc_fun_info_name

let make_acc fi e =
  make_app "acc_"
    [ Var (fi.jc_field_info_root ^ "_alloc_table") ;
      Var fi.jc_field_info_name ; e ]

let make_upd fi e1 e2 =
  make_app "upd_"
    [ Var (fi.jc_field_info_root ^ "_alloc_table") ;
      Var fi.jc_field_info_name ; e1 ; e2 ]
    
let rec make_lets l e =
  match l with
    | [] -> e
    | (tmp,a)::l -> Let(tmp,a,make_lets l e)


let rec expr e : expr =
  match e.jc_expr_node with
    | JCEconst JCCnull -> Var "null"
    | JCEconst c -> Cte(const c)
    | JCEvar v ->
	if v.jc_var_info_assigned 
	then Deref v.jc_var_info_final_name
	else Var v.jc_var_info_final_name
    | JCEif(e1,e2,e3) -> 
	let e1 = expr e1 in
	let e2 = expr e2 in
	let e3 = expr e3 in
	If(e1,e2,e3)
    | JCEshift(e1,e2) -> 
	let e1 = expr e1 in
	let e2 = expr e2 in
	make_app "shift" [e1; e2]
    | JCEinstanceof(e,t) ->
	let e = expr e in
	let tag = t.jc_struct_info_root ^ "_tag_table" in
	make_app "instanceof_" [Deref tag; e; Var (tag_name t)]
    | JCEcast(e,t) ->
	let e = expr e in
	let tag = t.jc_struct_info_root ^ "_tag_table" in
	make_app "downcast_" [Deref tag; e; Var (tag_name t)]
    | JCEderef(e,f) -> 
	let e = expr e in
	make_acc f e


let invariant_for_struct this st =
  let (_,invs) = 
    Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name 
  in
  make_and_list 
    (List.map (fun (li,_) -> make_logic_pred_call li [this]) invs)
  
let rec statement s = 
  (* reset_tmp_var(); *)
  match s.jc_statement_node with
    | JCScall(vio,f,l,s) -> 
	let el = List.map expr l in
	let call = make_app f.jc_fun_info_name el in
	begin
	  match vio with
	    | None -> 
		(* check that associated statement is empty *)
		begin match s.jc_statement_node with
		  | JCSblock [] -> () (* ok *)
		  | _ -> assert false
		end;
		call
	    | Some vi ->
		Let(vi.jc_var_info_final_name,call, statement s)
	end
    | JCSincr_local(op, vi) ->
	(* let tmp = !v in v <- tmp+-1 *)
	let tmp = tmp_var_name () in
	let v = vi.jc_var_info_name in
	Let(tmp, Deref(v), 
	    Assign(v,make_app (incr_call op) [Var tmp; const_un]))
    | JCSincr_heap(op,e1,fi) -> 
 	let e1 = expr e1 in
 	let tmp1 = tmp_var_name () in
 	let acc_fi_e = make_acc fi (Var tmp1) in
 	let updated_value = make_app (incr_call op) [acc_fi_e; const_un] in
	make_lets
 	  [ (tmp1, e1) ]
 	  (make_upd fi (Var tmp1) updated_value)
    | JCSassign_local (vi, e2) -> 
	let e2 = expr e2 in
	let n = vi.jc_var_info_final_name in
	Assign(n, e2)
    | JCSassign_heap(e1,fi,e2) -> 
	let e1 = expr e1 in
	let e2 = expr e2 in
	let tmp1 = tmp_var_name () in
	let tmp2 = tmp_var_name () in
	make_lets 
	  ([ (tmp1, e1) ; (tmp2, e2) ])
	  (make_upd fi (Var tmp1) (Var tmp2))
    | JCSblock l -> statement_list l
    | JCSif (e, s1, s2) -> 
	let e = expr e in
	If(e, statement s1, statement s2)
    | JCSloop (la, s) -> 
	While(Cte(Prim_bool true), assertion None "" la.jc_loop_invariant,
	      Some (term None "" la.jc_loop_variant,None), [statement s])
    | JCSassert a -> Assert(assertion None "" a, Void)
    | JCSdecl(vi,e,s) -> 
	begin
	  match e with
	    | None -> assert false
	    | Some e ->
		let e = expr e in
		if vi.jc_var_info_assigned then 
		  Let_ref(vi.jc_var_info_final_name,e, statement s)
		else 
		  Let(vi.jc_var_info_final_name,e, statement s)
	end
    | JCSreturn e -> 
	expr e
    | JCSunpack(_,e) -> 
	let e = expr e in make_app "unpack_" [e]
    | JCSpack(st,e) -> 
	let e = expr e in
	let tmp = tmp_var_name() in
	make_lets ([(tmp,e)])
	  (Assert(invariant_for_struct (LVar tmp) st, 
		  make_app "pack_" [Var tmp]))
    | JCSthrow (ei, Some e) -> 
	let e = expr e in
	Raise(ei.jc_exception_info_name,Some e)
    | JCSthrow (ei, None) -> 
	Raise(ei.jc_exception_info_name,None)
    | JCStry (s, catches, finally) -> 
	assert (finally.jc_statement_node = JCSblock []); (* TODO *)
	let catch s c = match c with
	  | (ei,Some v,st) ->
	      Try(s, 
		  ei.jc_exception_info_name, 
		  Some v.jc_var_info_final_name, statement st)
	  | (ei,None,st) ->
	      Try(s, 
		  ei.jc_exception_info_name, 
		  None, statement st)
	in
	List.fold_left catch (statement s) catches
 	

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
  (* declaration of the tag_id *)
  let tag_id_type = 
    { logic_type_name = "tag_id" ;
      logic_type_args = [simple_logic_type st.jc_struct_info_root] }
  in
  let acc =
    Logic(false,tag_name st,[],tag_id_type)::acc
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
	let tag_type =
	  Ref_type (Base_type { logic_type_name = "tag_table";
				logic_type_args = [simple_logic_type r] } )
	in
	Type(r,[]) ::
	Param(false,r ^ "_alloc_table",alloc_type) ::
	Param(false,r ^ "_tag_table",tag_type) :: acc
    | Some p ->
	(* axiom for instance_of *)
	let name = 
	  st.jc_struct_info_name ^ "_instanceof_" ^ p.jc_struct_info_name
	in
	let root = simple_logic_type st.jc_struct_info_root in
	let root_tag_table = 
	  { logic_type_name = "tag_table";
	    logic_type_args = [root] }
	in
	let root_pointer = 
	  { logic_type_name = "pointer";
	    logic_type_args = [root] }
	in
	let f =
	  LForall("a",root_tag_table,
		  LForall("p",root_pointer,
			  LImpl(LPred("instanceof",
				      [LVar "a";
				       LVar "p";
				       LVar (tag_name st)]),
				LPred("instanceof",
				      [LVar "a";
				       LVar "p";
				       LVar (tag_name p)]))))
	in
	Axiom(name,f)::acc

       
(*************
locations
*********)

let rec pset before loc = 
  match loc with
    | JCLSderef(ls,fi) ->
	let m = lvar (Some before) fi.jc_field_info_name in
	LApp("pset_deref", [m;pset before ls])
    | JCLSvar vi -> 
	let m = lvar_info (Some before) vi in
	LApp("pset_singleton", [m])
    | JCLSrange(ls,a,b) ->
	let ls = pset before ls in
	LApp("pset_range", [ls;term (Some before) before a; term (Some before) before b])
	
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

let excep_posts_for_others eopt excep_posts =
  ExceptionMap.fold
    (fun ei l acc ->
       if eopt = Some ei then acc 
       else (ei.jc_exception_info_name,LTrue)::acc)
    excep_posts []
       
let tr_fun f spec body acc =
  (* There will be two passes for requires clauses
     (one for invariants, and one for requires themselves)
     and this will be used by both *)
  let requires_assertion = assertion None "" spec.jc_fun_requires in
  (* Calculate invariants (for each parameter), that will be used as pre and post conditions *)
  let invariants =
    List.fold_right
      (fun v acc ->
	 match v.jc_var_info_type with
	   | JCTpointer(st,_,_) ->
	       let var = LVar v.jc_var_info_final_name in
	       let invariant = invariant_for_struct var st in
	       make_and invariant acc
	   | JCTrange _ -> acc
	   | JCTnative _ -> acc
	   | JCTlogic _ -> acc)
      f.jc_fun_info_parameters
      requires_assertion
  in
  let requires = 
    List.fold_right
      (fun v acc ->
	 match v.jc_var_info_type with
	   | JCTpointer(st,a,b) ->
	       let alloc =
		 st.jc_struct_info_root ^ "_alloc_table"
	       in
	       let tag =
		 st.jc_struct_info_root ^ "_tag_table"
	       in
	       let var = LVar v.jc_var_info_final_name in
	       let validity = 
		 make_and 
		   (LPred("le_int",
			  [LApp("offset_min",
				[LVar alloc; var]);
			   LConst (Prim_int (Num.string_of_num a))]))
		   (LPred("ge_int",
			  [LApp("offset_max",
				[LVar alloc; var]);
			   LConst (Prim_int (Num.string_of_num b))]))
	       in
	       let instance =
		 (LPred("instanceof",
			[LVar tag; var ; LVar (tag_name st)]))
	       in
               make_and (make_and validity instance) acc
	       (*let invariant = invariant_for_struct var st in
	       make_and 
		 (make_and (make_and validity instance) invariant)
		 acc*)
	   | JCTrange _ -> acc
	   | JCTnative _ -> acc
	   | JCTlogic _ -> acc)
      f.jc_fun_info_parameters
      requires_assertion
  in
  (* adding invariants to requires *)
  let requires = make_and requires invariants in
  let (normal_behaviors,excep_behaviors) =
    List.fold_left
      (fun (normal,excep) (id,b) ->
	 let post =
           make_and
	     (make_and
	       (assertion None "" b.jc_behavior_ensures)
	       (assigns "" f.jc_fun_info_effects b.jc_behavior_assigns))
             invariants
	 in
	 let a =
	   match b.jc_behavior_assumes with
	     | None -> post
	     | Some e -> 
		 make_impl (assertion (Some "") "" e) post
	 in
	 match b.jc_behavior_throws with
	   | None -> ((id,b,a)::normal,excep)
	   | Some ei ->
	       let eb =
		 try
		   ExceptionMap.find ei excep
		 with Not_found -> []
	       in
	       (normal,ExceptionMap.add ei ((id,b,a)::eb) excep))
      ([],ExceptionMap.empty)
      spec.jc_fun_behavior
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
  let reads =
    StringSet.fold
      (fun v acc -> (v ^ "_tag_table")::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_tag_table
      reads
  in
  let writes =
    FieldSet.fold
      (fun f acc -> f.jc_field_info_name::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_memories
      []
  in
  let normal_post =
    List.fold_right
      (fun (_,_,e) acc -> make_and e acc)
      normal_behaviors LTrue
  in
  let excep_posts =
    ExceptionMap.fold
      (fun ei l acc ->
	 let p = 
	   List.fold_right (fun (_,_,e) acc -> make_and e acc) l LTrue
	 in (ei.jc_exception_info_name,p)::acc) 
      excep_behaviors []
  in
  (* why parameter for calling the function *)
  let why_param = 
    let annot_type =
      Annot_type(requires,tr_type f.jc_fun_info_return_type,
		 reads,writes, normal_post, excep_posts)
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
  (* why functions for each behaviors *)
  let params = List.map parameter f.jc_fun_info_parameters in
  let acc =
    List.fold_right
      (fun (id,b,e) acc ->
	 let d =
	   Def(f.jc_fun_info_name ^ "_ensures_" ^ id,
	       Fun(params,
		   requires,statement_list body,
		   e,excep_posts_for_others None excep_behaviors))
	 in d::acc)
      normal_behaviors acc
  in 
  let acc =
    ExceptionMap.fold
      (fun ei l acc ->
	 List.fold_right
	   (fun (id,b,e) acc ->
	      let d =
		Def(f.jc_fun_info_name ^ "_exsures_" ^ id,
		    Fun(params,
			requires,statement_list body,
			LTrue,
			(ei.jc_exception_info_name,e) :: 
			excep_posts_for_others (Some ei) excep_behaviors))
	      in d::acc)
	   l acc)
      excep_behaviors acc
  in why_param::acc

let tr_logic_type id acc = Type(id,[])::acc

let tr_axiom id p acc = Axiom(id,assertion None "" p)::acc

let tr_exception ei acc =
  Exception(ei.jc_exception_info_name, 
	    Some (tr_base_type ei.jc_exception_info_type)) :: acc

let tr_range_type ri to_int of_int acc =
  let n = ri.jc_range_info_name in
  let range_pred x =
    LAnd(LPred("le_int",[LConst(Prim_int(Num.string_of_num(ri.jc_range_info_min))); x]),
	       LPred("le_int",[x; LConst(Prim_int(Num.string_of_num(ri.jc_range_info_max)))]))
  in
  let of_int_type =
    Prod_type("x", Base_type(simple_logic_type "int"),
	      Annot_type(range_pred (LVar "x"),
			 Base_type(simple_logic_type n),
			 [],[],
			 LPred("eq_int",
			       [LVar "x";LApp(to_int.jc_fun_info_name,[LVar "result"])]),[]))
  in
  Type(n,[]) ::
  Logic(false,to_int.jc_fun_info_name,
	[("",simple_logic_type n)],simple_logic_type "int") :: 
  Param(false,of_int.jc_fun_info_name,of_int_type) ::
  Axiom(n^"_range",
	LForall("x",simple_logic_type n,range_pred (LApp(to_int.jc_fun_info_name,[LVar "x"]))))		
  :: acc
	   
(*
Local Variables: 
compile-command: "unset LANG; make -C .. bin/jessie.byte"
End: 
*)
