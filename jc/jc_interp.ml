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
open Jc_invariants
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
    | Tinteger -> "integer"
    | Treal -> "real"

let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }
  
let tr_base_type t =
  match t with
    | JCTnative t -> simple_logic_type (tr_native_type t)
    | JCTlogic s -> simple_logic_type s
    | JCTenum ri -> simple_logic_type ri.jc_enum_info_name
    | JCTpointer (st, a, b) -> 
	let ti = simple_logic_type (st.jc_struct_info_root) in
	{ logic_type_name = "pointer";
	  logic_type_args = [ ti ] }
    | JCTnull -> assert false

let tr_type t = Base_type(tr_base_type t)
(*
  match t with
    | JCTnative _ | JCTlogic _ -> Base_type(tr_base_type t)
    | JCTpointer _ -> Base_type(tr_base_type t)	
*)

let unary_op = function
  | Uplus_int -> "uplus_int"
  | Uminus_int -> "neg_int"
  | Uplus_real -> "uplus_real"
  | Uminus_real -> "uminus_real"
  | Unot -> "not"
  | Ubw_not -> "bw_compl"

let unary_arg_type = function
  | Uplus_int 
  | Uminus_int
  | Ubw_not -> integer_type
  | Uplus_real 
  | Uminus_real -> real_type
  | Unot -> boolean_type

let bin_op = function
  | Bgt_int -> "gt_int_"
  | Blt_int -> "lt_int_"
  | Bge_int -> "ge_int_"
  | Ble_int -> "le_int_"
  | Beq_int -> "eq_int_"
  | Bneq_int -> "neq_int_"
  | Badd_int -> "add_int"
  | Bsub_int -> "sub_int"
  | Bmul_int -> "mul_int"
  | Bdiv_int -> "div_int"
  | Bmod_int -> "mod_int"
  | Beq_pointer -> "eq_pointer"
  | Bneq_pointer -> "neq_pointer"
  | Badd_real -> "add_real"
  | Bsub_real -> "sub_real"
  | Bmul_real -> "mul_real"
  | Bdiv_real -> "div_real"
  | Bneq_real -> "neq_real_"
  | Beq_real -> "eq_real_"
  | Bge_real -> "ge_real_"
  | Ble_real -> "le_real_"
  | Bgt_real -> "gt_real_"
  | Blt_real -> "lt_real_"
  | Bbw_and -> "bw_and"
  | Bbw_or -> "bw_or"
  | Bbw_xor -> "bw_xor"
  | Bshift_left -> "lsl"
  | Bshift_right -> "lsr"
  | Blor | Bland -> assert false (* should be handled before for laziness *)
  | Biff | Bimplies -> assert false (* never in expressions *)

let pred_bin_op = function
  | Bgt_int -> "gt_int"
  | Blt_int -> "lt_int"
  | Bge_int -> "ge_int"
  | Ble_int -> "le_int"
  | Beq_int -> "eq"
  | Bneq_int -> "neq"
  | Beq_pointer -> "eq"
  | Bneq_pointer -> "neq"
  | Bneq_real -> "neq"
  | Beq_real -> "eq"
  | Blor -> "bor"
  | Bland -> "band"
  | Biff | Bimplies -> assert false (* TODO *)
  | _ -> assert false (* TODO *)

let bin_arg_type loc = function
  | Bgt_int | Blt_int | Bge_int | Ble_int 
  | Beq_int | Bneq_int 
  | Badd_int | Bsub_int | Bmul_int | Bdiv_int | Bmod_int
  | Bbw_and | Bbw_or | Bbw_xor | Bshift_right | Bshift_left -> integer_type
  | Biff|Bimplies|Blor|Bland -> boolean_type
  | Bdiv_real | Bmul_real | Bsub_real | Badd_real
  | Bneq_real | Beq_real | Bge_real
  | Ble_real | Bgt_real | Blt_real -> real_type
  | Bneq_pointer | Beq_pointer -> assert false

let coerce loc tdest tsrc e =
  match tdest,tsrc with
    | JCTnative t, JCTnative u when t=u -> e
    | JCTlogic t, JCTlogic u when t=u -> e
    | JCTenum ri1, JCTenum ri2 when ri1==ri2 -> e
    | JCTnative Tinteger, JCTenum ri ->
	make_app ("integer_of_" ^ ri.jc_enum_info_name) [e]
    | JCTenum ri, JCTnative Tinteger ->
	make_app (ri.jc_enum_info_name ^ "_of_integer") [e]
    | _ , JCTnull -> e
    | JCTpointer (st, a, b), _  -> 
	make_app "downcast_" 
	  [ Deref (st.jc_struct_info_root ^ "_tag_table") ; e ;
	    Var (st.jc_struct_info_name ^ "_tag") ]	
    |  _ -> 
	 Jc_typing.typing_error loc 
	   "can't coerce type %a to type %a" 
	   Jc_output.print_type tsrc Jc_output.print_type tdest

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
    | JCTunary(op,t1) ->
	let t1' = term label oldlabel t1 in
	LApp (unary_op op, [t1'])
(* TODO: no need for coercion ? (contrary to expr)
	  [coerce t.jc_term_loc (unary_arg_type op) t1.jc_term_type t1' ]
*)
    | JCTbinary(t1,((Beq_pointer | Bneq_pointer) as op),t2) ->
let t1' = term label oldlabel t1 in
	let t2' = term label oldlabel t2 in
	LApp (bin_op op, [ t1'; t2'])
    | JCTbinary(t1,Bland,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,Blor,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,op,t2) ->
	let t1' = term label oldlabel t1 in
	let t2' = term label oldlabel t2 in
	LApp (bin_op op, [ t1'; t2'])
(* TODO: no need for coercion ? (contrary to expr)
	let e1' = expr e1 in
	let e2' = expr e2 in
	let t = bin_arg_type e.jc_expr_loc op in
	make_app (bin_op op) 
	  [ coerce e1.jc_expr_loc t e1.jc_expr_type e1'; 
	    coerce e2.jc_expr_loc t e2.jc_expr_type e2']	
*)
    | JCTshift(t1,t2) -> LApp("shift",[ft t1; ft t2])
    | JCTif(t1,t2,t3) -> assert false (* TODO *)
    | JCTderef(t,f) -> LApp("select",[lvar label f.jc_field_info_name;ft t])
    | JCTapp(f,l) -> make_logic_fun_call f (List.map ft l)	    
    | JCTold(t) -> term (Some oldlabel) oldlabel t
    | JCToffset(k,t,st) -> 
	let alloc =
	  st.jc_struct_info_root ^ "_alloc_table"
	in
	let f = match k with
	  | Offset_min -> "offset_min"
	  | Offset_max -> "offset_max"
	in
	LApp(f,[LVar alloc; ft t]) 
    | JCTinstanceof(t,ty) ->
	let tag = ty.jc_struct_info_root ^ "_tag_table" in
	LApp("instanceof_bool",
	     [lvar label tag; ft t;LVar (tag_name ty)])
    | JCTcast(t,ty) ->
	let tag = ty.jc_struct_info_root ^ "_tag_table" in
	LApp("downcast",
	     [lvar label tag; ft t;LVar (tag_name ty)])
    | JCTrange(t1,t2) -> assert false (* TODO ? *)

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
    | JCArelation(t1,op,t2) ->
	LPred (pred_bin_op op, [ft t1; ft t2])
    | JCAapp(f,l) -> 
	make_logic_pred_call f (List.map ft l)	    
    | JCAforall(v,p) -> 
	LForall(v.jc_var_info_final_name,
		tr_base_type v.jc_var_info_type,
		fa p)
    | JCAexists(v,p) -> 
	LExists(v.jc_var_info_final_name,
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
let _ = Jc_invariants.memory_field' := memory_field
	 
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
      (* Predicate *)
      | None, JCAssertion a -> 
	  let a = assertion None "" a in
	  Predicate(false,li.jc_logic_info_name,params_reads, a) 
      (* Function *)
      | Some ty, JCTerm t -> 
	  let ret = tr_base_type ty in
	  let t = term None "" t in
	  Function(false,li.jc_logic_info_name,params_reads, ret, t) 
      (* Logic *)
      | tyo, JCReads r ->
	  let ret = match tyo with
	    | None -> simple_logic_type "prop"
	    | Some ty -> tr_base_type ty
	  in
	  Logic(false, li.jc_logic_info_name, params_reads, ret)
      (* Other *)
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

(*
let incr_call op =
  match op with
    | Stat_inc -> Jc_pervasives.add_int_.jc_fun_info_name
    | Stat_dec -> Jc_pervasives.sub_int_.jc_fun_info_name
*)


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
    | JCEunary(op,e1) ->
	let e1' = expr e1 in
	make_app (unary_op op) 
	  [coerce e.jc_expr_loc (unary_arg_type op) e1.jc_expr_type e1' ]
    | JCEbinary(e1,((Beq_pointer | Bneq_pointer) as op),e2) ->
	let e1' = expr e1 in
	let e2' = expr e2 in
	make_app (bin_op op) [ e1'; e2']	
    | JCEbinary(e1,Bland,e2) ->
	(* lazy conjunction *)
	let e1' = expr e1 in
	let e2' = expr e2 in
	And(e1',e2')	
    | JCEbinary(e1,Blor,e2) ->
	(* lazy disjunction *)
	let e1' = expr e1 in
	let e2' = expr e2 in
	Or(e1',e2')	
    | JCEbinary(e1,op,e2) ->
	let e1' = expr e1 in
	let e2' = expr e2 in
	let t = bin_arg_type e.jc_expr_loc op in
	make_app (bin_op op) 
	  [ coerce e1.jc_expr_loc t e1.jc_expr_type e1'; 
	    coerce e2.jc_expr_loc t e2.jc_expr_type e2']	
    | JCEif(e1,e2,e3) -> 
	let e1 = expr e1 in
	let e2 = expr e2 in
	let e3 = expr e3 in
	If(e1,e2,e3)
    | JCEshift(e1,e2) -> 
	let e1' = expr e1 in
	let e2' = expr e2 in
	make_app "shift" 
	  [e1'; 
	   coerce e2.jc_expr_loc integer_type e2.jc_expr_type e2']
    | JCEoffset(k,e,st) -> 
	let alloc =
	  st.jc_struct_info_root ^ "_alloc_table"
	in
	let f = match k with
	  | Offset_min -> "offset_min"
	  | Offset_max -> "offset_max"
	in
	make_app f [Deref alloc; expr e] 
    | JCEinstanceof(e,t) ->
	let e = expr e in
	let tag = t.jc_struct_info_root ^ "_tag_table" in
	make_app "instanceof_" [Deref tag; e; Var (tag_name t)]
    | JCEcast(e,t) ->
	let e = expr e in
	let tag = t.jc_struct_info_root ^ "_tag_table" in
	make_app "downcast_" [Deref tag; e; Var (tag_name t)]
    | JCEderef(e,fi) -> 
	make_app "acc_"
	  [ Var (fi.jc_field_info_root ^ "_alloc_table") ;
	    Var fi.jc_field_info_name ; 
	    (* coerce e.jc_expr_loc integer_type e.jc_expr_type *) (expr e) ]



let invariant_for_struct this st =
  let (_,invs) = 
    Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name 
  in
  make_and_list 
    (List.map (fun (li,_) -> make_logic_pred_call li [this]) invs)

let any_value = function
  | JCTnative t -> 
      begin match t with
	| Tunit -> assert false (* TODO *)
	| Tboolean -> assert false (* TODO *)
	| Tinteger ->
	    App (Var "any_integer", Void)
	| Treal -> assert false (* TODO *)
      end
  | _ -> assert false (* TODO *)
  
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
    | JCSassign_local (vi, e2) -> 
	let e2' = expr e2 in
	let n = vi.jc_var_info_final_name in
	Assign(n, coerce e2.jc_expr_loc vi.jc_var_info_type e2.jc_expr_type e2')
    | JCSassign_heap(e1,fi,e2) -> 
	let e1' = expr e1 in
	let e2' = expr e2 in
	let tmp1 = tmp_var_name () in
	let tmp2 = tmp_var_name () in
        (append
	   (make_lets
	      ([ (tmp1, e1') ; (tmp2, coerce e2.jc_expr_loc fi.jc_field_info_type e2.jc_expr_type e2') ])
	      (append
		 (assert_mutable (LVar tmp1) fi)
		 (make_upd fi (Var tmp1) (Var tmp2))))
	   (assume_field_invariants fi))
(*	   (make_assume_field_assocs (fresh_program_point ()) fi)) *)
    | JCSblock l -> statement_list l
    | JCSif (e, s1, s2) -> 
	let e = expr e in
	If(e, statement s1, statement s2)
    | JCSloop (la, s) -> 
	While(Cte(Prim_bool true), assertion None "init" la.jc_loop_invariant,
	      Some (term None "" la.jc_loop_variant,None), [statement s])
    | JCSassert(None, a) -> Assert(assertion None "init" a, Void)
    | JCSassert(Some name, a) -> 
	Assert(LNamed(name,assertion None "init" a), Void)
    | JCSdecl(vi,e,s) -> 
	begin
	  let e',t = match e with
	    | None -> any_value vi.jc_var_info_type, vi.jc_var_info_type 
	    | Some e -> expr e, e.jc_expr_type
	  in
	  if vi.jc_var_info_assigned then 
	    Let_ref(vi.jc_var_info_final_name, 
		    coerce s.jc_statement_loc vi.jc_var_info_type t e', 
		    statement s)
	  else 
	    Let(vi.jc_var_info_final_name,
		coerce s.jc_statement_loc vi.jc_var_info_type t e', 
		statement s)
	end
    | JCSreturn(t,e) -> 
	coerce e.jc_expr_loc t e.jc_expr_type (expr e)
    | JCSunpack(st, e) ->
	(* La méthode consistant à placer unpack_ dans jessie.why ne marche pas
quand il y a un unpack par type structure. *)
	(* let e = expr e in make_app "unpack_" [e] *)
	let e = expr e in make_app ("unpack_"^st.jc_struct_info_root) [e]
    | JCSpack(st,e) ->
	let e = expr e in make_app ("pack_"^st.jc_struct_info_root) [e]
(*	let e = expr e in
	let tmp = tmp_var_name() in
	make_lets ([(tmp,e)])
	  (Assert(invariant_for_struct (LVar tmp) st, 
		  make_app "pack_" [Var tmp])) *)
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
  (*let tmp = "this" in
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
  in*)
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

let interp_fun_params f annot_type =
  match f.jc_fun_info_parameters with
    | [] ->
	Prod_type("tt",unit_type, annot_type)
    | l ->
	List.fold_right
	  (fun v acc ->
	     Prod_type(v.jc_var_info_final_name,
		       tr_type v.jc_var_info_type,
		       acc))
	  l annot_type
       
let tr_fun f spec body acc =
  (* Calculate invariants (for each parameter), that will be used as pre and post conditions *)
  let invariants =
    (* (* with the inv predicate (DISABLED) *) List.fold_right
      (fun v acc ->
	 match v.jc_var_info_type with
	   | JCTpointer(st,_,_) ->
	       let var = LVar v.jc_var_info_final_name in
	       (*let invariant = invariant_for_struct var st in
	       make_and invariant acc*)
               let params = valid_inv_params st in
               let params = List.map (fun (s, _) -> LVar s) params in
               make_and (LPred(valid_inv_name st, var::params)) acc
           | JCTnull -> assert false
	   | JCTrange _ -> acc
	   | JCTnative _ -> acc
	   | JCTlogic _ -> acc)
      f.jc_fun_info_parameters *)
      LTrue
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
           | JCTnull -> assert false
	   | JCTenum _ -> acc
	   | JCTnative _ -> acc
	   | JCTlogic _ -> acc)
      f.jc_fun_info_parameters
      (assertion None "" spec.jc_fun_requires)
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
  (* DEBUG *)
  (* List.iter (Printf.printf "*** %s\n") reads;
  flush stdout; *)
  (* why parameter for calling the function *)
  let why_param = 
    let annot_type =
      Annot_type(requires,tr_type f.jc_fun_info_return_type,
		 reads,writes, normal_post, excep_posts)
    in
    let fun_type = interp_fun_params f annot_type in
    Param(false,f.jc_fun_info_name,fun_type)
  in
  match body with
    | None -> 
	(* function was only declared *)
	why_param :: acc
    | Some body ->
	(* why functions for each behaviors *)
	let params = match f.jc_fun_info_parameters with
	  | [] -> ["tt", unit_type]
	  | l -> List.map parameter l
	in
	(* rename formals just before body is treated *)
	let list_of_refs =
	  List.fold_right
	    (fun id bl ->
	       if id.jc_var_info_assigned
	       then 
		 let n = id.jc_var_info_final_name in
		 let newn = "mutable_" ^ n in
		 id.jc_var_info_final_name <- newn;
		 (newn, n) :: bl
	       else bl) 
	    f.jc_fun_info_parameters [] 
	in
	let body = statement_list body in
	let tblock =
	  append
	    (*      (make_assume_all_assocs (fresh_program_point ()) f.jc_fun_info_parameters)*)
	    (assume_all_invariants f.jc_fun_info_parameters)
	    body
	in
	let tblock = make_label "init" tblock in
	let tblock =
	  List.fold_right
	    (fun (mut_id,id) bl ->
	       Let_ref(mut_id,Var(id),bl)) list_of_refs tblock 
	in
	let acc =
	  List.fold_right
	    (fun (id,b,e) acc ->
	       let d =
		 Def(
		   f.jc_fun_info_name ^ "_ensures_" ^ id,
		   Fun(
		     params,
		     requires,
		     tblock,
		     e,
		     excep_posts_for_others None excep_behaviors
		   )
		 )
	       in d::acc)
	    normal_behaviors acc
	in 
	(* redefine [tblock] for use in exception functions *)
	let tblock = make_label "init" tblock in
	let tblock =
	  List.fold_right
	    (fun (mut_id,id) bl ->
	       Let_ref(mut_id,Var(id),bl)) list_of_refs tblock 
	in
	let acc =
	  ExceptionMap.fold
	    (fun ei l acc ->
	       List.fold_right
		 (fun (id,b,e) acc ->
		    let d =
		      Def(f.jc_fun_info_name ^ "_exsures_" ^ id,
			  Fun(params,
			      requires,
			      tblock,
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

let tr_enum_type ri to_int of_int acc =
  let n = ri.jc_enum_info_name in
  let enum_pred x =
    LAnd(LPred("le_int",[LConst(Prim_int(Num.string_of_num(ri.jc_enum_info_min))); x]),
	       LPred("le_int",[x; LConst(Prim_int(Num.string_of_num(ri.jc_enum_info_max)))]))
  in
  let of_int_type =
    Prod_type("x", Base_type(simple_logic_type "integer"),
	      Annot_type(enum_pred (LVar "x"),
			 Base_type(simple_logic_type n),
			 [],[],
			 LPred("eq_int",
			       [LVar "x";LApp(to_int.jc_fun_info_name,[LVar "result"])]),[]))
  in
  Type(n,[]) ::
  Logic(false,to_int.jc_fun_info_name,
	[("",simple_logic_type n)],simple_logic_type "integer") :: 
  Param(false,of_int.jc_fun_info_name,of_int_type) ::
  Axiom(n^"_enum",
	LForall("x",simple_logic_type n,enum_pred (LApp(to_int.jc_fun_info_name,[LVar "x"]))))		
  :: acc

let tr_variable vi e acc =
  let t = 
    if vi.jc_var_info_assigned then
      Ref_type(tr_type vi.jc_var_info_type)
    else
      tr_type vi.jc_var_info_type
  in
  Param(false,vi.jc_var_info_name,t)::acc
	   
(*
Local Variables: 
compile-command: "unset LANG; make -C .. bin/jessie.byte"
End: 
*)
