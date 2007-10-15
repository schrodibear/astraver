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
open Format

(* locs table *)


type kind =
  | ArithOverflow
  | DownCast
  | IndexBounds
  | PointerDeref
  | UserCall
  | DivByZero
  | Pack
  | Unpack

let locs_table = Hashtbl.create 97
let name_counter = ref 0

let abs_fname f =
  if Filename.is_relative f then
    Filename.concat (Unix.getcwd ()) f 
  else f

let reg_loc ?name ?kind (b,e) =  
  let id = match name with
    | None ->  
	incr name_counter;
	  "JC_" ^ string_of_int !name_counter
    | Some n -> n
  in
(*
  Format.eprintf "Jc_interp: reg_loc id = '%s'@." id;
*)
  let (f,l,b,e) = 
    try
      match name with
	| None -> 
	    raise Not_found
	| Some n -> 
	    let (f,l,b,e,o) = Hashtbl.find Jc_options.locs_table n in
(*
	    Format.eprintf "Jc_interp: reg_loc id '%s' found@." id;
*)
	    Jc_options.lprintf "keeping old location for id '%s'@." n;
	    (f,l,b,e)
    with Not_found ->
(*
      Format.eprintf "Jc_interp: reg_loc id '%s' not found@." id;
*)
      let f = abs_fname b.Lexing.pos_fname in
      let l = b.Lexing.pos_lnum in
      let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
      let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
      (f,l,fc,lc)
  in
  Jc_options.lprintf "recording location for id '%s'@." id;
  Hashtbl.replace locs_table id (kind,f,l,b,e);
  id
    
let print_kind fmt k =
  fprintf fmt "%s"
    (match k with
       | Pack -> "Pack"
       | Unpack -> "Unpack"
       | DivByZero -> "DivByZero"
       | UserCall -> "UserCall"
       | PointerDeref -> "PointerDeref"
       | IndexBounds -> "IndexBounds"
       | DownCast -> "DownCast"
       | ArithOverflow -> "ArithOverflow"
    )

let print_locs fmt =
  Hashtbl.iter 
    (fun id (k,f,l,b,e) ->
       fprintf fmt "[%s]@\n" id;
       begin
	 match k with
	   | None -> ()
	   | Some k -> fprintf fmt "kind = %a@\n" print_kind k
       end;
       fprintf fmt "file = \"%s\"@\n" f;
       fprintf fmt "line = %d@\n" l;
       fprintf fmt "begin = %d@\n" b;
       fprintf fmt "end = %d@\n@\n" e)
    locs_table


(* consts *)

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

let why_integer_type = simple_logic_type "int"
  
let tr_base_type t =
  match t with
    | JCTnative t -> simple_logic_type (tr_native_type t)
    | JCTlogic s -> simple_logic_type s
    | JCTenum ri -> 
	simple_logic_type ri.jc_enum_info_name
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

let logic_enum_of_int n = n.jc_enum_info_name ^ "_of_integer"
let safe_fun_enum_of_int n = "safe_" ^ n.jc_enum_info_name ^ "_of_integer_"
let fun_enum_of_int n = n.jc_enum_info_name ^ "_of_integer_"
let logic_int_of_enum n = "integer_of_" ^ n.jc_enum_info_name
let fun_any_enum n = "any_" ^ n.jc_enum_info_name

let term_coerce loc tdest tsrc e =
  match tdest, tsrc with
  | JCTnative t, JCTnative u when t=u -> e
  | JCTlogic t, JCTlogic u when t=u -> e
  | JCTenum ri1, JCTenum ri2 when ri1==ri2 -> e
  | JCTnative Tinteger, JCTnative Tunit -> e (* hack for ai - Nicolas *)
  | JCTnative Tinteger, JCTenum ri ->
      LApp(logic_int_of_enum ri,[e])
  | JCTenum ri, JCTnative Tinteger ->
      LApp(logic_enum_of_int ri,[e])
  | JCTpointer (st1, _, _), JCTpointer(st2,_,_) 
    when Jc_typing.substruct st2 st1 -> e
  | JCTpointer (st, a, b), (JCTpointer(_,_,_) | JCTnull)  -> 
      LApp("downcast", 
	   [ LVar (st.jc_struct_info_root ^ "_tag_table") ; e ;
	     LVar (st.jc_struct_info_name ^ "_tag") ])	
  |  _ -> 
      Jc_typing.typing_error loc 
	"can't coerce type %a to type %a" 
	print_type tsrc print_type tdest
	
let make_guarded_app ?name (k:kind) loc f l =
  let lab =
    match name with
      | None | Some "" -> reg_loc ~kind:k loc
      | Some n -> reg_loc ~name:n ~kind:k loc
  in
  Label(lab,make_app f l)

let coerce ~no_int_overflow lab loc tdest tsrc e =
  match tdest,tsrc with
    | JCTnative t, JCTnative u when t=u -> e
    | JCTlogic t, JCTlogic u when t=u -> e
    | JCTenum ri1, JCTenum ri2 when ri1==ri2 -> e
    | JCTenum ri1, JCTenum ri2 -> 
	let e' = make_app (logic_int_of_enum ri2) [e] in
	if no_int_overflow then 
	  make_app (safe_fun_enum_of_int ri1) [e']
	else
	  make_guarded_app ~name:lab ArithOverflow loc 
	    (fun_enum_of_int ri1) [e']
    | JCTnative Tinteger, JCTenum ri ->
	make_app (logic_int_of_enum ri) [e]
    | JCTenum ri, JCTnative Tinteger ->
	if no_int_overflow then 
	  make_app (safe_fun_enum_of_int ri) [e]
	else
	  make_guarded_app ~name:lab ArithOverflow loc (fun_enum_of_int ri) [e]
    | _ , JCTnull -> e
    | JCTpointer (st, a, b), _  -> 
	make_guarded_app ~name:lab DownCast loc "downcast_" 
	  [ Deref (st.jc_struct_info_root ^ "_tag_table") ; e ;
	    Var (st.jc_struct_info_name ^ "_tag") ]	
    |  _ -> 
	 Jc_typing.typing_error loc 
	   "can't coerce type %a to type %a" 
	   print_type tsrc print_type tdest

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
	let t1' = ft t1 in
	LApp (unary_op op, 
	      [term_coerce t.jc_term_loc 
		 (unary_arg_type op) t1.jc_term_type t1' ])
    | JCTbinary(t1,((Beq_pointer | Bneq_pointer) as op),t2) ->
	let t1' = ft t1 in
	let t2' = ft t2 in
	LApp (bin_op op, [ t1'; t2'])
    | JCTbinary(t1,Bland,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,Blor,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,op,t2) ->
	let t1' = ft t1 in
	let t2' = ft t2 in
	let t = bin_arg_type t.jc_term_loc op in
	LApp (bin_op op, 
	      [ term_coerce t1.jc_term_loc t 
		  t1.jc_term_type t1'; 
		term_coerce t2.jc_term_loc t 
		  t2.jc_term_type t2'])
    | JCTshift(t1,t2) -> 
	let t2' = ft t2 in
	LApp("shift",[ft t1; 
		      term_coerce t2.jc_term_loc integer_type 
			t2.jc_term_type t2'])
    | JCTsub_pointer(t1,t2) -> 
	LApp("sub_pointer",[ft t1; ft t2])
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

let tag label oldlabel = function
  | JCTtag st -> LVar (st.jc_struct_info_root^"_tag")
  | JCTbottom -> LVar "bottom_tag"
  | JCTtypeof(t, st) ->
      let te = term label oldlabel t in
      LApp("typeof", [ LVar (st.jc_struct_info_root^"_tag_table"); te ])
	     

let rec assertion label oldlabel a =
  let fa = assertion label oldlabel 
  and ft = term label oldlabel
  and ftag = tag label oldlabel
  in
  let a' =
    match a.jc_assertion_node with
      | JCAtrue -> LTrue
      | JCAfalse -> LFalse
      | JCAif(t1,p2,p3) -> LIf(ft t1,fa p2,fa p3)
      | JCAand l -> make_and_list (List.map fa l)
      | JCAor l -> make_or_list (List.map fa l)
      | JCAimplies(a1,a2) -> make_impl (fa a1) (fa a2)
      | JCAiff(a1,a2) -> make_equiv (fa a1) (fa a2)
      | JCAnot(a) -> LNot(fa a)
      | JCArelation(t1,((Beq_pointer | Bneq_pointer) as op),t2) ->
	  let t1' = ft t1 in
	  let t2' = ft t2 in
	  LPred (pred_bin_op op, [ t1'; t2'])
      | JCArelation(t1,op,t2) ->
	  let t1' = ft t1 in
	  let t2' = ft t2 in
	  let t = bin_arg_type a.jc_assertion_loc op in
	  LPred(pred_bin_op op, 
		[ term_coerce t1.jc_term_loc t
		    t1.jc_term_type t1'; 
		  term_coerce t2.jc_term_loc t 
		    t2.jc_term_type t2'])
      | JCAapp(f,l) -> 
	  begin try
	    make_logic_pred_call f 
	      (List.map2 
		 (fun vi t -> 
		    term_coerce t.jc_term_loc 
		      vi.jc_var_info_type t.jc_term_type (ft t))
		 f.jc_logic_info_parameters l)	    
	  with Invalid_argument _ -> assert false
	  end
      | JCAquantifier(Forall,v,p) -> 
	LForall(v.jc_var_info_final_name,
		tr_base_type v.jc_var_info_type,
		fa p)
      | JCAquantifier(Exists,v,p) -> 
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
      | JCAmutable(te, st, ta) ->
	  let mutable_field = LVar (mutable_name st.jc_struct_info_root) in
	  let tag = ftag ta.jc_tag_node in
	  LPred("eq", [ LApp("select", [ mutable_field; ft te ]); tag ])
      | JCAtagequality(t1, t2, h) ->
	  LPred("eq", [ ftag t1.jc_tag_node; ftag t2.jc_tag_node ])
  in
  if a.jc_assertion_label <> "" then
    LNamed(reg_loc ~name:a.jc_assertion_label a.jc_assertion_loc,a')
  else
    a'
  

(****************************

logic functions

****************************)

let tr_logic_const vi init acc =
  let decl =
    Logic(false,vi.jc_var_info_name,[], tr_base_type vi.jc_var_info_type) :: acc
  in
  match init with
      | None -> decl
      | Some t ->
	  Axiom(vi.jc_var_info_name ^ "_value_axiom" , 
		LPred("eq",[term_coerce Loc.dummy_position integer_type
			      vi.jc_var_info_type (LVar vi.jc_var_info_name); 
			    term_coerce t.jc_term_loc integer_type 
			      t.jc_term_type (term None "" t)])) 
	  :: decl 

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

type shift_offset = Int_offset of string | Expr_offset of Jc_ast.expr 

let bounded lb rb s =
  let n = Num.num_of_string s in Num.le_num lb n && Num.le_num n rb

let lbounded lb s =
  let n = Num.num_of_string s in Num.le_num lb n

let rbounded rb s =
  let n = Num.num_of_string s in Num.le_num n rb

let destruct_pointer e = 
  let ptre,off = match e.jc_expr_node with
    | JCEshift(e1,e2) -> 
	begin match e2.jc_expr_node with
	| JCEconst (JCCinteger s) -> 
	    e1,Int_offset s
	| JCEconst _ -> assert false
	| _ ->
	    e1,Expr_offset e2
	end
    | _ -> e,Int_offset "0"
  in
  match ptre.jc_expr_type with
  | JCTpointer(_,lb,rb) -> ptre,off,lb,rb
  | _ -> assert false

let rec make_lets l e =
  match l with
    | [] -> e
    | (tmp,a)::l -> Let(tmp,a,make_lets l e)

let rec make_upd loc ~threats fi e1 v =
  let expr = expr ~threats and offset = offset ~threats in
  if threats then
    match destruct_pointer e1 with
    | _,Int_offset s,Some lb,Some rb when bounded lb rb s ->
	make_app "safe_upd_" 
	  [ Var fi.jc_field_info_name ; expr e1; v ]
    | p,(Int_offset s as off),Some lb,Some rb when lbounded lb s ->
	make_guarded_app IndexBounds loc "lsafe_bound_upd_" 
	  [ Var fi.jc_field_info_name ; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,(Int_offset s as off),Some lb,Some rb when rbounded rb s ->
	make_guarded_app IndexBounds loc "rsafe_bound_upd_" 
	  [ Var fi.jc_field_info_name ; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num lb)); v ]
    | p,off,Some lb,Some rb ->
	make_guarded_app IndexBounds loc "bound_upd_" 
	  [ Var fi.jc_field_info_name ; expr p; offset off; 
	    Cte (Prim_int (Num.string_of_num lb)); 
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,(Int_offset s as off),Some lb,None when lbounded lb s ->
	make_guarded_app IndexBounds loc "lsafe_lbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var fi.jc_field_info_name; expr p; offset off; v ]
    | p,off,Some lb,None ->
	make_guarded_app IndexBounds loc "lbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var fi.jc_field_info_name; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num lb)); v ]
    | p,(Int_offset s as off),None,Some rb when rbounded rb s ->
	make_guarded_app IndexBounds loc "rsafe_rbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var fi.jc_field_info_name; expr p; offset off; v ]
    | p,off,None,Some rb ->
	make_guarded_app IndexBounds loc "rbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var fi.jc_field_info_name; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | _,_,None,None ->
	make_guarded_app PointerDeref loc "upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var fi.jc_field_info_name ; expr e1; v ]
  else
    make_app "safe_upd_"
      [ Var fi.jc_field_info_name ; expr e1 ; v ]
    
and offset ~threats = function
  | Int_offset s -> Cte (Prim_int s)
  | Expr_offset e -> 
      coerce ~no_int_overflow:(not threats) 
	e.jc_expr_label e.jc_expr_loc integer_type e.jc_expr_type 
	(expr ~threats e)

and expr ~threats e : expr =
  let expr = expr ~threats and offset = offset ~threats in
  let loc = e.jc_expr_loc in
  let e' =
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
	  [coerce ~no_int_overflow:(not threats) 
	     e1.jc_expr_label loc (unary_arg_type op) e1.jc_expr_type e1' ]
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
	let t = bin_arg_type loc op in
	(match op with
	   | Bdiv_int | Bdiv_real | Bmod_int ->
	       make_guarded_app DivByZero loc
	   | _ -> make_app)
	  (bin_op op) 
	  [ coerce ~no_int_overflow:(not threats) 
	      e1.jc_expr_label e1.jc_expr_loc t e1.jc_expr_type e1'; 
	    coerce ~no_int_overflow:(not threats) 
	      e2.jc_expr_label e2.jc_expr_loc t e2.jc_expr_type e2']	
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
	   coerce ~no_int_overflow:(not threats) 
	     e2.jc_expr_label e2.jc_expr_loc integer_type e2.jc_expr_type e2']
    | JCEsub_pointer(e1,e2) -> 
	let e1' = expr e1 in
	let e2' = expr e2 in
	(* FIXME: need to check that are in the same block *)
	make_app "sub_pointer" [ e1'; e2']
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
	(* always safe *)
	make_app "instanceof_" [Deref tag; e; Var (tag_name t)]
    | JCEcast(e1,t) ->
	let e1 = expr e1 in
	let tag = t.jc_struct_info_root ^ "_tag_table" in
	make_guarded_app DownCast loc "downcast_" 
	  [Deref tag; e1; Var (tag_name t)]
    | JCErange_cast(ri,e1) ->
	let e1' = expr e1 in
	coerce ~no_int_overflow:(not threats)
	  e.jc_expr_label e.jc_expr_loc (JCTenum ri) e1.jc_expr_type e1'
    | JCEderef(e,fi) ->
	if threats then
	  match destruct_pointer e with
	  | _,Int_offset s,Some lb,Some rb when bounded lb rb s ->
	      make_app "safe_acc_" 
		[ Var fi.jc_field_info_name ; expr e ]
	  | p,(Int_offset s as off),Some lb,Some rb when lbounded lb s ->
	      make_guarded_app IndexBounds loc "lsafe_bound_acc_" 
		[ Var fi.jc_field_info_name ; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,(Int_offset s as off),Some lb,Some rb when rbounded rb s ->
	      make_guarded_app IndexBounds loc "rsafe_bound_acc_" 
		[ Var fi.jc_field_info_name ; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num lb)) ]
	  | p,off,Some lb,Some rb ->
	      make_guarded_app IndexBounds loc "bound_acc_" 
		[ Var fi.jc_field_info_name ; expr p; offset off; 
		  Cte (Prim_int (Num.string_of_num lb)); 
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,(Int_offset s as off),Some lb,None when lbounded lb s ->
	      make_guarded_app IndexBounds loc "lsafe_lbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var fi.jc_field_info_name; expr p; offset off ]
	  | p,off,Some lb,None ->
	      make_guarded_app IndexBounds loc "lbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var fi.jc_field_info_name; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num lb)) ]
	  | p,(Int_offset s as off),None,Some rb when rbounded rb s ->
	      make_guarded_app IndexBounds loc "rsafe_rbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var fi.jc_field_info_name; expr p; offset off ]
	  | p,off,None,Some rb ->
	      make_guarded_app IndexBounds loc "rbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var fi.jc_field_info_name; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | _,_,None,None ->
	      make_guarded_app PointerDeref loc "acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var fi.jc_field_info_name ; expr e ]
	else
	  make_app "safe_acc_"
	    [ Var fi.jc_field_info_name ; 
	      (* coerce e.jc_expr_loc integer_type e.jc_expr_type *) (expr e) ]
    | JCEalloc (e, st) ->
	let alloc = st.jc_struct_info_root ^ "_alloc_table" in
	let tag = st.jc_struct_info_root ^ "_tag_table" in
	begin
	  match Jc_options.inv_sem with
	    | InvOwnership ->
		let mut = Jc_invariants.mutable_name st.jc_struct_info_root in
		let com = Jc_invariants.committed_name st.jc_struct_info_root in
		make_app "alloc_parameter_ownership" 
		  [Var alloc; Var mut; Var com; Var tag; Var (tag_name st); 
		   coerce ~no_int_overflow:(not threats) 
		     e.jc_expr_label e.jc_expr_loc integer_type 
		     e.jc_expr_type (expr e)]
	    | InvArguments | InvNone ->
		make_app "alloc_parameter" 
		  [Var alloc; Var tag; Var (tag_name st); 
		   coerce ~no_int_overflow:(not threats) 
		     e.jc_expr_label e.jc_expr_loc integer_type 
		     e.jc_expr_type (expr e)]
	end
    | JCEfree e ->
	let st = match e.jc_expr_type with
	  | JCTpointer(st, _, _) -> st
	  | _ -> assert false
	in	
	let alloc = st.jc_struct_info_root ^ "_alloc_table" in
	if Jc_options.inv_sem = InvOwnership then
	  let com = Jc_invariants.committed_name st.jc_struct_info_root in
	  make_app "free_parameter_ownership" [Var alloc; Var com; expr e]
	else
	  make_app "free_parameter" [Var alloc; expr e]
  in
(*
  if lab <> "" then
    Label(reg_loc ~name:lab loc,e')
  else
*)
    e'

let invariant_for_struct this st =
  let (_,invs) = 
    Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name 
  in
  make_and_list 
    (List.map (fun (li,_) -> make_logic_pred_call li [this]) invs)

let any_value ty = 
  match ty with
  | JCTnative t -> 
      begin match t with
	| Tunit -> Void
	| Tboolean -> App (Var "any_bool", Void)
	| Tinteger -> App (Var "any_int", Void)
	| Treal -> App (Var "any_real", Void)
      end
  | JCTnull 
  | JCTpointer _ -> App (Var "any_pointer", Void)
  | JCTenum ri -> 
      App (Var ("any_" ^ ri.jc_enum_info_name), Void)
  | JCTlogic _ -> assert false

  
let jessie_return_variable = "jessie_returned_value"
let jessie_return_exception = "Return"
let return_void = ref false

let expr_coerce ~threats vi e =
  coerce ~no_int_overflow:(not threats) 
    e.jc_expr_label e.jc_expr_loc vi.jc_var_info_type 
    e.jc_expr_type (expr ~threats e)
  
let rec statement ~threats s = 
  (* reset_tmp_var(); *)
  let statement = statement ~threats in
  let expr = expr ~threats in
  match s.jc_statement_node with
    | JCScall(vio,f,l,block) -> 
(*
	Format.eprintf "Jc_interp: lab for call = '%s'@."
	  s.jc_statement_label;
*)
	let loc = s.jc_statement_loc in
	let el = 
	  try
	    List.map2 (expr_coerce ~threats) f.jc_fun_info_parameters l 
	  with Invalid_argument _ -> assert false
	in
	let call = 
	  make_guarded_app UserCall loc f.jc_fun_info_name el 
	in
	begin
	  match vio with
	    | None -> 
		(* check that associated statement is empty *)
		begin match block.jc_statement_node with
		  | JCSblock [] -> () (* ok *)
		  | _ -> assert false
		end;
		begin match f.jc_fun_info_return_type with
		| JCTnative Tunit -> call
		| _ -> let tmp = tmp_var_name () in Let(tmp,call,Void)
		end
	    | Some vi ->
		Let(vi.jc_var_info_final_name,call, statement block)
	end
    | JCSassign_var (vi, e2) -> 
	let e2' = expr e2 in
	let n = vi.jc_var_info_final_name in
	Assign(n, coerce ~no_int_overflow:(not threats) 
		 e2.jc_expr_label e2.jc_expr_loc vi.jc_var_info_type 
		 e2.jc_expr_type e2')
    | JCSassign_heap(e1,fi,e2) -> 
	let e1' = expr e1 in
	let e2' = expr e2 in
	let tmp1 = tmp_var_name () in
	let tmp2 = tmp_var_name () in
	let upd = make_upd ~threats s.jc_statement_loc fi e1 (Var tmp2) in
(* Yannick: ignore variables to be able to refine update function used. *)	
(* 	let upd = make_upd ~threats fi (Var tmp1) (Var tmp2) in *)
(* Claude: do not ignore variable tmp2, since it may involve a coercion. 
   Anyway, safety of the update do not depend on e2 *)
	let upd = if threats && Jc_options.inv_sem = InvOwnership then
	  append (assert_mutable (LVar tmp1) fi) upd else upd in
	let lets =
	  (make_lets
	     ([ (tmp1, e1') ; (tmp2, coerce ~no_int_overflow:(not threats) 
				 e2.jc_expr_label e2.jc_expr_loc 
				 fi.jc_field_info_type 
				 e2.jc_expr_type e2') ])
	     upd)
	in
	if Jc_options.inv_sem = InvOwnership then
	  append lets (assume_field_invariants fi)
	else
	  lets
(*	if Jc_options.inv_sem = Jc_options.InvOwnership then   (make_assume_field_assocs (fresh_program_point ()) fi)) *)
    | JCSblock l -> statement_list ~threats l
    | JCSif (e, s1, s2) -> 
	let e = expr e in
	If(e, statement s1, statement s2)
    | JCSloop (la, s) ->
	let la' = assertion None "init" la.jc_loop_invariant in
	let la'' =
	  if la.jc_loop_invariant.jc_assertion_label = "" then
	    LNamed(reg_loc la.jc_loop_invariant.jc_assertion_loc,la')
	  else la'
	in
	begin match la.jc_loop_variant with
	| Some t when threats ->
	    While(Cte(Prim_bool true), la'',
	          Some (term None "" t,None), [statement s])
	| _ ->
	    While(Cte(Prim_bool true), la'',
	          None, [statement s])
	end
    | JCSassert(None, a) -> 
	Assert(LNamed(reg_loc a.jc_assertion_loc,
		      assertion None "init" a), Void)
    | JCSassert(Some name, a) -> 
	Assert(LNamed(reg_loc ~name a.jc_assertion_loc,
		      assertion None "init" a), Void)
    | JCSdecl(vi,e,s) -> 
	begin
	  let e' = match e with
	    | None -> 
		any_value vi.jc_var_info_type
	    | Some e -> 
		coerce ~no_int_overflow:(not threats) 
		  e.jc_expr_label s.jc_statement_loc vi.jc_var_info_type e.jc_expr_type 
		  (expr e)
	  in
	  if vi.jc_var_info_assigned then 
	    Let_ref(vi.jc_var_info_final_name, e', statement s)
	  else 
	    Let(vi.jc_var_info_final_name, e', statement s)
	end
    | JCSreturn_void -> Raise(jessie_return_exception,None)	
    | JCSreturn(t,e) -> 
	append
	  (Assign(jessie_return_variable,
		  coerce ~no_int_overflow:(not threats) 
		    e.jc_expr_label e.jc_expr_loc t e.jc_expr_type (expr e)))
	  (Raise(jessie_return_exception,None))
    | JCSunpack(st, e, as_t) ->
	let e = expr e in 
	make_guarded_app Unpack s.jc_statement_loc
	  ("unpack_"^st.jc_struct_info_root) [e; Var (tag_name as_t)]
    | JCSpack(st, e, from_t) ->
	let e = expr e in 
	make_guarded_app Pack s.jc_statement_loc
	  ("pack_"^st.jc_struct_info_root) [e; Var (tag_name from_t)]
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

and statement_list ~threats l = 
  List.fold_right 
    (fun s acc -> append (statement ~threats s) acc) l Void

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
	let acc = Type(r,[]) ::
	  Param(false,r ^ "_alloc_table",alloc_type) ::
	  Param(false,r ^ "_tag_table",tag_type) :: acc
	in
	(* axiom for parenttag *)
	let name =
	  st.jc_struct_info_name ^ "_parenttag_bottom"
	in
	let p =
	  LPred("parenttag", [ LVar (tag_name st); LVar "bottom_tag" ])
	in
	Axiom(name, p)::acc
    | Some p ->
	(* axiom for instance_of *)
	(*let name =
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
	let acc = 
	  Axiom(name,f)::acc
	in*)
	(* axiom for parenttag *)
	let name =
	  st.jc_struct_info_name ^ "_parenttag_" ^ p.jc_struct_info_name
	in
	let p =
	  LPred("parenttag", [ LVar (tag_name st); LVar (tag_name p) ])
	in
	Axiom(name, p)::acc


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
    | JCLSrange(ls,None,None) ->
	let ls = pset before ls in
	LApp("pset_all", [ls])
    | JCLSrange(ls,None,Some b) ->
	let ls = pset before ls in
	let b' = term (Some before) before b in
	LApp("pset_range_left", 
	     [ls; 
	      term_coerce b.jc_term_loc integer_type b.jc_term_type b'])
    | JCLSrange(ls,Some a,None) ->
	let ls = pset before ls in
	let a' = term (Some before) before a in
	LApp("pset_range_right", 
	     [ls; 
	      term_coerce a.jc_term_loc integer_type a.jc_term_type a'])
    | JCLSrange(ls,Some a,Some b) ->
	let ls = pset before ls in
	let a' = term (Some before) before a in
	let b' = term (Some before) before b in
	LApp("pset_range", 
	     [ls; 
	      term_coerce a.jc_term_loc integer_type a.jc_term_type a'; 
	      term_coerce b.jc_term_loc integer_type b.jc_term_type b'])
	
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
  (* Calculate invariants (for each parameter), that will
     be used as pre and post conditions *)
  let invariants =
    if Jc_options.inv_sem = InvArguments then
      List.fold_left
	(fun acc v ->
	   match v.jc_var_info_type with
	     | JCTpointer(st, _, _) ->
		 make_and acc
		   (invariant_for_struct
		      (LVar v.jc_var_info_final_name) st)
	     | _ -> acc)
	LTrue
	f.jc_fun_info_parameters
    else begin
    (* (* with the inv predicate (DISABLED) *)
      List.fold_right
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
    end
  in
  let requires = spec.jc_fun_requires in
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
	       let validity = match a,b with
		 | None,None -> LTrue
		 | Some a,None ->
		     LPred("le_int",
			  [LApp("offset_min",
				[LVar alloc; var]);
			   LConst (Prim_int (Num.string_of_num a))])
		 | None, Some b ->
		     LPred("ge_int",
			  [LApp("offset_max",
				[LVar alloc; var]);
			   LConst (Prim_int (Num.string_of_num b))])
		 | Some a,Some b ->
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
      (LNamed(reg_loc requires.jc_assertion_loc,assertion None "" requires))
  in
  (* Jc_options.lprintf "DEBUG: tr_fun 1@."; *)
  (* adding invariants to requires *)
  let requires = make_and requires invariants in
  let (normal_behaviors,excep_behaviors) =
    List.fold_left
      (fun (normal,excep) (id,b) ->
	 let post =
	   make_and
	     (LNamed(reg_loc b.jc_behavior_ensures.jc_assertion_loc,
		     assertion None "" b.jc_behavior_ensures))
	     (assigns "" f.jc_fun_info_effects b.jc_behavior_assigns)
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
    VarSet.fold
      (fun v acc -> v.jc_var_info_final_name::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_globals
      reads
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
  let reads =
    StringSet.fold
      (fun v acc -> (mutable_name v)::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_mutable
      reads
  in
  let reads =
    StringSet.fold
      (fun v acc -> (committed_name v)::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_committed
      reads
  in
  let writes =
    FieldSet.fold
      (fun f acc -> f.jc_field_info_name::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_memories
      []
  in
  let writes =
    VarSet.fold
      (fun v acc -> v.jc_var_info_final_name::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_globals
      writes
  in
  let writes =
    StringSet.fold
      (fun v acc -> (v ^ "_alloc_table")::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
      writes
  in
  let writes =
    StringSet.fold
      (fun v acc -> (v ^ "_tag_table")::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_tag_table
      writes
  in
  let writes =
    StringSet.fold
      (fun v acc -> (mutable_name v)::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_mutable
      writes
  in
  let writes =
    StringSet.fold
      (fun v acc -> (committed_name v)::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_committed
      writes
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
  (* Jc_options.lprintf "DEBUG: tr_fun 2@."; *)
  (* why parameter for calling the function *)
  let ret_type = tr_type f.jc_fun_info_return_type in
  let why_param = 
    let annot_type =
      Annot_type(requires,ret_type,
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
	return_void := 
	  (match f.jc_fun_info_return_type with
	    | JCTnative Tunit -> true
	    | _ -> false);		
	(* default behavior *)
	let why_body = statement_list ~threats:true body in
	let tblock =
	  if Jc_options.inv_sem = InvOwnership then
	    append
	      (*      (make_assume_all_assocs (fresh_program_point ()) f.jc_fun_info_parameters)*)
	      (assume_all_invariants f.jc_fun_info_parameters)
	      why_body
	  else
	    why_body
	in
	let tblock = 
	  if !return_void then
	    Try(append tblock (Raise(jessie_return_exception,None)),
		jessie_return_exception,None,Void)
	  else
	    let e = any_value f.jc_fun_info_return_type in
	    Let_ref(jessie_return_variable,e,
		    Try(append tblock Absurd,
			jessie_return_exception,None,
			Deref(jessie_return_variable)))
	in
	let tblock = make_label "init" tblock in
	let tblock =
	  List.fold_right
	    (fun (mut_id,id) bl ->
	       Let_ref(mut_id,Var(id),bl)) list_of_refs tblock 
	in
	let acc =
	  Def(
	    f.jc_fun_info_name ^ "_safety",
	    Fun(
	      params,
	      requires,
	      tblock,
	      invariants,
	      excep_posts_for_others None excep_behaviors
	    )
	  )::acc
	in
	(* user behaviors *)
	let acc = 
	  if spec.jc_fun_behavior = [] then
	    acc
	  else
	    let body = statement_list ~threats:false body in
	    let tblock =
	      if Jc_options.inv_sem = InvOwnership then
		append
		  (*      (make_assume_all_assocs (fresh_program_point ()) f.jc_fun_info_parameters)*)
		  (assume_all_invariants f.jc_fun_info_parameters)
		  body
	      else
		body
	    in
	    let tblock = 
	      if !return_void then
		Try(append tblock (Raise(jessie_return_exception,None)),
		    jessie_return_exception,None,Void)
	      else
		let e = any_value f.jc_fun_info_return_type in
		Let_ref(jessie_return_variable,e,
			Try(append tblock Absurd,
			    jessie_return_exception,None,
			    Deref(jessie_return_variable)))
	    in
	    let tblock = make_label "init" tblock in
	    let tblock =
	      List.fold_right
		(fun (mut_id,id) bl ->
		   Let_ref(mut_id,Var(id),bl)) list_of_refs tblock 
	    in
	    (* normal behaviors *)
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
	    (* CLAUDE: pourquoi ??????
	       let tblock = make_label "init" tblock in
	       let tblock =
	       List.fold_right
	       (fun (mut_id,id) bl ->
	       Let_ref(mut_id,Var(id),bl)) list_of_refs tblock 
	       in
	    *)
	    (* exceptional behaviors *)
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
	    in acc
	in why_param::acc

let tr_logic_type id acc = Type(id,[])::acc

let tr_axiom id p acc = 
  Axiom(id,assertion None "" p)::acc

let tr_exception ei acc =
  let typ = match ei.jc_exception_info_type with
    | Some tei -> Some (tr_base_type tei)
    | None -> None
  in
  Exception(ei.jc_exception_info_name, typ) :: acc

let tr_enum_type ri (* to_int of_int *) acc =
  let n = ri.jc_enum_info_name in
  let enum_pred x =
    LAnd(LPred("le_int",[LConst(Prim_int(Num.string_of_num(ri.jc_enum_info_min))); x]),
	       LPred("le_int",[x; LConst(Prim_int(Num.string_of_num(ri.jc_enum_info_max)))]))
  in
  let safe_of_int_type =
    Prod_type("x", Base_type(why_integer_type),
	      Annot_type(LTrue,
			 Base_type(simple_logic_type n),
			 [],[],
			 LPred("eq_int",
			       [LVar "x";LApp(logic_int_of_enum ri,
					      [LVar "result"])]),[]))
  in
  let of_int_type =
    Prod_type("x", Base_type(why_integer_type),
	      Annot_type(enum_pred (LVar "x"),
			 Base_type(simple_logic_type n),
			 [],[],
			 LPred("eq_int",
			       [LVar "x";LApp(logic_int_of_enum ri,
					      [LVar "result"])]),[]))
  in
  let any_type =
    Prod_type("", Base_type(simple_logic_type "unit"),
	      Annot_type(LTrue,
			 Base_type(simple_logic_type n),
			 [],[],
			 LTrue,[]))
  in
  Type(n,[]) ::
    Logic(false,logic_int_of_enum ri,
	  [("",simple_logic_type n)],why_integer_type) :: 
    Logic(false,logic_enum_of_int ri,
	  [("",why_integer_type)],simple_logic_type n) :: 
    Param(false,fun_enum_of_int ri,of_int_type) ::
    Param(false,safe_fun_enum_of_int ri,safe_of_int_type) ::
    Param(false,fun_any_enum ri,any_type) ::
    Axiom(n^"_enum",
	  LForall("x",simple_logic_type n,enum_pred 
		    (LApp(logic_int_of_enum ri,[LVar "x"])))) ::
    acc

let tr_variable vi e acc =
  if vi.jc_var_info_assigned then
    let t = Ref_type(tr_type vi.jc_var_info_type) in
    Param(false,vi.jc_var_info_name,t)::acc
  else
    let t = tr_base_type vi.jc_var_info_type in
    Logic(false,vi.jc_var_info_name,[],t)::acc


	   
(*
Local Variables: 
compile-command: "unset LANG; make -C .. bin/jessie.byte"
End: 
*)
