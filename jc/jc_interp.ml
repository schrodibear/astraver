(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
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

(* $Id: jc_interp.ml,v 1.192 2007-12-18 08:55:39 marche Exp $ *)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Jc_invariants
open Output
open Format
open Jc_name
open Jc_region
open Jc_separation

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

let reg_loc ?id ?oldid ?kind ?name ?beh (b,e) =  
  let id,oldid = match id,oldid with
    | None,_ ->  
	incr name_counter;
	"JC_" ^ string_of_int !name_counter, oldid
    | Some n, None -> n,Some n
    | Some n, Some o -> n, Some o
  in
(*
  Format.eprintf "Jc_interp: reg_loc id = '%s'@." id;
*)
  let (name,f,l,b,e) = 
    try
      match oldid with
	| None -> 
	    raise Not_found
	| Some n -> 
	    let (f,l,b,e,o) = Hashtbl.find Jc_options.locs_table n in
(*
	    Format.eprintf "Jc_interp: reg_loc id '%s' found@." oldid;
*)
	    Jc_options.lprintf "keeping old location for id '%s'@." n;
	    let n =
	      try 
		match List.assoc "name" o with
		  | Rc.RCident s | Rc.RCstring s -> Some s
		  | _ -> raise Not_found
	      with Not_found -> name
	    in
	    (n,f,l,b,e)
    with Not_found ->
(*
      Format.eprintf "Jc_interp: reg_loc id '%s' not found@." id;
*)
      let f = abs_fname b.Lexing.pos_fname in
      let l = b.Lexing.pos_lnum in
      let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
      let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
      (name,f,l,fc,lc)
  in
  Jc_options.lprintf "recording location for id '%s'@." id;
  Hashtbl.replace locs_table id (kind,name,beh,f,l,b,e);
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
    (fun id (kind,name,beh,f,l,b,e) ->
       fprintf fmt "[%s]@\n" id;
       Option_misc.iter
	 (fun k -> fprintf fmt "kind = %a@\n" print_kind k) kind;
       Option_misc.iter
	 (fun n -> fprintf fmt "name = \"%s\"@\n" n) name;
       Option_misc.iter
	 (fun b -> fprintf fmt "behavior = \"%s\"@\n" b) beh;
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
    | JCCinteger s -> Prim_int (Num.string_of_num (Numconst.integer s))
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

let tr_type t = Base_type (tr_base_type t)

 

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
  | Bdiv_int -> "div_int_"
  | Bmod_int -> "mod_int_"
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
  | Beq_bool -> "eq_bool_"
  | Bneq_bool -> "neq_bool_"
  | Bbw_and -> "bw_and"
  | Bbw_or -> "bw_or"
  | Bbw_xor -> "bw_xor"
  | Bshift_left -> "lsl"
  | Blogical_shift_right -> "lsr"
  | Barith_shift_right -> "asr"
  | Blor | Bland -> assert false (* should be handled before for laziness *)
  | Biff | Bimplies -> assert false (* never in expressions *)

let term_bin_op = function
  | Bgt_int -> "gt_int"
  | Blt_int -> "lt_int"
  | Bge_int -> "ge_int"
  | Ble_int -> "le_int"
  | Beq_int -> "eq_int"
  | Bneq_int -> "neq_int"
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
  | Bneq_real -> "neq_real"
  | Beq_real -> "eq_real"
  | Bge_real -> "ge_real"
  | Ble_real -> "le_real"
  | Bgt_real -> "gt_real"
  | Blt_real -> "lt_real"
  | Beq_bool -> "eq_bool"
  | Bneq_bool -> "neq_bool"
  | Bbw_and -> "bw_and"
  | Bbw_or -> "bw_or"
  | Bbw_xor -> "bw_xor"
  | Bshift_left -> "lsl"
  | Blogical_shift_right -> "lsr"
  | Barith_shift_right -> "asr"
  | Blor | Bland -> assert false (* should be handled before for laziness *)
  | Biff | Bimplies -> assert false (* never in terms *)

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
  | Bbw_and | Bbw_or | Bbw_xor 
  | Blogical_shift_right | Barith_shift_right | Bshift_left -> integer_type
  | Biff|Bimplies|Blor|Bland -> boolean_type
  | Bdiv_real | Bmul_real | Bsub_real | Badd_real
  | Bneq_real | Beq_real | Bge_real
  | Ble_real | Bgt_real | Blt_real -> real_type
  | Beq_bool | Bneq_bool -> boolean_type
  | Bneq_pointer | Beq_pointer -> assert false

let equality_op_for_type = function
  | JCTnative Tunit -> assert false
  | JCTnative Tboolean -> "eq_bool"
  | JCTnative Tinteger -> "eq_int"
  | JCTnative Treal -> "eq_real"
  | JCTlogic s -> (* TODO *) assert false
  | JCTenum ei -> "eq_int"
  | JCTpointer _ -> "eq_pointer"
  | JCTnull ->  "eq_pointer"

(*
let logic_enum_of_int n = n.jc_enum_info_name ^ "_of_integer"
*)
let safe_fun_enum_of_int n = "safe_" ^ n.jc_enum_info_name ^ "_of_integer_"
let fun_enum_of_int n = n.jc_enum_info_name ^ "_of_integer_"
let logic_int_of_enum n = "integer_of_" ^ n.jc_enum_info_name
let fun_any_enum n = "any_" ^ n.jc_enum_info_name

let term_coerce loc tdest tsrc e =
  match tdest, tsrc with
  | JCTnative t, JCTnative u when t=u -> e
  | JCTlogic t, JCTlogic u when t=u -> e
  | JCTenum ri1, JCTenum ri2 when ri1==ri2 -> e
  | JCTnative Tinteger, JCTenum ri ->
      LApp(logic_int_of_enum ri,[e])
  | JCTenum ri, JCTnative Tinteger ->
      assert false (* a explicit cast should be required by jc_typing *)
      (* LApp(logic_enum_of_int ri,[e]) *)
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
	
let make_guarded_app ~name (k : kind) loc f l =
  let lab =
    match name with
      | "" -> reg_loc ~kind:k loc
      | n -> reg_loc ~id:n ~kind:k loc
  in
  Label (lab, make_app f l)

let coerce ~no_int_overflow lab loc tdest tsrc e =
  match tdest, tsrc with
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
    | JCTpointer (st1,_,_), JCTpointer (st2,_,_) 
	when Jc_typing.substruct st2 st1 -> e
    | JCTpointer (st,_,_), _  -> 
	make_guarded_app ~name:lab DownCast loc "downcast_" 
	  [ Deref (st.jc_struct_info_root ^ "_tag_table") ; e ;
	    Var (st.jc_struct_info_name ^ "_tag") ]	
    | _ -> 
	Jc_typing.typing_error loc 
	  "can't coerce type %a to type %a" 
	  print_type tsrc print_type tdest


(**************************

terms and assertions 

*************************)

let alloc_table_type st = 
  {
    logic_type_name = "alloc_table";
    logic_type_args = [simple_logic_type st.jc_struct_info_root];
  }

let pointer_type st = 
  {
    logic_type_name = "pointer";
    logic_type_args = [simple_logic_type st.jc_struct_info_root];
  }

let tag_table_type st = 
  {
    logic_type_name = "tag_table";
    logic_type_args = [simple_logic_type st.jc_struct_info_root];
  }

let tag_id_type st = 
  {
    logic_type_name = "tag_id";
    logic_type_args = [simple_logic_type st.jc_struct_info_root];
  }

let lvar ?(assigned=true) label v =
  if assigned then
    match label with 
      | None -> LVar v 
      | Some l -> LVarAtLabel(v,l)
  else LVar v

let var v = Var v

let lvar_info label v = 
  if v.jc_var_info_name = "\\result" then 
    v.jc_var_info_final_name <- "result";
  lvar ~assigned:v.jc_var_info_assigned label v.jc_var_info_final_name

let logic_params li l =
  let l =
    FieldRegionSet.fold
      (fun (fi,r) acc -> (LVar(field_region_memory_name(fi,r)))::acc)
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
  LApp(li.jc_logic_info_final_name,params)

let make_logic_pred_call li l =
  let params = logic_params li l in
    LPred (li.jc_logic_info_final_name, params)

let rec term label oldlabel t =
  let ft = term label oldlabel in
  let t' =
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
	LApp (term_bin_op op, [ t1'; t2'])
    | JCTbinary(t1,Bland,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,Blor,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,op,t2) ->
	let t1' = ft t1 in
	let t2' = ft t2 in
	let t = bin_arg_type t.jc_term_loc op in
	LApp (term_bin_op op, 
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
    | JCTderef(t,fi) -> 
	let mem = field_region_memory_name(fi,t.jc_term_region) in
	LApp("select",[lvar label mem;ft t])
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
in
  if t.jc_term_label <> "" then
    Tnamed(reg_loc ~id:t.jc_term_label t.jc_term_loc,t')
  else
    t'

let named_term label oldlabel t =
  let t' = term label oldlabel t in
  match t' with
    | Tnamed _ -> t'
    | _ -> 
	let n = reg_loc t.jc_term_loc in
	Tnamed(n,t')

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
      | JCAapp (f, l) -> 
	  (* No type verification for full_separated for the moment. *)
	  if f.jc_logic_info_name = "full_separated" then
	    make_logic_pred_call f (List.map ft l)
	  else begin try
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
    LNamed(reg_loc ~id:a.jc_assertion_label a.jc_assertion_loc,a')
  else
    a'
  

let named_jc_assertion loc a =
  match a with
    | LNamed _ -> a
    | _ -> let n = reg_loc loc in LNamed(n,a)


let named_assertion label oldlabel a =
  let a' = assertion label oldlabel a in
  named_jc_assertion a.jc_assertion_loc a'


let ( ** ) = fun f g x -> f(g x)

let direct_embedded_struct_fields st =
  List.fold_left 
    (fun acc fi -> 
      match fi.jc_field_info_type with
	| JCTpointer(st', Some _, Some _) -> 
	    assert (st.jc_struct_info_name <> st'.jc_struct_info_name);
	    fi :: acc
	| _ -> acc
    ) [] st.jc_struct_info_fields
    
let embedded_struct_fields st =
  let rec collect forbidden_set st = 
    let forbidden_set = StringSet.add st.jc_struct_info_name forbidden_set in
    let fields = direct_embedded_struct_fields st in
    let fstructs = 
      List.fold_left 
	(fun acc fi -> match fi.jc_field_info_type with
	  | JCTpointer (st', Some _, Some _) -> 
	      assert 
		(not (StringSet.mem st'.jc_struct_info_name forbidden_set));
	      st' :: acc
	   | _ -> assert false
	) [] fields
    in
    fields @ List.flatten (List.map (collect forbidden_set) fstructs)
  in
  let fields = collect (StringSet.singleton st.jc_struct_info_name) st in
  let fields = 
    List.fold_left (fun acc fi -> FieldSet.add fi acc) FieldSet.empty fields
  in
  FieldSet.elements fields
      
let field_sinfo fi = 
  match fi.jc_field_info_type with JCTpointer(st,_,_) -> st | _ -> assert false

let field_bounds fi = 
  match fi.jc_field_info_type with 
    | JCTpointer(_,Some a,Some b) -> a,b | _ -> assert false

let struct_alloc_arg st =
  alloc_table_name st, alloc_table_type st

let field_memory_arg fi =
  field_memory_name fi, memory_field fi


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
    FieldRegionSet.fold
      (fun (fi,r) acc -> 
	 (field_region_memory_name(fi,r), memory_field fi)::acc)
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
    match li.jc_logic_info_result_type, ta with
	(* Predicate *)
      | None, JCAssertion a -> 
	  let a = assertion None "" a in
	    Predicate (false, li.jc_logic_info_final_name,params_reads, a) 
	      (* Function *)
      | Some ty, JCTerm t -> 
	  let ret = tr_base_type ty in
	  let t = term None "" t in
	  Function(false,li.jc_logic_info_final_name,params_reads, ret, t) 
      (* Logic *)
      | tyo, JCReads r ->
	  let ret = match tyo with
	    | None -> simple_logic_type "prop"
	    | Some ty -> tr_base_type ty
	  in
	  Logic(false, li.jc_logic_info_final_name, params_reads, ret)
      (* Other *)
      | _ -> assert false
  in 
  let acc = decl :: acc in
  (* full_separated axioms. *)
  let sep_preds = 
    List.fold_left (fun acc vi ->
      match vi.jc_var_info_type with
	| JCTpointer(st,_,_) -> 
	    LPred("full_separated",[LVar "tmp"; LVar vi.jc_var_info_final_name])
	    :: acc
	| _ -> acc
    ) [] li.jc_logic_info_parameters
  in
  if List.length sep_preds = 0 then acc else
    let params_names = List.map fst params_reads in
    let normal_params = List.map (fun name -> LVar name) params_names in
    FieldRegionSet.fold (fun (fi,r) acc ->
      let update_params = 
	List.map (fun name ->
	  if name = field_region_memory_name(fi,r) then
	    LApp("store",[LVar name;LVar "tmp";LVar "tmpval"])
	  else LVar name
	) params_names
      in
      let a = 
	match li.jc_logic_info_result_type with
	  | None ->
	      LImpl(
		make_and_list sep_preds,
		LIff(
		  LPred(li.jc_logic_info_final_name,normal_params),
		  LPred(li.jc_logic_info_final_name,update_params)))
	  | Some rety ->
	      LImpl(
		make_and_list sep_preds,
		LPred(equality_op_for_type rety,[
		  LApp(li.jc_logic_info_final_name,normal_params);
		  LApp(li.jc_logic_info_final_name,update_params)]))
      in
      let a = 
	List.fold_left (fun a (name,ty) -> LForall(name,ty,a)) a params_reads
      in
      let a = 
	LForall(
	  "tmp",pointer_type fi.jc_field_info_struct,
	  LForall(
	    "tmpval",tr_base_type fi.jc_field_info_type,
	    a))
      in
      Axiom(
	"full_separated_" ^ li.jc_logic_info_name ^ "_" ^ fi.jc_field_info_name,
	a) :: acc
    ) li.jc_logic_info_effects.jc_effect_memories acc
  
(*
let tr_predicate li p acc =
  let params =
    List.map
      (fun vi ->
	 (vi.jc_var_info_final_name,
	   tr_base_type vi.jc_var_info_type))
      li.jc_logic_info_parameters
  in
  Predicate(false,li.jc_logic_info_final_name,params,
	    assertion None "" p) :: acc
*)  

(****************************

expressions and statements

****************************)


let rec is_substruct si1 si2 =
  if si1.jc_struct_info_name = si2.jc_struct_info_name then true else
    match si1.jc_struct_info_parent with
      | None -> false
      | Some si -> is_substruct si si2

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

let rec make_upd lab loc ~threats fi e1 v =
  let expr = expr ~threats and offset = offset ~threats in
  let mem = field_region_memory_name(fi,e1.jc_expr_region) in
  if threats then
    match destruct_pointer e1 with
    | _,Int_offset s,Some lb,Some rb when bounded lb rb s ->
	make_app "safe_upd_" 
	  [ Var mem ; expr e1; v ]
    | p,(Int_offset s as off),Some lb,Some rb when lbounded lb s ->
	make_guarded_app ~name:lab IndexBounds loc "lsafe_bound_upd_" 
	  [ Var mem ; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,(Int_offset s as off),Some lb,Some rb when rbounded rb s ->
	make_guarded_app ~name:lab IndexBounds loc "rsafe_bound_upd_" 
	  [ Var mem ; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num lb)); v ]
    | p,off,Some lb,Some rb ->
	make_guarded_app ~name:lab IndexBounds loc "bound_upd_" 
	  [ Var mem ; expr p; offset off; 
	    Cte (Prim_int (Num.string_of_num lb)); 
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,(Int_offset s as off),Some lb,None when lbounded lb s ->
	make_guarded_app ~name:lab IndexBounds loc "lsafe_lbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var mem; expr p; offset off; v ]
    | p,off,Some lb,None ->
	make_guarded_app ~name:lab IndexBounds loc "lbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var mem; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num lb)); v ]
    | p,(Int_offset s as off),None,Some rb when rbounded rb s ->
	make_guarded_app ~name:lab IndexBounds loc "rsafe_rbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var mem; expr p; offset off; v ]
    | p,off,None,Some rb ->
	make_guarded_app ~name:lab IndexBounds loc "rbound_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var mem; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,Int_offset s,None,None when int_of_string s = 0 ->
	make_guarded_app ~name:lab PointerDeref loc "upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var mem ; expr p; v ]
    | p,off,None,None ->
	make_guarded_app ~name:lab PointerDeref loc "offset_upd_" 
	  [ Var (fi.jc_field_info_root ^ "_alloc_table");
	    Var mem ; expr p; offset off; v ]
  else
    make_app "safe_upd_"
      [ Var mem ; expr e1 ; v ]
    
and offset ~threats = function
  | Int_offset s -> Cte (Prim_int s)
  | Expr_offset e -> 
      coerce ~no_int_overflow:(not threats) 
	e.jc_expr_label e.jc_expr_loc integer_type e.jc_expr_type 
	(expr ~threats e)

and expr ~threats e : expr =
  let expr = expr ~threats and offset = offset ~threats in
  let loc = e.jc_expr_loc in
  let lab = e.jc_expr_label in
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
	     lab loc (unary_arg_type op) e1.jc_expr_type e1' ]
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
	       make_guarded_app ~name:lab DivByZero loc
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
    | JCEcast (e, si) ->
	let tag = tag_table_name si in
	let et = term None "" (term_of_expr e) in
	let typea = 
	  match e.jc_expr_type with
	    | JCTpointer (si', _, _) -> 
		if is_substruct si' si then LTrue else
		  LPred ("instanceof", [LVar tag; et; LVar (tag_name si)])
	    | _ -> LTrue
	in
	let e = expr e in
	let tag = si.jc_struct_info_root ^ "_tag_table" in
	let call = 
	  make_guarded_app ~name:lab DownCast loc "downcast_" 
	    [Deref tag; e; Var (tag_name si)]
	in
	  if typea = LTrue then call else Assert (typea, call)
    | JCErange_cast(ri,e1) ->
	let e1' = expr e1 in
	coerce ~no_int_overflow:(not threats)
	  e.jc_expr_label e.jc_expr_loc (JCTenum ri) e1.jc_expr_type e1'
    | JCEderef(e,fi) ->
	let mem = field_region_memory_name(fi,e.jc_expr_region) in
	if threats then
	  match destruct_pointer e with
	  | _,Int_offset s,Some lb,Some rb when bounded lb rb s ->
	      make_app "safe_acc_" 
		[ Var mem ; expr e ]
	  | p,(Int_offset s as off),Some lb,Some rb when lbounded lb s ->
	      make_guarded_app ~name:lab IndexBounds loc "lsafe_bound_acc_" 
		[ Var mem ; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,(Int_offset s as off),Some lb,Some rb when rbounded rb s ->
	      make_guarded_app ~name:lab IndexBounds loc "rsafe_bound_acc_" 
		[ Var mem ; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num lb)) ]
	  | p,off,Some lb,Some rb ->
	      make_guarded_app ~name:lab IndexBounds loc "bound_acc_" 
		[ Var mem ; expr p; offset off; 
		  Cte (Prim_int (Num.string_of_num lb)); 
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,(Int_offset s as off),Some lb,None when lbounded lb s ->
	      make_guarded_app ~name:lab IndexBounds loc "lsafe_lbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var mem; expr p; offset off ]
	  | p,off,Some lb,None ->
	      make_guarded_app ~name:lab IndexBounds loc "lbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var mem; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num lb)) ]
	  | p,(Int_offset s as off),None,Some rb when rbounded rb s ->
	      make_guarded_app ~name:lab IndexBounds loc "rsafe_rbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var mem; expr p; offset off ]
	  | p,off,None,Some rb ->
	      make_guarded_app ~name:lab IndexBounds loc "rbound_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var mem; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,Int_offset s,None,None when int_of_string s = 0 ->
	      make_guarded_app ~name:lab PointerDeref loc "acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var mem ; expr p ]
	  | p,off,None,None ->
	      make_guarded_app ~name:lab PointerDeref loc "offset_acc_" 
		[ Var (fi.jc_field_info_root ^ "_alloc_table");
		  Var mem ; expr p; offset off ]
	else
	  make_app "safe_acc_"
	    [ Var mem ; 
	      (* coerce e.jc_expr_loc integer_type e.jc_expr_type *) (expr e) ]
    | JCEalloc (siz, st) ->
	let alloc = st.jc_struct_info_root ^ "_alloc_table" in
	let tag = st.jc_struct_info_root ^ "_tag_table" in
	let fields = embedded_struct_fields st in
	let fields = List.map (fun fi -> (fi,e.jc_expr_region)) fields in
	begin
	  match !Jc_options.inv_sem with
	    | InvOwnership ->
		let mut = Jc_invariants.mutable_name st.jc_struct_info_root in
		let com = Jc_invariants.committed_name st.jc_struct_info_root in
		make_app "alloc_parameter_ownership" 
		  [Var alloc; Var mut; Var com; Var tag; Var (tag_name st); 
		   coerce ~no_int_overflow:(not threats) 
		     siz.jc_expr_label siz.jc_expr_loc integer_type 
		     siz.jc_expr_type (expr siz)]
	    | InvArguments | InvNone ->
	      (* Claude : pourquoi un cas particulier pour taille 1 ?? *)
		begin match siz.jc_expr_node with 
		  | JCEconst(JCCinteger "1") ->
		      make_app (alloc_one_param_name st) 
			((List.map (var ** field_region_memory_name) fields)
			@ [Void])
		  | _ ->
		      make_app (alloc_param_name st)
			[coerce ~no_int_overflow:(not threats) 
			  siz.jc_expr_label siz.jc_expr_loc integer_type 
			  siz.jc_expr_type (expr siz)]
		end
	end
    | JCEfree e ->
	let st = match e.jc_expr_type with
	  | JCTpointer(st, _, _) -> st
	  | _ -> assert false
	in	
	let alloc = st.jc_struct_info_root ^ "_alloc_table" in
	if !Jc_options.inv_sem = InvOwnership then
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

(*
let invariant_for_struct this st =
  let (_, invs) = 
    Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name 
  in
  make_and_list
    (List.map (fun (li, _) -> make_logic_pred_call li [this]) invs)
*)

let exception_name ei =
  ei.jc_exception_info_name ^ "_exc"

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

let type_assert vi e =
  match vi.jc_var_info_type, e.jc_expr_type with
    | JCTpointer (si, n1o, n2o), JCTpointer (si', n1o', n2o') ->
	let et = term None "" (term_of_expr e) in
	let alloc = alloc_table_name si in
	let offset_mina = match n1o, n1o' with
	  | None, _ -> LTrue
	  | Some n, Some n' when Num.le_num n' n -> LTrue
	  | Some n, _ -> 
	      LPred ("le_int",
		     [LApp ("offset_min", [LVar alloc; et]);
		      LConst (Prim_int (Num.string_of_num n))])
	in
	let offset_maxa = match n2o, n2o' with
	  | None, _ -> LTrue 
	  | Some n, Some n' when Num.le_num n n' -> LTrue
	  | Some n, _ -> 
	      LPred ("ge_int",
		     [LApp ("offset_max", [LVar alloc; et]);
		      LConst (Prim_int (Num.string_of_num n))])
	in
	  make_and_list [offset_mina; offset_maxa]
    | _ -> LTrue
	
let expr_coerce ~threats vi e =
  coerce ~no_int_overflow:(not threats)
    e.jc_expr_label e.jc_expr_loc vi.jc_var_info_type 
    e.jc_expr_type (expr ~threats e)
    
let rec statement ~threats s = 
  (* reset_tmp_var(); *)
  let statement = statement ~threats in
  let expr = expr ~threats in
  let lab = s.jc_statement_label in
    match s.jc_statement_node with
      | JCScall (vio, call, block) -> 
	  let f = call.jc_call_fun in
	  let l = call.jc_call_args in
	  (*
	    Format.eprintf "Jc_interp: lab for call = '%s'@."
	    s.jc_statement_label;
	  *)
	  let loc = s.jc_statement_loc in
	  let arg_types_assert = 
	    List.fold_left2 (fun acc vi e -> make_and (type_assert vi e) acc) 
	      LTrue f.jc_fun_info_parameters l 
	  in
	  let el =
	    try
	      List.map2 (expr_coerce ~threats) f.jc_fun_info_parameters l 
	    with Invalid_argument _ -> assert false
	  in
	  let mems =
	    FieldRegionSet.fold
	      (fun (fi,r) acc ->
		if r.jc_reg_variable then
		  let r = 
		    try Region.assoc r call.jc_call_region_assoc
		    with Not_found -> assert false
		  in
		  (Var(field_region_memory_name(fi,r)))::acc 
		else acc)
	      (FieldRegionSet.union
		f.jc_fun_info_effects.jc_reads.jc_effect_memories 
		f.jc_fun_info_effects.jc_writes.jc_effect_memories)
	      []
	  in
	  let el = el @ mems in
	  let call = 
	    make_guarded_app ~name:lab UserCall loc 
	      f.jc_fun_info_final_name el 
	  in
	  let call = 
	    if arg_types_assert = LTrue then call else
	      Assert (arg_types_assert, call) 
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
	let upd = make_upd ~threats lab s.jc_statement_loc 
	  fi e1 (Var tmp2) 
	in
(* Yannick: ignore variables to be able to refine update function used. *)	
(* 	let upd = make_upd ~threats fi (Var tmp1) (Var tmp2) in *)
(* Claude: do not ignore variable tmp2, since it may involve a coercion. 
   Anyway, safety of the update do not depend on e2 *)
	let upd = if threats && !Jc_options.inv_sem = InvOwnership then
	  append (assert_mutable (LVar tmp1) fi) upd else upd in
	let lets =
	  (make_lets
	     ([ (tmp1, e1') ; (tmp2, coerce ~no_int_overflow:(not threats) 
				 e2.jc_expr_label e2.jc_expr_loc 
				 fi.jc_field_info_type 
				 e2.jc_expr_type e2') ])
	     upd)
	in
	if !Jc_options.inv_sem = InvOwnership then
	  append lets (assume_field_invariants fi)
	else
	  lets
(*	if !Jc_options.inv_sem = Jc_options.InvOwnership then   (make_assume_field_assocs (fresh_program_point ()) fi)) *)
    | JCSblock l -> statement_list ~threats l
    | JCSif (e, s1, s2) -> 
	let e = expr e in
	If(e, statement s1, statement s2)
    | JCSloop (la, s) ->
	let inv = named_assertion None "init" la.jc_loop_invariant in
	begin 
	  match la.jc_loop_variant with
	    | Some t when threats ->
		let variant = named_term None "" t in
		While(Cte(Prim_bool true), inv,
	              Some (term_coerce t.jc_term_loc integer_type 
			    t.jc_term_type variant,None), [statement s])
	    | _ ->
		While(Cte(Prim_bool true), inv,
	              None, [statement s])
	end
    | JCSassert((*None,*) a) -> 
	Assert(named_assertion None "init" a, Void)
(*
    | JCSassert(Some name, a) -> 
	
	Assert(LNamed(reg_loc ~name a.jc_assertion_loc,
		      assertion None "init" a), Void)
*)
    | JCSdecl(vi,e,s) -> 
	begin
	  let e' = match e with
	    | None -> 
		any_value vi.jc_var_info_type
	    | Some e -> 
(*
		eprintf "decl of vi=%s@." vi.jc_var_info_name;
*)
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
	  (Raise (jessie_return_exception, None))
    | JCSunpack(st, e, as_t) ->
	let e = expr e in 
	make_guarded_app ~name:lab Unpack s.jc_statement_loc
	  ("unpack_"^st.jc_struct_info_root) [e; Var (tag_name as_t)]
    | JCSpack(st, e, from_t) ->
	let e = expr e in 
	make_guarded_app ~name:lab Pack s.jc_statement_loc
	  ("pack_"^st.jc_struct_info_root) [e; Var (tag_name from_t)]
    | JCSthrow (ei, Some e) -> 
	let e = expr e in
	Raise(exception_name ei,Some e)
    | JCSthrow (ei, None) -> 
	Raise(exception_name ei,None)
    | JCStry (s, catches, finally) -> 
	assert (finally.jc_statement_node = JCSblock []); (* TODO *)
	let catch (s,excs) (ei,v_opt,st) =
	  if ExceptionSet.mem ei excs then
	    (Try(s, 
		 exception_name ei, 
		 Option_misc.map (fun v -> v.jc_var_info_final_name) v_opt,
		 statement st),
	     ExceptionSet.remove ei excs)
	  else
	    begin
	      eprintf "Warning: exception %s cannot be thrown@."
		ei.jc_exception_info_name;
	      (s,excs)
	    end
	in
	let ef = Jc_effect.statement empty_fun_effect s in
	let (s,_) =
	  List.fold_left catch (statement s,ef.jc_raises) catches
	in s

and statement_list ~threats l = 
  List.fold_right 
    (fun s acc -> append (statement ~threats s) acc) l Void

(******************
 structures
******************)

let tr_struct st acc =
  let alloc_type = alloc_table_type st in
  let tagid_type = tag_id_type st in
  let ptr_type = pointer_type st in
  let direct_fields = direct_embedded_struct_fields st in
  let all_fields = embedded_struct_fields st in
  let all_structs = 
    List.fold_left (fun acc fi -> StructSet.add (field_sinfo fi) acc) 
      StructSet.empty all_fields
  in
  let all_structs = StructSet.fold (fun st acc -> st :: acc) all_structs [] in
  let alloc = alloc_table_name st in
  let tagtab = tag_table_name st in
    (* Declarations of field memories. *)
  let acc =
    if Jc_options.separation then acc else
      List.fold_left
	(fun acc fi ->
	  let mem = memory_field fi in
	  Param(
	    false,
	    field_memory_name fi,
	    Ref_type(Base_type mem))::acc)
	acc st.jc_struct_info_fields
  in
  (* declaration of the tag_id *)
  let acc =
    Logic(false,tag_name st,[],tagid_type)::acc
  in

  (* One element validity predicate. *)
  (* [offset_min(alloc,x) == 0 and offset_max(alloc,x) == 0] *)
  let top_validity =
    LAnd(
      LPred("eq_int",[
	LApp("offset_min",[LVar alloc;LVar "x"]);LConst(Prim_int "0")]),
      LPred("eq_int",[
        LApp("offset_max",[LVar alloc;LVar "x"]);LConst(Prim_int "0")]))
  in
  let field_validity_list =
    List.map (fun fi ->
      let st = field_sinfo fi in
      let a,b = field_bounds fi in
      let alloc = alloc_table_name st in
      let fields = embedded_struct_fields st in
      let structs = 
	List.fold_left (fun acc fi -> StructSet.add (field_sinfo fi) acc) 
	  StructSet.empty fields
      in
      let structs = StructSet.fold (fun st acc -> st :: acc) structs [] in
      (* [valid_st(select(fi,x),a,b,alloc...)] *)
      LPred(
	valid_pred_name st,
	LApp("select",[LVar(field_memory_name fi);LVar "x"])
	:: LConst(Prim_int(Num.string_of_num a))
	:: LConst(Prim_int(Num.string_of_num b))
	:: LVar alloc
	:: List.map (lvar None ** alloc_table_name) structs
	@ List.map (lvar None ** field_memory_name) fields)
    ) direct_fields
  in
  let field_validity = make_and_list field_validity_list in
  let validity = LAnd(top_validity,field_validity) in
  let params = 
    ("x",ptr_type)
    :: (alloc,alloc_type)
    :: List.map struct_alloc_arg all_structs
    @ List.map field_memory_arg all_fields
  in
  let acc = 
    Predicate(false,valid_one_pred_name st,params,validity) :: acc
  in

  (* Validity predicate. *)
  (* [offset_min(alloc,x) == a and offset_max(alloc,x) == b] *)
  let top_validity =
    LAnd(
      LPred("eq_int",[
	LApp("offset_min",[LVar alloc;LVar "x"]);LVar "a"]),
      LPred("eq_int",[
        LApp("offset_max",[LVar alloc;LVar "x"]);LVar "b"]))
  in
  let field_validity_list =
    List.map (fun fi ->
      let st = field_sinfo fi in
      let a,b = field_bounds fi in
      let alloc = alloc_table_name st in
      let fields = embedded_struct_fields st in
      let structs = 
	List.fold_left (fun acc fi -> StructSet.add (field_sinfo fi) acc) 
	  StructSet.empty fields
      in
      let structs = StructSet.fold (fun st acc -> st :: acc) structs [] in
      (* [valid_st(select(fi,x+i),a,b,alloc...)] *)
      LPred(
	valid_pred_name st,
	LApp("select",[
	  LVar(field_memory_name fi);LApp("shift",[LVar "x";LVar "i"])])
	:: LConst(Prim_int(Num.string_of_num a))
	:: LConst(Prim_int(Num.string_of_num b))
	:: LVar alloc
	:: List.map (lvar None ** alloc_table_name) structs
	@ List.map (lvar None ** field_memory_name) fields)
    ) direct_fields
  in
  let field_validity = make_and_list field_validity_list in
  (* [forall int i. i >= a and i <= b 
   *                  -> valid_st1(...) and valid_st2(...) and ...] 
   *)
  let field_validity =
    LForall(
      "i",why_integer_type,
      LImpl(
	LAnd(
	  LPred("ge_int",[LVar "i";LVar "a"]),
	  LPred("le_int",[LVar "i";LVar "b"])),
	field_validity))
  in
  let validity = LAnd(top_validity,field_validity) in
  let params = 
    ("x",ptr_type)
    :: ("a",why_integer_type)
    :: ("b",why_integer_type)
    :: (alloc,alloc_type)
    :: List.map struct_alloc_arg all_structs
    @ List.map field_memory_arg all_fields
  in
  let acc = 
    Predicate(false,valid_pred_name st,params,validity) :: acc
  in

  (* Allocation of one element parameter. *)
  let alloc_type = 
    Annot_type(
      (* no pre *)
      LTrue,
      (* [st_root pointer] *)
      Base_type ptr_type,
      (* [reads all_fields writes alloc,tagtab] *)
      (List.map (fun si -> alloc_table_name si) all_structs
	@ List.map (fun fi -> fi.jc_field_info_final_name) all_fields),[alloc;tagtab],
      (* normal post *)
      make_and_list [
	(* [valid_one_st(result,alloc...)] *)
	LPred(
	  valid_one_pred_name st,
	  LVar "result"
	  :: LVar alloc
	  :: List.map (lvar None ** alloc_table_name) all_structs
	  @ List.map (lvar None ** field_memory_name) all_fields);
	(* [instanceof(tagtab,result,tag_st)] *)
	LPred("instanceof",[LVar tagtab;LVar "result";LVar(tag_name st)]);
	(* [alloc_extends(old(alloc),alloc)] *)
	LPred("alloc_extends",[LVarAtLabel(alloc,"");LVar alloc]);
	(* [alloc_extern(old(alloc),result)] *)
	LPred("alloc_extern",[LVarAtLabel(alloc,"");LVar "result"])
      ],
      (* no exceptional post *)
      [])
  in
  let alloc_type =
    List.fold_left (fun acc fi ->
      Prod_type(field_memory_name fi,Ref_type(Base_type(memory_field fi)),acc)
    ) alloc_type all_fields
  in
  let alloc_type = Prod_type("tt",unit_type,alloc_type) in
  let acc = 
    Param(false,alloc_one_param_name st,alloc_type) :: acc
  in

  (* Allocation parameter. *)
  let alloc_type = 
    Annot_type(
      (* [n >= 0] *)
      LPred("gt_int",[LVar "n";LConst(Prim_int "0")]),
      (* [st_root pointer] *)
      Base_type ptr_type,
      (* [reads all_fields; writes alloc,tagtab] *)
      (List.map (fun si -> alloc_table_name si) all_structs
	@ List.map (fun fi -> fi.jc_field_info_final_name) all_fields), [alloc; tagtab],
      (* normal post *)
      make_and_list [
	(* [valid_st(result,0,n-1,alloc...)] *)
	LPred(
	  valid_pred_name st,
	  LVar "result"
	  :: LConst(Prim_int "0")
	  :: LApp("sub_int",[LVar "n";LConst(Prim_int "1")])
	  :: LVar alloc
	  :: List.map (lvar None ** alloc_table_name) all_structs
	  @ List.map (lvar None ** field_memory_name) all_fields);
	(* [instanceof(tagtab,result,tag_st)] *)
	LPred("instanceof",[LVar tagtab;LVar "result";LVar(tag_name st)]);
	(* [alloc_extends(old(alloc),alloc)] *)
	LPred("alloc_extends",[LVarAtLabel(alloc,"");LVar alloc]);
	(* [alloc_extern(old(alloc),result)] *)
	LPred("alloc_extern",[LVarAtLabel(alloc,"");LVar "result"])
      ],
      (* no exceptional post *)
      [])
  in
  let alloc_type =
    List.fold_left (fun acc fi ->
      Prod_type(field_memory_name fi,Ref_type(Base_type(memory_field fi)),acc)
    ) alloc_type all_fields
  in
  let alloc_type = Prod_type("n",Base_type why_integer_type,alloc_type) in
  let acc = 
    Param(false,alloc_param_name st,alloc_type) :: acc
  in
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
    | JCLSderef(ls,fi,r) ->
	let m = lvar (Some before) (field_region_memory_name(fi,r)) in
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
    | JCLderef(e,fi,fr) -> 
	let iloc = pset before e in
	let l =
	  try
	    let l = FieldRegionMap.find (fi,location_set_region e) mems in
	    iloc::l
	  with Not_found -> [iloc]
	in
	(refs, FieldRegionMap.add (fi,location_set_region e) l mems)
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
    FieldRegionSet.fold
      (fun (fi,r) m -> 
	 FieldRegionMap.add (fi,r) [] m)
      ef.jc_writes.jc_effect_memories FieldRegionMap.empty 
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
  FieldRegionMap.fold
    (fun (fi,r) p acc -> 
       let v = field_region_memory_name(fi,r) in
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
       match eopt with 
	 | Some ei -> acc
	 | None -> (exception_name ei, LTrue)::acc)
    excep_posts []
    
let interp_fun_params f memories annot_type =
  let annot_type = 
    if not Jc_options.separation then annot_type else
      List.fold_left (fun acc (name,ty) ->
	Prod_type(name,Ref_type(Base_type ty),acc)
      ) annot_type memories
  in
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
       
  
let tr_fun f loc spec body acc =
  let requires = spec.jc_fun_requires in
  let requires = 
    List.fold_right
      (fun v acc ->
	 match v.jc_var_info_type with
	   | JCTpointer(st,a,b) ->
	       let alloc = alloc_table_name st in
	       let var = LVar v.jc_var_info_final_name in
	       let fields = embedded_struct_fields st in
	       let fields = List.map (fun fi -> 
		 (fi,Region.make_field v.jc_var_info_region fi)) fields 
	       in
	       f.jc_fun_info_effects <-
		 Jc_effect.fef_union 
		 f.jc_fun_info_effects
		 (List.fold_left Jc_effect.add_field_reads f.jc_fun_info_effects fields);
	       let validity = match a,b with
		 | Some a, Some b 
		     when Num.eq_num a (Num.num_of_int 0)
		       && Num.eq_num b (Num.num_of_int 0) ->
		     let structs = 
		       List.fold_left 
			 (fun acc (fi,_) -> StructSet.add (field_sinfo fi) acc) 
			 StructSet.empty fields
		     in
		     let structs = 
		       StructSet.fold (fun st acc -> st :: acc) structs [] in
		     LPred(
		       valid_one_pred_name st,
		       var
		       :: LVar alloc
		       :: List.map (lvar None ** alloc_table_name) structs
		       @ List.map (lvar None ** field_region_memory_name) fields)
		 | Some a,Some b ->
		     let structs = 
		       List.fold_left 
			 (fun acc (fi,_) -> StructSet.add (field_sinfo fi) acc) 
			 StructSet.empty fields
		     in
		     let structs = 
		       StructSet.fold (fun st acc -> st :: acc) structs [] in
		     LPred(
		       valid_pred_name st,
		       var
		       :: LConst(Prim_int(Num.string_of_num a))
		       :: LConst(Prim_int(Num.string_of_num b))
		       :: LVar alloc
		       :: List.map (lvar None ** alloc_table_name) structs
		       @ List.map (lvar None ** field_region_memory_name) fields)
		 | _ -> LTrue
	       in
		 make_and validity acc
           | JCTnull -> assert false
	   | JCTenum _ -> acc
	   | JCTnative _ -> acc
	   | JCTlogic _ -> acc)
      f.jc_fun_info_parameters
      (named_assertion None "" requires)
  in

  (* partition behaviors as follows:
     - behaviors inferred by analysis (postfixed by 'safety': they will be added to fun safety)
     - user defined behaviors 
     TODO ?: also add inferred behaviors to other funs ? *)
  let (normal_behaviors_safety, normal_behaviors, excep_behaviors_safety, excep_behaviors) =
    List.fold_left
      (fun (normal_safety, normal, excep_safety, excep) (loc, id, b) ->
	 let post =
	   match b.jc_behavior_assigns with
	     | None ->
		 (named_assertion None "" b.jc_behavior_ensures)		
	     | Some(locassigns,a) ->
		 named_jc_assertion loc
		   (make_and
		      (named_assertion None "" b.jc_behavior_ensures)		
		      (named_jc_assertion
			 locassigns
			 (assigns "" f.jc_fun_info_effects (Some a))))
	 in
	 let a =
	   match b.jc_behavior_assumes with
	     | None -> post
	     | Some e -> 
		 make_impl (assertion (Some "") "" e) post
	 in
	 match b.jc_behavior_throws with
	   | None -> 
	       if id = "safety" then 
		 ((id, b, a) :: normal_safety, normal, excep_safety, excep)
	       else 
		 (normal_safety, (id, b, a) :: normal, excep_safety, excep)
	   | Some ei ->
	       let eb =
		 try
		   ExceptionMap.find ei excep
		 with Not_found -> []
	       in
	       if id = "safety" then 
		 (normal_safety, normal, 
		  ExceptionMap.add ei ((id, b, a) :: eb) excep_safety, excep)
	       else
		 (normal_safety, normal, excep_safety, 
		  ExceptionMap.add ei ((id, b, a) :: eb) excep))
      ([], [], ExceptionMap.empty, ExceptionMap.empty)
      spec.jc_fun_behavior
  in
  let excep_behaviors = 
    ExceptionSet.fold
      (fun ei acc -> 
	 if ExceptionMap.mem ei acc then acc else
	   let b = 
	     { default_behavior with 
		 jc_behavior_throws = Some ei; jc_behavior_ensures = (raw_asrt JCAtrue); } 
	   in
	   ExceptionMap.add ei [ei.jc_exception_info_name ^ "_b", b, LTrue] acc)
      f.jc_fun_info_effects.jc_raises
      excep_behaviors
  in
  let reads =
    FieldRegionSet.fold
      (fun (f,r) acc -> (field_region_memory_name(f,r))::acc)
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
    FieldRegionSet.fold
      (fun (f,r) acc -> (field_region_memory_name(f,r))::acc)
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
  let memories =
    FieldRegionSet.fold
      (fun (fi,r) acc ->
	if r.jc_reg_variable then
	  (field_region_memory_name(fi,r),memory_field fi)::acc 
	else acc)
      (FieldRegionSet.union
	f.jc_fun_info_effects.jc_reads.jc_effect_memories 
	f.jc_fun_info_effects.jc_writes.jc_effect_memories)
      []
  in
  let normal_post =
    List.fold_right
      (fun (_,_,e) acc -> make_and e acc)
      normal_behaviors LTrue
  in
  let normal_post_safety =
    List.fold_right
      (fun (_,_,e) acc -> make_and e acc)
      normal_behaviors_safety LTrue
  in
  let excep_posts =
    ExceptionMap.fold
      (fun ei l acc ->
	 let p = 
	   List.fold_right (fun (_,_,e) acc -> make_and e acc) l LTrue
	 in (exception_name ei,p)::acc) 
      excep_behaviors []
  in
  let excep_posts_safety =
    ExceptionMap.fold
      (fun ei l acc ->
	 let p = 
	   List.fold_right (fun (_,_,e) acc -> make_and e acc) l LTrue
	 in (exception_name ei,p)::acc) 
      excep_behaviors_safety []
  in
  (* DEBUG *)
  (* Jc_options.lprintf "DEBUG: tr_fun 2@."; *)
  (* why parameter for calling the function *)
  let ret_type = tr_type f.jc_fun_info_return_type in
  let param_normal_post = 
    if is_purely_exceptional_fun spec then LFalse else
      make_and normal_post normal_post_safety 
  in
  let param_excep_posts = excep_posts @ excep_posts_safety in
  let why_param = 
    let annot_type =
      Annot_type(requires, ret_type,
		 reads,writes, param_normal_post, param_excep_posts)
    in
    let fun_type = interp_fun_params f memories annot_type in
      Param (false, f.jc_fun_info_final_name, fun_type)
  in
  match body with
    | None -> 
	(* function was only declared *)
	why_param :: acc
    | Some body ->
	if Jc_options.verify <> [] && 
	  not (List.mem f.Jc_fenv.jc_fun_info_name Jc_options.verify) 
	then 
	  why_param :: acc 
	else
	  (* why functions for each behaviors *)
	    let mem_params = 
	      List.map (fun (name,ty) -> name,Ref_type(Base_type ty)) memories
	    in
	    let params = match f.jc_fun_info_parameters with
	      | [] -> ["tt", unit_type]
	      | l -> List.map parameter l
	    in
	    let params = params @ mem_params in
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
	      printf "Generating Why function %s@."
		f.Jc_fenv.jc_fun_info_final_name;
	      (* default behavior *)
	      let body_safety = statement_list ~threats:true body in
	      let tblock =
		if !Jc_options.inv_sem = InvOwnership then
		  append
		    (* (make_assume_all_assocs (fresh_program_point ()) 
		       f.jc_fun_info_parameters)*)
		    (assume_all_invariants f.jc_fun_info_parameters)
		    body_safety
		else
		  body_safety
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
	      let tblock_safety =
		List.fold_right
		  (fun (mut_id,id) bl ->
		     Let_ref(mut_id,Var(id),bl)) list_of_refs tblock 
	      in
	      let safety_b, user_b = 
		List.partition
		  (fun (_,s, _) -> s = "safety")
		  spec.jc_fun_behavior
	      in
		spec.jc_fun_behavior <- user_b;
	      let safety_exists = safety_b <> [] in
	      let newid = f.jc_fun_info_name ^ "_safety" in
	      let _ = reg_loc 
		~id:newid
		~oldid:f.jc_fun_info_name
		~name:("function " ^ f.jc_fun_info_name)
		~beh:"Safety" loc 
	      in
	      let acc = 
		if is_purely_exceptional_fun spec then acc else
		if safety_exists then 
		  Def(
		    newid,
		    Fun(
		      params,
		      requires,
		      tblock_safety,
		      normal_post_safety,
		      excep_posts_safety @ excep_posts_for_others None excep_behaviors 
		    ))::acc 
		else
		  Def(
		    newid,
		    Fun(
		      params,
		      requires,
		      tblock_safety,
		      LTrue,
		      excep_posts_for_others None excep_behaviors
		    ))::acc
	      in
		(* user behaviors *)
	      let acc = 
		if spec.jc_fun_behavior = [] then
		  acc
		else
		  let body = statement_list ~threats:false body in
		  let tblock =
		    if !Jc_options.inv_sem = InvOwnership then
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
			 let newid = f.jc_fun_info_name ^ "_ensures_" ^ id in
			 let beh = 
			   if id="default" then "Behavior" else
			     "Normal behavior `"^id^"'"
			 in
			 let _ = reg_loc 
			   ~id:newid
			   ~oldid:f.jc_fun_info_name
			   ~name:("function "^f.jc_fun_info_name)
			   ~beh  
			   loc 
			 in
			 let d =
			   Def(
			     newid,
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
			      let newid = 
				f.jc_fun_info_name ^ "_exsures_" ^ id 
			      in
			      let _ = reg_loc 
				~id:newid
				~oldid:f.jc_fun_info_name
				~name:("function "^f.jc_fun_info_name)
				~beh:("Exceptional behavior `"^id^"'")  
				loc in
			      let d =
				Def(newid,
				    Fun(params,
					requires,
					tblock,
					LTrue,
					(exception_name ei,e) :: 
					  excep_posts_for_others (Some ei) excep_behaviors)) in
				d::acc)
			   l acc)
		      excep_behaviors acc
		  in
		    acc 
	in why_param::acc

let tr_logic_type id acc = Type(id,[])::acc

let tr_axiom id p acc = 
  let a = assertion None "" p in
  let ef = Jc_effect.assertion empty_effects p in
  let a =
    FieldRegionSet.fold (fun (fi,r) a -> 
      LForall (field_region_memory_name(fi,r), memory_field fi, a)
    ) ef.jc_effect_memories a 
  in
  (* How to add quantification on other effects (alloc, tag) without knowing 
   * their type ? *)
  Axiom(id,a)::acc

let tr_exception ei acc =
  Jc_options.lprintf "producing exception '%s'@." ei.jc_exception_info_name;
  let typ = match ei.jc_exception_info_type with
    | Some tei -> Some (tr_base_type tei)
    | None -> None
  in
  Exception(exception_name ei, typ) :: acc

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
(*
    Logic(false,logic_enum_of_int ri,
	  [("",why_integer_type)],simple_logic_type n) :: 
*)
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
  compile-command: "unset LANG; make -j -C .. bin/jessie.byte"
  End: 
*)
