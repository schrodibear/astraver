(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
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

(* $Id: jc_interp.ml,v 1.234 2008-02-07 19:22:03 nrousset Exp $ *)

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
open Jc_interp_misc
open Jc_struct_tools
open Jc_pattern

(* locs table *)


type kind =
  | ArithOverflow
  | DownCast
  | IndexBounds
  | PointerDeref
  | AllocSize
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
  try 
    (* If label already refered to in [Output.locs_table], do not reference it
     * more. This is the case for generated annotations. 
     *)
    match id with None -> raise Not_found | Some id ->
      ignore (Hashtbl.find Output.locs_table id);
      id
  with Not_found ->

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
       | AllocSize -> "AllocSize"
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

let why_integer_type = simple_logic_type "int"
  
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
  | Bgt_int -> "gt_int_bool"
  | Blt_int -> "lt_int_bool"
  | Bge_int -> "ge_int_bool"
  | Ble_int -> "le_int_bool"
  | Beq_int -> "eq_int_bool"
  | Bneq_int -> "neq_int_bool"
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
  | JCTpointer _
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
      let e' = LApp(logic_int_of_enum ri,[e]) in
      begin
	match e with
	  | Tnamed(n,_) -> Tnamed(n,e')
	  | _ -> e'
      end
  | JCTenum ri, JCTnative Tinteger ->
      assert false (* a explicit cast should be required by jc_typing *)
      (* LApp(logic_enum_of_int ri,[e]) *)
  | JCTpointer (JCvariant _, _, _), JCTpointer _ -> e
  | JCTpointer (st1, _, _), JCTpointer(JCtag st2,_,_) 
      when Jc_typing.substruct st2 st1 -> e
  | JCTpointer (JCtag st, a, b), (JCTpointer(_,_,_) | JCTnull)  -> 
      LApp("downcast", 
	   [ LVar (tag_table_name (JCtag st)) ; e ;
	     LVar (tag_name st) ])	
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
    | JCTpointer (JCvariant _, _, _), JCTpointer _ -> e
    | JCTpointer (st1,_,_), JCTpointer (JCtag st2,_,_) 
	when Jc_typing.substruct st2 st1 -> e
    | JCTpointer (JCtag st,_,_), _  -> 
	make_guarded_app ~name:lab DownCast loc "downcast_" 
	  [ Deref (tag_table_name (JCtag st)) ; e ;
	    Var (tag_name st) ]	
    | _ -> 
	Jc_typing.typing_error loc 
	  "can't coerce type %a to type %a" 
	  print_type tsrc print_type tdest

(**************************

terms and assertions 

*************************)


let lvar ?(assigned=true) ?(label_in_name=false) label v =
  if label_in_name then
    LVar(label_var label v)
  else
    if assigned then
      match label with 
	| LabelHere -> LVar v
	| LabelOld -> LVarAtLabel(v,"")
	| LabelPre -> LVarAtLabel(v,"init")
	| LabelPost -> LVar v
	| LabelName l -> LVarAtLabel(v,l)
    else LVar v

let var v = Var v

let lvar_info label v = 
  lvar ~assigned:v.jc_var_info_assigned label v.jc_var_info_final_name

(* Return (t, lets) where:
 * t is the Why term
 * lets is a list of (id, value), which should be binded
 * at the assertion level. *)
let rec term ~global_assertion label oldlabel t =
  let ft = term ~global_assertion label oldlabel in
  let t', lets =
  match t.jc_term_node with
    | JCTconst JCCnull -> LVar "null", []
    | JCTvar v -> lvar_info label v, []
    | JCTconst c -> LConst(const c), []
    | JCTunary(op,t1) ->
	let t1', lets = ft t1 in
	LApp (unary_op op, 
	      [term_coerce t.jc_term_loc 
		 (unary_arg_type op) t1.jc_term_type t1' ]), lets
    | JCTbinary(t1,((Beq_pointer | Bneq_pointer) as op),t2) ->
	let t1', lets1 = ft t1 in
	let t2', lets2 = ft t2 in
	LApp (term_bin_op op, [ t1'; t2']), lets1@lets2
    | JCTbinary(t1,Bland,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,Blor,t2) ->
	assert false (* should be an assertion *)
    | JCTbinary(t1,op,t2) ->
	let t1', lets1 = ft t1 in
	let t2', lets2 = ft t2 in
	let t = bin_arg_type t.jc_term_loc op in
	LApp (term_bin_op op, 
	      [ term_coerce t1.jc_term_loc t 
		  t1.jc_term_type t1'; 
		term_coerce t2.jc_term_loc t 
		  t2.jc_term_type t2']), lets1@lets2
    | JCTshift(t1,t2) -> 
	let t1', lets1 = ft t1 in
	let t2', lets2 = ft t2 in
	LApp("shift",[t1'; 
		      term_coerce t2.jc_term_loc integer_type 
			t2.jc_term_type t2']), lets1@lets2
    | JCTsub_pointer(t1,t2) -> 
	let t1', lets1 = ft t1 in
	let t2', lets2 = ft t2 in
	LApp("sub_pointer",[t1'; t2']), lets1@lets2
    | JCTif(t1,t2,t3) -> assert false (* TODO *)
    | JCTderef(t,lab,fi) -> 
	let t', lets = ft t in
	let mem = field_region_memory_name(fi,t.jc_term_region) in
	LApp("select",[lvar ~label_in_name:global_assertion lab mem; t']), lets
    | JCTapp app ->
	let f = app.jc_app_fun and l = app.jc_app_args in
	let args, lets = List.fold_right
	  (fun arg (args, lets) ->
	     let arg', arglets = ft arg in
	     arg'::args, arglets@lets)
	  l ([], [])
	in
	make_logic_fun_call ~label_in_name:global_assertion f args
	  app.jc_app_region_assoc app.jc_app_label_assoc, []
    | JCTold(t) -> term ~global_assertion oldlabel oldlabel t
    | JCTat(t,lab) -> term ~global_assertion lab oldlabel t
    | JCToffset(k,t,st) -> 
	let alloc = 
	  alloc_region_table_name (JCtag st, t.jc_term_region)
	in
	let f = match k with
	  | Offset_min -> "offset_min"
	  | Offset_max -> "offset_max"
	in
	let t', lets = ft t in
	LApp(f,[LVar alloc; t']), lets
    | JCTinstanceof(t,label,ty) ->
	let t', lets = ft t in
	let tag = tag_table_name (JCtag ty) in
	LApp("instanceof_bool",
	     [lvar label tag; t';LVar (tag_name ty)]), lets
    | JCTcast(t,label,ty) ->
	let t', lets = ft t in
	let tag = tag_table_name (JCtag ty) in
	LApp("downcast",
	     [lvar label tag; t';LVar (tag_name ty)]), lets
    | JCTrange(t1,t2) -> assert false (* TODO ? *)
    | JCTmatch(t, ptl) ->
	let t', lets1 = ft t in
	(* TODO: use a temporary variable for t' *)
	(* if the pattern-matching is incomplete, default value is true *)
	let ptl', lets2 =
	  pattern_list_term ft t' t.jc_term_type ptl (LConst(Prim_bool true)) in
	ptl', lets1@lets2
  in
  (if t.jc_term_label <> "" then
     Tnamed(reg_loc ~id:t.jc_term_label t.jc_term_loc,t')
   else
     t'), lets

let named_term ~global_assertion label oldlabel t =
  let t', lets = term ~global_assertion label oldlabel t in
  match t' with
    | Tnamed _ -> t', lets
    | _ -> 
	let n = reg_loc t.jc_term_loc in
	Tnamed(n,t'), lets

let tag ~global_assertion label oldlabel = function
  | JCTtag st -> LVar (tag_name st), []
  | JCTbottom -> LVar "bottom_tag", []
  | JCTtypeof(t, st) ->
      let te, lets = term ~global_assertion label oldlabel t in
      make_typeof st te, lets

let rec assertion ~global_assertion label oldlabel a =
  let fa = assertion ~global_assertion label oldlabel 
  and ft = term ~global_assertion label oldlabel
  and ftag = tag ~global_assertion label oldlabel
  in
  let a', lets =
    match a.jc_assertion_node with
      | JCAtrue -> LTrue, []
      | JCAfalse -> LFalse, []
      | JCAif(t1,p2,p3) ->
	  let t1', lets = ft t1 in
	  LIf(t1', fa p2, fa p3), lets
      | JCAand l -> make_and_list (List.map fa l), []
      | JCAor l -> make_or_list (List.map fa l), []
      | JCAimplies(a1,a2) -> make_impl (fa a1) (fa a2), []
      | JCAiff(a1,a2) -> make_equiv (fa a1) (fa a2), []
      | JCAnot(a) -> LNot(fa a), []
      | JCArelation(t1,((Beq_pointer | Bneq_pointer) as op),t2) ->
	  let t1', lets1 = ft t1 in
	  let t2', lets2 = ft t2 in
	  LPred (pred_bin_op op, [ t1'; t2']), lets1@lets2
      | JCArelation(t1,op,t2) ->
	  let t1', lets1 = ft t1 in
	  let t2', lets2 = ft t2 in
	  let t = bin_arg_type a.jc_assertion_loc op in
	  LPred(pred_bin_op op, 
		[ term_coerce t1.jc_term_loc t
		    t1.jc_term_type t1'; 
		  term_coerce t2.jc_term_loc t 
		    t2.jc_term_type t2']), lets1@lets2
      | JCAapp app -> 
	  let f = app.jc_app_fun in
	  let l = app.jc_app_args in
	  let args, lets = List.fold_right
	    (fun arg (args, lets) ->
	       let arg', arglets = ft arg in
	       arg'::args, arglets@lets)
	    l ([], [])
	  in
	  let args' = List.map2 (fun x y -> x, y) l args in
	  (* No type verification for full_separated for the moment. *)
	  if f.jc_logic_info_name = "full_separated" then
	    make_logic_pred_call ~label_in_name:false f args [] [], lets
	  else begin try
	    make_logic_pred_call ~label_in_name:global_assertion f  
	      (List.map2 
		 (fun vi (t, t') -> 
		    term_coerce t.jc_term_loc 
		      vi.jc_var_info_type t.jc_term_type t')
		 f.jc_logic_info_parameters args')
	      app.jc_app_region_assoc
	      app.jc_app_label_assoc, lets
	  with Invalid_argument _ -> assert false
	  end
      | JCAquantifier(Forall,v,p) -> 
	LForall(v.jc_var_info_final_name,
		tr_base_type v.jc_var_info_type,
		fa p), []
      | JCAquantifier(Exists,v,p) -> 
	  LExists(v.jc_var_info_final_name,
		  tr_base_type v.jc_var_info_type,
		  fa p), []
      | JCAold a -> assertion ~global_assertion oldlabel oldlabel a, []
      | JCAat(a,lab) -> assertion ~global_assertion lab oldlabel a, []
      | JCAbool_term(t) ->
	  let t', lets = ft t in
	  LPred("eq",[t'; LConst(Prim_bool true)]), lets
      | JCAinstanceof(t,lab,ty) -> 
	  let t', lets = ft t in
	  let tag = tag_table_name (JCtag ty) in
	  LPred("instanceof", [lvar lab tag; t'; LVar (tag_name ty)]), lets
      | JCAmutable(te, st, ta) ->
	  let te', lets1 = ft te in
	  let tag, lets2 = ftag ta.jc_tag_node in
	  let mutable_field = LVar (mutable_name (JCtag st)) in
	  LPred("eq", [ LApp("select", [ mutable_field; te' ]); tag ]),
	  lets1@lets2
      | JCAtagequality(t1, t2, h) ->
	  let t1', lets1 = ftag t1.jc_tag_node in
	  let t2', lets2 = ftag t2.jc_tag_node in
	  LPred("eq", [ t1'; t2' ]), lets1@lets2
(*      | JCAmatch _ -> assert false *)
  in
  let a' = make_pred_binds lets a' in
  if a.jc_assertion_label <> "" then
    begin
(*
      eprintf "Assertion has label %s@." a.jc_assertion_label;
*)
      LNamed(reg_loc ~id:a.jc_assertion_label a.jc_assertion_loc,a')
    end
  else
    begin
      (*
	eprintf "Assertion has no label@.";
      *)
      a'
    end
  

let named_jc_assertion loc a =
  match a with
    | LNamed (lab,_) -> 
(*
	eprintf "Assertion already named %s@." lab;
*)
	a
    | _ -> 
	let n = reg_loc loc in 
(*
	eprintf "Registering new name %s for assertion@." n;
*)
	LNamed(n,a)


let named_assertion ~global_assertion label oldlabel a =
  let a' = assertion ~global_assertion label oldlabel a in
  named_jc_assertion a.jc_assertion_loc a'

let struct_alloc_arg a =
  alloc_table_name a, alloc_table_type a

let field_memory_arg fi =
  field_memory_name fi, field_memory_type fi

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
	let t', lets = term ~global_assertion:true LabelHere LabelHere t in
	let pred =
	  LPred(
	    "eq",
	    [term_coerce Loc.dummy_position integer_type
	       vi.jc_var_info_type (LVar vi.jc_var_info_name); 
	     term_coerce t.jc_term_loc integer_type 
	       t.jc_term_type t']
	  )
	in
	let ax =
	  Axiom(
	    vi.jc_var_info_name ^ "_value_axiom",
	    make_pred_binds lets pred
	  )
	in
	ax::decl

let tr_logic_fun li ta acc =
  let params =
    List.map
      (fun vi ->
	 (vi.jc_var_info_final_name,
	   tr_base_type vi.jc_var_info_type))
      li.jc_logic_info_parameters
  in  
  let params_reads = 
    Jc_interp_misc.logic_params ~label_in_name:true li @ params 
  in
(*
    FieldRegionSet.fold
      (fun (fi,r) acc -> 
	 (field_region_memory_name(fi,r), memory_field fi)::acc)
      li.jc_logic_info_effects.jc_effect_memories
      params
  in
  let params_reads =
    StringRegionSet.fold
      (fun (a,r) acc -> 
	 (alloc_region_table_name(a,r),alloc_table_type a)::acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      params_reads
  in
  let params_reads =
    StringSet.fold
      (fun v acc ->
	 let st, _ = Hashtbl.find Jc_typing.structs_table v in
	 let t = { logic_type_args = [struct_model_type st];
		   logic_type_name = tag_table_type_name }
	 in
	 (tag_table_name st, t)::acc)
      li.jc_logic_info_effects.jc_effect_tag_table
      params_reads
  in
*)
  let decl =
    match li.jc_logic_info_result_type, ta with
	(* Predicate *)
      | None, JCAssertion a -> 
	  let a = assertion ~global_assertion:true LabelHere LabelHere a in
	    Predicate (false, li.jc_logic_info_final_name,params_reads, a) 
	      (* Function *)
      | Some ty, JCTerm t -> 
	  let ret = tr_base_type ty in
	  let t, lets = term ~global_assertion:true LabelHere LabelHere t in
	  assert (lets = []);
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
    FieldRegionMap.fold (fun (fi,r) labels acc ->
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
		LPred("eq",[
		  LApp(li.jc_logic_info_final_name,normal_params);
		  LApp(li.jc_logic_info_final_name,update_params)]))
      in
      let a = 
	List.fold_left (fun a (name,ty) -> LForall(name,ty,a)) a params_reads
      in
      let a = 
	LForall(
	  "tmp",pointer_type (JCtag fi.jc_field_info_struct),
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

let rec make_upd lab loc ~infunction ~threats fi e1 v =
  let expr = expr ~infunction ~threats and offset = offset ~infunction ~threats in
  let mem = Var(field_region_memory_name(fi,e1.jc_expr_region)) in
  let alloc = 
    alloc_region_table_name (JCtag fi.jc_field_info_root, e1.jc_expr_region)
  in
  let alloc = 
    if Region.polymorphic e1.jc_expr_region then
      if StringRegionSet.mem (field_root_name fi, e1.jc_expr_region)
	infunction.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
      then Deref alloc
      else Var alloc
    else Deref alloc
  in
  if threats then
    match destruct_pointer e1 with
    | _,Int_offset s,Some lb,Some rb when bounded lb rb s ->
	make_app "safe_upd_" 
	  [ mem ; expr e1; v ]
    | p,(Int_offset s as off),Some lb,Some rb when lbounded lb s ->
	make_guarded_app ~name:lab IndexBounds loc "lsafe_bound_upd_" 
	  [ mem ; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,(Int_offset s as off),Some lb,Some rb when rbounded rb s ->
	make_guarded_app ~name:lab IndexBounds loc "rsafe_bound_upd_" 
	  [ mem ; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num lb)); v ]
    | p,off,Some lb,Some rb ->
	make_guarded_app ~name:lab IndexBounds loc "bound_upd_" 
	  [ mem ; expr p; offset off; 
	    Cte (Prim_int (Num.string_of_num lb)); 
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,(Int_offset s as off),Some lb,None when lbounded lb s ->
	make_guarded_app ~name:lab IndexBounds loc "lsafe_lbound_upd_" 
	  [ alloc; mem; expr p; offset off; v ]
    | p,off,Some lb,None ->
	make_guarded_app ~name:lab IndexBounds loc "lbound_upd_" 
	  [ alloc; mem; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num lb)); v ]
    | p,(Int_offset s as off),None,Some rb when rbounded rb s ->
	make_guarded_app ~name:lab IndexBounds loc "rsafe_rbound_upd_" 
	  [ alloc; mem; expr p; offset off; v ]
    | p,off,None,Some rb ->
	make_guarded_app ~name:lab IndexBounds loc "rbound_upd_" 
	  [ alloc; mem; expr p; offset off;
	    Cte (Prim_int (Num.string_of_num rb)); v ]
    | p,Int_offset s,None,None when int_of_string s = 0 ->
	make_guarded_app ~name:lab PointerDeref loc "upd_" 
	  [ alloc; mem ; expr p; v ]
    | p,off,None,None ->
	make_guarded_app ~name:lab PointerDeref loc "offset_upd_" 
	  [ alloc; mem ; expr p; offset off; v ]
  else
    make_app "safe_upd_"
      [ mem ; expr e1 ; v ]
    
and offset ~infunction ~threats = function
  | Int_offset s -> Cte (Prim_int s)
  | Expr_offset e -> 
      coerce ~no_int_overflow:(not threats) 
	e.jc_expr_label e.jc_expr_loc integer_type e.jc_expr_type 
	(expr ~infunction ~threats e)

and expr ~infunction ~threats e : expr =
  let expr = expr ~infunction ~threats and offset = offset ~infunction ~threats in
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
	  alloc_region_table_name (JCtag st, e.jc_expr_region) in
	let alloc = 
	  if Region.polymorphic e.jc_expr_region then
	    if StringRegionSet.mem (root_name st, e.jc_expr_region)
	      infunction.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
	    then Deref alloc
	    else Var alloc
	  else Deref alloc
	in
	let f = match k with
	  | Offset_min -> "offset_min"
	  | Offset_max -> "offset_max"
	in
	make_app f [alloc; expr e] 
    | JCEinstanceof(e,t) ->
	let e = expr e in
	let tag = tag_table_name (JCtag t) in
	(* always safe *)
	make_app "instanceof_" [Deref tag; e; Var (tag_name t)]
    | JCEcast (e, si) ->
	let tag = tag_table_name (JCtag si) in
	(* ??? TODO faire ca correctement: on peut tres bien caster des expressions qui ne sont pas des termes !!! *)
	let et, _ = term ~global_assertion:false LabelHere LabelHere (term_of_expr e) in
	let typea = 
	  match e.jc_expr_type with
	    | JCTpointer (JCtag si', _, _) -> 
		if is_substruct si' si then LTrue else
		  LPred ("instanceof", [LVar tag; et; LVar (tag_name si)])
	    | JCTpointer (JCvariant _, _, _) -> assert false (* TODO *)
	    | _ -> LTrue
	in
	let e = expr e in
	let tag = tag_table_name (JCtag si) in
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
	let mem = 
	  if Region.polymorphic e.jc_expr_region then
	    if FieldRegionMap.mem (fi,e.jc_expr_region)
	      infunction.jc_fun_info_effects.jc_writes.jc_effect_memories
	    then Deref mem
	    else Var mem
	  else Deref mem
	in
	let alloc = 
	  alloc_region_table_name (JCtag fi.jc_field_info_root,
				   e.jc_expr_region)
	in
	let alloc = 
	  if Region.polymorphic e.jc_expr_region then
	    if StringRegionSet.mem (field_root_name fi, e.jc_expr_region)
	      infunction.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
	    then Deref alloc
	    else Var alloc
	  else Deref alloc
	in
	if threats then
	  match destruct_pointer e with
	  | _,Int_offset s,Some lb,Some rb when bounded lb rb s ->
	      make_app "safe_acc_" 
		[ mem ; expr e ]
	  | p,(Int_offset s as off),Some lb,Some rb when lbounded lb s ->
	      make_guarded_app ~name:lab IndexBounds loc "lsafe_bound_acc_" 
		[ mem ; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,(Int_offset s as off),Some lb,Some rb when rbounded rb s ->
	      make_guarded_app ~name:lab IndexBounds loc "rsafe_bound_acc_" 
		[ mem ; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num lb)) ]
	  | p,off,Some lb,Some rb ->
	      make_guarded_app ~name:lab IndexBounds loc "bound_acc_" 
		[ mem ; expr p; offset off; 
		  Cte (Prim_int (Num.string_of_num lb)); 
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,(Int_offset s as off),Some lb,None when lbounded lb s ->
	      make_guarded_app ~name:lab IndexBounds loc "lsafe_lbound_acc_" 
		[ alloc; mem; expr p; offset off ]
	  | p,off,Some lb,None ->
	      make_guarded_app ~name:lab IndexBounds loc "lbound_acc_" 
		[ alloc; mem; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num lb)) ]
	  | p,(Int_offset s as off),None,Some rb when rbounded rb s ->
	      make_guarded_app ~name:lab IndexBounds loc "rsafe_rbound_acc_" 
		[ alloc; mem; expr p; offset off ]
	  | p,off,None,Some rb ->
	      make_guarded_app ~name:lab IndexBounds loc "rbound_acc_" 
		[ alloc; mem; expr p; offset off;
		  Cte (Prim_int (Num.string_of_num rb)) ]
	  | p,Int_offset s,None,None when int_of_string s = 0 ->
	      make_guarded_app ~name:lab PointerDeref loc "acc_" 
		[ alloc; mem ; expr p ]
	  | p,off,None,None ->
	      make_guarded_app ~name:lab PointerDeref loc "offset_acc_" 
		[ alloc; mem ; expr p; offset off ]
	else
	  make_app "safe_acc_"
	    [ mem ; 
	      (* coerce e.jc_expr_loc integer_type e.jc_expr_type *) (expr e) ]
    | JCEalloc (siz, st) ->
	let alloc = alloc_region_table_name (JCtag st, e.jc_expr_region) in
	let tag = tag_table_name (JCtag st) in
(*	
	let fields = embedded_struct_fields st in
	let fields = List.map (fun fi -> (fi,e.jc_expr_region)) fields in
	let roots = embedded_struct_roots st in
	let roots = List.map find_tag_or_variant roots in
	let roots = List.map (fun a -> (a, e.jc_expr_region)) roots in
*)
	let fields = all_memories ~select:fully_allocated (JCtag st) in
	let fields = List.map (fun fi -> (fi, e.jc_expr_region)) fields in
	let roots = all_types ~select:fully_allocated (JCtag st) in
	let roots = List.map (fun a -> (JCvariant a, e.jc_expr_region)) roots in
	begin
	  match !Jc_options.inv_sem with
	    | InvOwnership ->
		let mut = mutable_name (JCtag st) in
		let com = committed_name (JCtag st) in
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
			([Void; Var alloc]
			@ (List.map (var ** alloc_region_table_name) roots)
			@ (List.map (var ** field_region_memory_name) fields))
		  | _ ->
		      make_guarded_app 
			~name:lab AllocSize loc
			(alloc_param_name st)
			([coerce ~no_int_overflow:(not threats) 
			  siz.jc_expr_label siz.jc_expr_loc integer_type 
			  siz.jc_expr_type (expr siz); Var alloc]
			@ (List.map (var ** alloc_region_table_name) roots)
			@ (List.map (var ** field_region_memory_name) fields))

		end
	end
    | JCEfree e ->
	let st = match e.jc_expr_type with
	  | JCTpointer(JCtag st, _, _) -> st
	  | JCTpointer(JCvariant vi, _, _) -> assert false (* TODO *)
	  | _ -> assert false
	in	
	let alloc = 
	  alloc_region_table_name (JCtag st, e.jc_expr_region) in
	if !Jc_options.inv_sem = InvOwnership then
	  let com = committed_name (JCtag st) in
	  make_app "free_parameter_ownership" [Var alloc; Var com; expr e]
	else
	  make_app "free_parameter" [Var alloc; expr e]
(*    | JCEmatch _ -> assert false *)
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

let return_void = ref false

let type_assert vi e =
  match vi.jc_var_info_type, e.jc_expr_type with
    | JCTpointer (si, n1o, n2o), JCTpointer (si', n1o', n2o') ->
	let et, lets =
	  term ~global_assertion:false LabelHere LabelHere (term_of_expr e) in
	let alloc = alloc_table_name si in
	  begin
	    match n1o, n2o with
	      | None, None -> LTrue
	      | Some n, None -> 
		  begin match n1o' with
		    | Some n' when Num.le_num n' n -> LTrue
		    | _ -> 
			let pred =
			  LPred ("le_int",
				 [LApp ("offset_min", [LVar alloc; et]);
				  LConst (Prim_int (Num.string_of_num n))])
			in
			make_pred_binds lets pred
		  end
	      | None, Some n -> 
		  begin match n2o' with
		    | Some n' when Num.le_num n n' -> LTrue
		    | _ -> 
			let pred =
			  LPred ("ge_int",
				 [LApp ("offset_max", [LVar alloc; et]);
				  LConst (Prim_int (Num.string_of_num n))])
			in
			make_pred_binds lets pred
		  end
	      | Some n1, Some n2 
		  when Num.eq_num n1 (Num.num_of_int 0)
		    && Num.eq_num n2 (Num.num_of_int 0) ->
		  begin match n1o', n2o' with
		    | Some n1', Some n2'
			when Num.eq_num n1' (Num.num_of_int 0)
			  && Num.eq_num n2' (Num.num_of_int 0) -> LTrue
		    | Some n1', None when Num.eq_num n1' (Num.num_of_int 0) ->
			let pred =
			  LPred ("eq_int",
				 [LApp ("offset_max", [LVar alloc; et]);
				  LConst (Prim_int "0")])
			in
			make_pred_binds lets pred
		    | None, Some n2' when Num.eq_num n2' (Num.num_of_int 0) ->
			let pred =
			  LPred ("eq_int",
				 [LApp ("offset_min", [LVar alloc; et]);
				  LConst (Prim_int "0")])
			in
			make_pred_binds lets pred
		    | _ -> LTrue
		  end
	      | Some n1, Some n2 -> LTrue
	  end
  | _ -> LTrue
	
let expr_coerce ~infunction ~threats vi e =
  coerce ~no_int_overflow:(not threats)
    e.jc_expr_label e.jc_expr_loc vi.jc_var_info_type 
    e.jc_expr_type (expr ~infunction ~threats e)
    
let rec statement ~infunction ~threats s = 
  (* reset_tmp_var(); *)
  let statement = statement ~infunction ~threats in
  let expr = expr ~infunction ~threats in
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
	    try match f.jc_fun_info_parameters with
	      | [] -> [Void]
	      | params -> List.map2 (expr_coerce ~infunction ~threats) params l 
	    with Invalid_argument _ -> assert false
	  in
	  let write_mems =
	    FieldRegionMap.fold
	      (fun (fi,distr) labels acc ->
		if Region.polymorphic distr then
		  try 
		    let locr = RegionList.assoc distr call.jc_call_region_assoc in
		    (* Check that we do not pass a same memory twice as 
		     * a pointer.
		     *)
		    begin
		      assert(not(FieldRegionList.mem (fi,locr) acc));
	      	      (fi,locr)::acc 
		    end
		  with Not_found -> 
		    (* Local memory. Not passed in argument by the caller. *)
		    acc
		else acc)
	      f.jc_fun_info_effects.jc_writes.jc_effect_memories
	      []
	  in
	  let read_mems =
	    FieldRegionMap.fold
	      (fun (fi,distr) labels acc ->
		 if FieldRegionMap.mem (fi,distr) f.jc_fun_info_effects.jc_writes.jc_effect_memories then acc else
		if Region.polymorphic distr then
		  (* Distant region is polymorphic. It should be passed as
		   * argument to the function. 
		   *)
		  try 
		    let locr = RegionList.assoc distr call.jc_call_region_assoc in
		    if Region.polymorphic locr then
		      if FieldRegionMap.mem (fi,locr) 
			infunction.jc_fun_info_effects.jc_writes.jc_effect_memories
		      then 
			begin
			  (* Check that we do not pass a same memory as 
			   * a pointer and a dereference. 
			   *)
			  assert(not(FieldRegionList.mem (fi,locr) write_mems));
			  (Deref(field_region_memory_name(fi,locr)))::acc 
			end
		      else (Var(field_region_memory_name(fi,locr)))::acc 
		    else
		      begin
			(* Check that we do not pass in argument a constant 
			 * memory that is also read/written directly by 
			 * the function called.
			 *)
			assert(not(FieldRegionMap.mem (fi,locr) f.jc_fun_info_effects.jc_reads.jc_effect_memories
			  ));
			assert(not(FieldRegionMap.mem (fi,locr) f.jc_fun_info_effects.jc_writes.jc_effect_memories
			));
			if FieldRegionMap.mem (fi,locr) 
			  f.jc_fun_info_effects.jc_writes.jc_effect_memories
			then (Var(field_region_memory_name(fi,locr)))::acc 
			else (Deref(field_region_memory_name(fi,locr)))::acc 
		      end
		  with Not_found -> 
		    (* Local memory. Not passed in argument by the caller. *)
		    acc
		else acc)
	      f.jc_fun_info_effects.jc_reads.jc_effect_memories
	      []
	  in
	  let write_mems = 
	    List.map (fun (fi,r) -> Var(field_region_memory_name(fi,r))) 
	      write_mems in
	  let write_allocs =
	    StringRegionSet.fold
	      (fun (a,distr) acc ->
		if Region.polymorphic distr then
		  try 
		    let locr = RegionList.assoc distr call.jc_call_region_assoc in
		    (* Check that we do not pass a same allocation table 
		     * twice as a pointer.
		     *)
		    begin
		      assert(not(StringRegionList.mem (a,locr) acc));
	      	      (a,locr)::acc 
		    end
		  with Not_found -> 
		    (* Local allocation table. 
		     * Not passed in argument by the caller. 
		     *)
		    acc
		else acc)
	      f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
	      []
	  in
	  let read_allocs =
	    StringRegionSet.fold
	      (fun (a,distr) acc ->
		if Region.polymorphic distr then
		  (* Distant region is polymorphic. It should be passed as
		   * argument to the function. 
		   *)
		  try 
		    let locr = RegionList.assoc distr call.jc_call_region_assoc in
		    if Region.polymorphic locr then
		      if StringRegionSet.mem (a,locr) 
			infunction.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
		      then 
			begin
			  (* Check that we do not pass a same allocation table
			   * as a pointer and a dereference. 
			   *)
			  assert(not(StringRegionList.mem (a,locr) write_allocs));
			  (Deref(alloc_region_table_name2(a,locr)))::acc 
			end
		      else (Var(alloc_region_table_name2(a,locr)))::acc 
		    else
		      begin
			(* Check that we do not pass in argument a constant 
			 * allocation table that is also read/written directly
			 * by the function called.
			 *)
			let fallocs = StringRegionSet.union
			  f.jc_fun_info_effects.jc_reads.jc_effect_alloc_table
			  f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
			in
			assert(not(StringRegionSet.mem (a,locr) fallocs));
			if StringRegionSet.mem (a,locr) 
			  f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
			then (Var(alloc_region_table_name2(a,locr)))::acc 
			else (Deref(alloc_region_table_name2(a,locr)))::acc 
		      end
		  with Not_found -> 
		    (* Local allocation table.
		     * Not passed in argument by the caller. *)
		    acc
		else acc)
	      (StringRegionSet.diff
		f.jc_fun_info_effects.jc_reads.jc_effect_alloc_table
		f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table)
	      []
	  in
	  let write_allocs = 
	    List.map (fun (a,r) -> Var(alloc_region_table_name2(a,r))) 
	      write_allocs in
	  let el = el @ write_allocs @ write_mems @ read_allocs @ read_mems in
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
		    begin match f.jc_fun_info_result.jc_var_info_type with
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
	let upd = make_upd ~infunction ~threats lab s.jc_statement_loc 
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
    | JCSblock l -> statement_list ~infunction ~threats l
    | JCSlabel(lab,s) ->
	Label(lab.label_info_name, statement s)
    | JCSif (e, s1, s2) -> 
	let e = expr e in
	If(e, statement s1, statement s2)
    | JCSloop (la, s) ->
	let inv = named_assertion
	  ~global_assertion:false
	  LabelHere
	  LabelPre
	  la.jc_loop_invariant
	in 
	let free_inv = named_assertion 
	  ~global_assertion:false 
	  LabelHere 
	  LabelPre 
	  la.jc_free_loop_invariant 
	in
	let inv = if Jc_options.trust_ai then inv else make_and inv free_inv in
	let body = [statement s] in
	let body = 
	  if Jc_options.trust_ai then
	    BlackBox (Annot_type (LTrue, unit_type, [], [], free_inv, [])) :: body 
	  else body
	in
	  begin 
	    match la.jc_loop_variant with
	      | Some t when threats ->
		  let variant, lets = named_term
		    ~global_assertion:false
		    LabelHere
		    LabelPre
		    t
		  in
		    assert (lets = []);
		    While(Cte(Prim_bool true), inv,
			  Some (term_coerce t.jc_term_loc integer_type 
				  t.jc_term_type variant,None), body)
	      | _ ->
		  While(Cte(Prim_bool true), inv,
			None, body)
	  end
    | JCSassert a -> 
	Assert(named_assertion
		 ~global_assertion:false
		 LabelHere
		 LabelPre
		 a,
	       Void)
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
		  e.jc_expr_label e.jc_expr_loc vi.jc_var_info_type e.jc_expr_type 
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
	  (unpack_name st) [e; Var (tag_name as_t)]
    | JCSpack(st, e, from_t) ->
	let e = expr e in 
	make_guarded_app ~name:lab Pack s.jc_statement_loc
	  (pack_name st) [e; Var (tag_name from_t)]
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
    | JCSmatch (e, psl) ->
	let tmp = tmp_var_name () in
	let body = pattern_list_expr statement (LVar tmp) e.jc_expr_region
	  e.jc_expr_type psl in
	Let(tmp, expr e, body)

and statement_list ~infunction ~threats l = 
  List.fold_right 
    (fun s acc -> append (statement ~infunction ~threats s) acc) l Void

(******************
 structures
******************)

(*
If T is a structure:
   valid_T(p, a, b, allocs ...) =
     if T is root:
       offset_min(alloc_i, p) == a &&
       offset_max(alloc_i, p) == b
     else if S is the direct superclass of T:
       valid_S(p, a, b, allocs ...)
     and for all field (T'[a'..b'] f) of p,
       valid_T'(p.f, a', b', allocs ...)
If T is a variant, then we only have the condition on offset_min and max.
*)
let make_valid_pred tov =
  let p = "p" in
  let a = "a" in
  let b = "b" in
  let params =
    let allocs = List.map
      (fun vi ->
	 let tov = JCvariant vi in
	   alloc_table_name tov,
	 alloc_table_type tov)
      (Jc_struct_tools.all_types ~select:fully_allocated tov)
    in
    let memories = List.map
      (fun fi ->
	 field_memory_name fi,
	 field_memory_type fi)
      (Jc_struct_tools.all_memories ~select:fully_allocated tov)
    in
    let p = p, pointer_type tov in
    let a = a, why_integer_type in
    let b = b, why_integer_type in
      p::a::b::allocs@memories
  in
  let validity =
    let omin, omax, super_valid = match tov with
      | JCtag { jc_struct_info_parent = Some st } ->
	  LTrue,
	  LTrue,
	  make_valid_pred_app (JCtag st) (LVar p) (LVar a) (LVar b)
      | JCtag { jc_struct_info_parent = None }
      | JCvariant _ ->
	  make_eq (make_offset_min tov (LVar p)) (LVar a),
	  make_eq (make_offset_max tov (LVar p)) (LVar b),
	  LTrue
    in
    let fields_valid = match tov with
      | JCtag st ->
	  List.map
	    (function
	       | { jc_field_info_type =
		     JCTpointer(ftov, Some fa, Some fb) } as fi ->
		   make_valid_pred_app ftov
		     (make_select_fi fi (LVar p))
		     (const_of_num fa)
		     (const_of_num fb)
	       | _ ->
		   LTrue)
	    st.jc_struct_info_fields
      | JCvariant _ ->
	  [LTrue]
    in
    make_and_list (omin::omax::super_valid::fields_valid)
  in
  Predicate(false, valid_pred_name tov, params, validity)

let tr_struct st acc =
  let alloc_ty = alloc_table_type (JCtag st) in
  let tagid_type = tag_id_type (JCtag st) in
  let ptr_type = pointer_type (JCtag st) in
(*  let all_fields = embedded_struct_fields st in
  let all_roots = embedded_struct_roots st in
  let all_roots = List.map find_struct all_roots in*)
  let all_fields = all_memories ~select:fully_allocated (JCtag st) in
  let all_roots = all_types ~select:fully_allocated (JCtag st) in
  let all_tovs = List.map (fun st -> JCvariant st) all_roots in
  let alloc = alloc_table_name (JCtag st) in
  let tagtab = tag_table_name (JCtag st) in
    (* Declarations of field memories. *)
  let acc =
    if !Jc_options.separation_sem = SepRegions then acc else
      List.fold_left
	(fun acc fi ->
	  let mem = field_memory_type fi in
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

  let acc = (make_valid_pred (JCtag st)) :: acc in

  (* Allocation of one element parameter. *)
  let alloc_type = 
    Annot_type(
      (* no pre *)
      LTrue,
      (* [st_root pointer] *)
      Base_type ptr_type,
      (* [reads all_fields writes alloc,tagtab] *)
      (List.map alloc_table_name all_tovs
	@ List.map (fun fi -> fi.jc_field_info_final_name) all_fields),[alloc;tagtab],
      (* normal post *)
      make_and_list [
	(* [valid_one_st(result,alloc...)] *)
	make_valid_one_pred_app (JCtag st) (LVar "result");
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
    List.fold_right (fun fi acc ->
      Prod_type(field_memory_name fi,
		Ref_type(Base_type(field_memory_type fi)),
		acc)
    ) all_fields alloc_type 
  in
  let alloc_type =
    List.fold_right (fun a acc ->
      Prod_type(alloc_table_name a,Ref_type(Base_type(alloc_table_type a)),acc)
    ) all_tovs alloc_type
  in
  let alloc_type = Prod_type(alloc,Ref_type(Base_type alloc_ty),alloc_type) in
  let alloc_type = Prod_type("tt",unit_type,alloc_type) in
  let acc = 
    Param(false,alloc_one_param_name st,alloc_type) :: acc
  in

  (* Allocation parameter. *)
  let alloc_type = 
    Annot_type(
      (* [n >= 0] *)
      LPred("ge_int",[LVar "n";LConst(Prim_int "0")]),
      (* [st_root pointer] *)
      Base_type ptr_type,
      (* [reads all_fields; writes alloc,tagtab] *)
      (List.map alloc_table_name all_tovs
	@ List.map (fun fi -> fi.jc_field_info_final_name) all_fields), [alloc; tagtab],
      (* normal post *)
      make_and_list [
	(* [valid_st(result,0,n-1,alloc...)] *)
	make_valid_pred_app (JCtag st)
	  (LVar "result")
	  (LConst(Prim_int "0"))
	  (LApp("sub_int",[LVar "n"; LConst(Prim_int "1")]));
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
    List.fold_right (fun fi acc ->
      Prod_type(field_memory_name fi,
		Ref_type(Base_type(field_memory_type fi)),
		acc)
    ) all_fields alloc_type
  in
  let alloc_type =
    List.fold_right (fun a acc ->
      Prod_type(alloc_table_name a,Ref_type(Base_type(alloc_table_type a)),acc)
    ) all_tovs alloc_type
  in
  let alloc_type = Prod_type(alloc,Ref_type(Base_type alloc_ty),alloc_type) in
  let alloc_type = Prod_type("n",Base_type why_integer_type,alloc_type) in
  let acc = 
    Param(false,alloc_param_name st,alloc_type) :: acc
  in

  match st.jc_struct_info_parent with
    | None ->
	(* axiom for parenttag *)
	let name = st.jc_struct_info_name ^ "_parenttag_bottom" in
	let p = LPred("parenttag", [ LVar (tag_name st); LVar "bottom_tag" ]) in
	Axiom(name, p)::acc
    | Some p ->
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

let rec pset ~global_assertion before loc = 
  let fpset = pset ~global_assertion before in
  match loc with
    | JCLSderef(ls,lab,fi,r) ->
	let m = lvar ~label_in_name:global_assertion lab (field_region_memory_name(fi,r)) in
	LApp("pset_deref", [m;fpset ls])
    | JCLSvar vi -> 
	let m = lvar_info before vi in
	LApp("pset_singleton", [m])
    | JCLSrange(ls,None,None) ->
	let ls = fpset ls in
	LApp("pset_all", [ls])
    | JCLSrange(ls,None,Some b) ->
	let ls = fpset ls in
	let b', lets = term ~global_assertion before before b in
	assert (lets = []);
	LApp("pset_range_left", 
	     [ls; 
	      term_coerce b.jc_term_loc integer_type b.jc_term_type b'])
    | JCLSrange(ls,Some a,None) ->
	let ls = fpset ls in
	let a', lets = term ~global_assertion before before a in
	assert (lets = []);
	LApp("pset_range_right", 
	     [ls; 
	      term_coerce a.jc_term_loc integer_type a.jc_term_type a'])
    | JCLSrange(ls,Some a,Some b) ->
	let ls = fpset ls in
	let a', lets1 = term ~global_assertion before before a in
	let b', lets2 = term ~global_assertion before before b in
	assert (lets1 = [] && lets2 = []);
	LApp("pset_range", 
	     [ls; 
	      term_coerce a.jc_term_loc integer_type a.jc_term_type a'; 
	      term_coerce b.jc_term_loc integer_type b.jc_term_type b'])
	
let rec collect_locations ~global_assertion before (refs,mems) loc =
  match loc with
    | JCLderef(e,lab,fi,fr) -> 
	let iloc = pset ~global_assertion lab e in
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
    | JCLat(loc,lab) ->
	collect_locations ~global_assertion before (refs,mems) loc

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
    FieldRegionMap.fold
      (fun (fi,r) labels m -> 
	 FieldRegionMap.add (fi,r) [] m)
      ef.jc_writes.jc_effect_memories FieldRegionMap.empty 
  in
  let refs,mems = 
    List.fold_left (collect_locations ~global_assertion:false before) (refs,mems) locs
  in
  let a =
    StringMap.fold
      (fun v p acc -> 
	if p then acc else
	  make_and acc (LPred("eq", [LVar v; lvar before v])))
      refs LTrue
  in
  FieldRegionMap.fold
    (fun (fi,r) p acc -> 
       let v = field_region_memory_name(fi,r) in
       let alloc = alloc_region_table_name(JCtag fi.jc_field_info_root,r) in
       make_and acc
	 (LPred("not_assigns",
		[lvar before alloc; 
		 lvar before v;
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
    
let interp_fun_params f write_mems read_mems annot_type =
  let annot_type = 
    if !Jc_options.separation_sem = SepNone then annot_type else
      List.fold_right (fun (name,ty) acc ->
	Prod_type(name,Base_type ty,acc)
      ) read_mems annot_type
  in
  let annot_type = 
    if !Jc_options.separation_sem = SepNone then annot_type else
      List.fold_right (fun (name,ty) acc ->
	Prod_type(name,Ref_type(Base_type ty),acc)
      ) write_mems annot_type
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
  let requires_param = 
    (named_assertion 
       ~global_assertion:false 
       LabelHere 
       LabelHere 
       spec.jc_fun_requires) 
  in
  let free_requires = 
    (named_assertion 
       ~global_assertion:false 
       LabelHere 
       LabelHere 
       spec.jc_fun_free_requires)
  in
  let requires = make_and requires_param free_requires in
  let requires_param = if Jc_options.trust_ai then requires_param else requires in
  let requires =
    List.fold_left 
      (fun acc vi ->
	 make_and
	   (match vi.jc_var_info_type with
	      | JCTpointer (tov, n1o, n2o) ->
		  let vit, lets = 
		    term ~global_assertion:false LabelHere LabelHere
		      (term_var_no_loc vi) 
		  in
		  begin match n1o, n2o with
		    | None, _ | _, None -> LTrue
		    | Some n1, Some n2 ->
			let pred =
			  make_valid_pred_app tov
			    vit
			    (const_of_num n1)
			    (const_of_num n2)
			in
			make_pred_binds lets pred
		  end
	      | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull -> LTrue)
	   acc)
      requires
      f.jc_fun_info_parameters
  in
  (* partition behaviors as follows:
     - (optional) 'safety' behavior (if Arguments Invariant Policy is selected)
     - (optional) 'inferred' behaviors (calculated by analysis)
     - user defined behaviors *)
  let (safety_behavior,
       normal_behaviors_inferred, normal_behaviors, 
       excep_behaviors_inferred, excep_behaviors) =
    List.fold_left
      (fun (safety, normal_inferred, normal, excep_inferred, excep) (loc, id, b) ->
	 let post =
	   match b.jc_behavior_assigns with
	     | None ->
		 (*
		   eprintf "lab,loc for ensures: \"%s\", %a@."
		   b.jc_behavior_ensures.jc_assertion_label
		   Loc.gen_report_position b.jc_behavior_ensures.jc_assertion_loc;
		 *)
		 (named_assertion ~global_assertion:false LabelPost LabelPre 
		    b.jc_behavior_ensures)		
	     | Some (locassigns, a) ->
		 named_jc_assertion loc
		   (make_and
		      (named_assertion ~global_assertion:false LabelPost LabelPre 
			 b.jc_behavior_ensures)		
		      (named_jc_assertion
			 locassigns
			 (assigns LabelHere f.jc_fun_info_effects (Some a))))
	 in
	 let a =
	   match b.jc_behavior_assumes with
	     | None -> post
	     | Some e -> 
		 make_impl (assertion ~global_assertion:false LabelHere LabelHere e) post
	 in
	   match b.jc_behavior_throws with
	     | None -> 
		 begin match id with
		   | "safety" ->
		       ((id, b, a) :: safety, 
			normal_inferred, normal, excep_inferred, excep)
		   | "inferred" -> 
		       (safety,
			(id, b, a) :: normal_inferred, 
			(if Jc_options.trust_ai then normal else (id, b, a) :: normal), 
			excep_inferred, excep)
		   | _ -> 
		       (safety, 
			normal_inferred, (id, b, a) :: normal, 
			excep_inferred, excep)
		 end
	     | Some ei ->
		 let eb =
		   try
		     ExceptionMap.find ei excep
		   with Not_found -> []
		 in
		   if id = "inferred" then 
		     (safety, normal_inferred, normal, 
		      ExceptionMap.add ei ((id, b, a) :: eb) excep_inferred, 
		      if Jc_options.trust_ai then excep else 
			ExceptionMap.add ei ((id, b, a) :: eb) excep)
		   else
		     (safety, normal_inferred, normal, excep_inferred, 
		      ExceptionMap.add ei ((id, b, a) :: eb) excep))
      ([], [], [], ExceptionMap.empty, ExceptionMap.empty)
      spec.jc_fun_behavior
  in
  let user_excep_behaviors = excep_behaviors in
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
    FieldRegionMap.fold
      (fun (fi,r) labels acc -> 
	let mem = field_region_memory_name(fi,r) in
	if Region.polymorphic r then
	  if RegionList.mem r f.jc_fun_info_param_regions then
	    if FieldRegionMap.mem (fi,r) 
	      f.jc_fun_info_effects.jc_writes.jc_effect_memories 
	    then mem::acc 
	    else acc
	  else acc
	else mem::acc)
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
    StringRegionSet.fold
      (fun (a,r) acc -> 
	let alloc = alloc_region_table_name2(a,r) in
	if Region.polymorphic r then
	  if RegionList.mem r f.jc_fun_info_param_regions then
	    if StringRegionSet.mem (a,r) 
	      f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table 
	    then alloc::acc 
	    else acc
	  else acc
	else alloc::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_alloc_table
      reads
  in
  let reads =
    StringSet.fold
      (fun v acc -> (tag_table_name2 v)::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_tag_table
      reads
  in
  let reads =
    StringSet.fold
      (fun v acc -> (mutable_name2 v)::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_mutable
      reads
  in
  let reads =
    StringSet.fold
      (fun v acc -> (committed_name2 v)::acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_committed
      reads
  in
  let writes =
    FieldRegionMap.fold
      (fun (fi,r) labels acc ->
	let mem = field_region_memory_name(fi,r) in
	if Region.polymorphic r then
	  if RegionList.mem r f.jc_fun_info_param_regions then mem::acc else acc
	else mem::acc)
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
    StringRegionSet.fold
      (fun (a,r) acc ->
	let alloc = alloc_region_table_name2(a,r) in
	if Region.polymorphic r then
	  if RegionList.mem r f.jc_fun_info_param_regions then alloc::acc else acc
	else alloc::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
      writes
  in
  let writes =
    StringSet.fold
      (fun v acc -> (tag_table_name2 v)::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_tag_table
      writes
  in
  let writes =
    StringSet.fold
      (fun v acc -> (mutable_name2 v)::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_mutable
      writes
  in
  let writes =
    StringSet.fold
      (fun v acc -> (committed_name2 v)::acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_committed
      writes
  in
  let param_write_mems,local_write_mems =
    FieldRegionMap.fold
      (fun (fi,r) labels (param_acc,local_acc) ->
	if Region.polymorphic r then
	  let mem = field_region_memory_name(fi,r),field_memory_type fi in
	  if RegionList.mem r f.jc_fun_info_param_regions then
	    mem::param_acc,local_acc
	  else
	    param_acc,mem::local_acc
	else param_acc,local_acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_memories
      ([],[])
  in
  let param_read_mems,local_read_mems =
    FieldRegionMap.fold
      (fun (fi,r) labels ((param_acc,local_acc) as acc) ->
	 if FieldRegionMap.mem (fi,r) 
	   f.jc_fun_info_effects.jc_writes.jc_effect_memories
	 then acc else
	   if Region.polymorphic r then
	  let mem = field_region_memory_name(fi,r),field_memory_type fi in
	  if RegionList.mem r f.jc_fun_info_param_regions then
	    mem::param_acc,local_acc
	  else
	    param_acc,mem::local_acc
	else param_acc,local_acc)
      f.jc_fun_info_effects.jc_reads.jc_effect_memories
      ([],[])
  in
  let param_write_allocs,local_write_allocs =
    StringRegionSet.fold
      (fun (a,r) (param_acc,local_acc) ->
	if Region.polymorphic r then
	  let alloc = alloc_region_table_name2(a,r),alloc_table_type2 a in
	  if RegionList.mem r f.jc_fun_info_param_regions then
	    alloc::param_acc,local_acc
	  else
	    param_acc,alloc::local_acc
	else param_acc,local_acc)
      f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
      ([],[])
  in
  let param_read_allocs,local_read_allocs =
    StringRegionSet.fold
      (fun (a,r) (param_acc,local_acc) ->
	if Region.polymorphic r then
	  let alloc = alloc_region_table_name2(a,r),alloc_table_type2 a in
	  if RegionList.mem r f.jc_fun_info_param_regions then
	    alloc::param_acc,local_acc
	  else
	    param_acc,alloc::local_acc
	else param_acc,local_acc)
      (StringRegionSet.diff 
	f.jc_fun_info_effects.jc_reads.jc_effect_alloc_table
	f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table)
      ([],[])
  in
  let safety_post =
    List.fold_right
      (fun (_, _, e) acc -> make_and e acc)
      safety_behavior LTrue
  in
  let normal_post =
    List.fold_right
      (fun (_,_,e) acc -> make_and e acc)
      normal_behaviors LTrue
  in
  let normal_post_inferred =
    List.fold_right
      (fun (_,_,e) acc -> make_and e acc)
      normal_behaviors_inferred LTrue
  in
  let excep_posts =
    ExceptionMap.fold
      (fun ei l acc ->
	 let p = 
	   List.fold_right (fun (_,_,e) acc -> make_and e acc) l LTrue
	 in (exception_name ei,p)::acc) 
      excep_behaviors []
  in
  let excep_posts_inferred =
    ExceptionMap.fold
      (fun ei l acc ->
	 let p = 
	   List.fold_right (fun (_,_,e) acc -> make_and e acc) l LTrue
	 in (exception_name ei,p)::acc) 
      excep_behaviors_inferred []
  in
    (* DEBUG *)
    (* Jc_options.lprintf "DEBUG: tr_fun 2@."; *)
    (* why parameter for calling the function *)
  let ret_type = tr_type f.jc_fun_info_result.jc_var_info_type in
  let param_normal_post = 
    if is_purely_exceptional_fun spec then LFalse else
      make_and_list [safety_post; normal_post; normal_post_inferred] 
  in
  let param_excep_posts = excep_posts @ excep_posts_inferred in
  let why_param = 
    let annot_type =
      Annot_type(requires_param, ret_type,
		 reads,writes, param_normal_post, param_excep_posts)
    in
    let fun_type = 
      interp_fun_params f (param_write_allocs @ param_write_mems) (param_read_allocs @ param_read_mems) annot_type 
    in
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
	    let write_mems = 
	      List.map (fun (name,ty) -> name,Ref_type(Base_type ty)) 
		(param_write_mems @ param_write_allocs)
	    in
	    let read_mems = 
	      List.map (fun (name,ty) -> name,Base_type ty) 
		(param_read_mems @ param_read_allocs)
	    in
	    let params = match f.jc_fun_info_parameters with
	      | [] -> ["tt", unit_type]
	      | l -> List.map parameter l
	    in
	    let params = params @ write_mems @ read_mems in
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
		(match f.jc_fun_info_result.jc_var_info_type with
		   | JCTnative Tunit -> true
		   | _ -> false);		
	      printf "Generating Why function %s@."
		f.Jc_fenv.jc_fun_info_final_name;
	      (* default behavior *)
	      let body_safety = 
		statement_list ~infunction:f ~threats:true body in
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
		List.fold_left (fun acc (mem_name,_) ->
		  Let(mem_name,App(Var "any_memory",Void),acc)
		) tblock local_read_mems
	      in
	      let tblock =
		List.fold_left (fun acc (mem_name,_) ->
		  Let_ref(mem_name,App(Var "any_memory",Void),acc)
		) tblock local_write_mems
	      in
	      let tblock =
		List.fold_left (fun acc (alloc_name,_) ->
		  Let(alloc_name,App(Var "any_alloc_table",Void),acc)
		) tblock local_read_allocs
	      in
	      let tblock =
		List.fold_left (fun acc (alloc_name,_) ->
		  Let_ref(alloc_name,App(Var "any_alloc_table",Void),acc)
		) tblock local_write_allocs
	      in
	      let tblock = 
		if !return_void then
		  Try(append tblock (Raise(jessie_return_exception,None)),
		      jessie_return_exception,None,Void)
		else
		  let e = any_value f.jc_fun_info_result.jc_var_info_type in
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
	      let newid = f.jc_fun_info_name ^ "_safety" in
	      let _ = reg_loc 
		~id:newid
		~oldid:f.jc_fun_info_name
		~name:("function " ^ f.jc_fun_info_name)
		~beh:"Safety" loc 
	      in
	      let acc = 
		if is_purely_exceptional_fun spec then acc else
		  Def(
		    newid,
		    Fun(
		      params,
		      requires,
		      tblock_safety,
		      safety_post,
		      excep_posts_for_others None excep_behaviors
		    ))::acc
	      in
		(* user behaviors *)
	      let acc = 
		if spec.jc_fun_behavior = [] then
		  acc
		else
		  let body = statement_list ~infunction:f ~threats:false body in
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
		      let e = any_value f.jc_fun_info_result.jc_var_info_type in
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
		      user_excep_behaviors acc
		  in
		    acc 
	in why_param::acc

let tr_logic_type id acc = Type(id,[])::acc

let tr_axiom id is_axiom p acc = 
  let ef = Jc_effect.assertion empty_effects p in
  let a = assertion ~global_assertion:true LabelHere LabelHere p in
  let a =
    FieldRegionMap.fold 
      (fun (fi,r) labels a -> 
	 LogicLabelSet.fold
	   (fun lab a ->
	      LForall (label_var lab (field_region_memory_name(fi,r)), 
		       field_memory_type fi, a))
	   labels a)
      ef.jc_effect_memories a 
  in
  let a =
    StringRegionSet.fold (fun (alloc,r) a -> 
      LForall (alloc_region_table_name2(alloc,r), alloc_table_type2 alloc, a)
    ) ef.jc_effect_alloc_table a 
  in
  (* How to add quantification on other effects (alloc, tag) without knowing 
   * their type ? *)
  if is_axiom then Axiom(id,a)::acc else Goal(id,a)::Axiom(id ^ "_as_axiom",a)::acc

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

let tr_region r acc =
  Type(r.jc_reg_final_name,[]) :: acc

let tr_memory (fi,r) acc =
  Param(
    false,field_region_memory_name(fi,r),
    Ref_type(Base_type(field_memory_type fi))) :: acc

let tr_alloc_table (tov,r) acc =
  Param(
    false,alloc_region_table_name(tov,r),
    Ref_type(Base_type(alloc_table_type tov))) :: acc

let tr_alloc_table2 (a,r) acc =
  Jc_options.lprintf "Looking for %s in Jc_interp.tr_alloc_table2@." a;
  tr_alloc_table (find_tag_or_variant a, r) acc

(*************************
        Variants
*************************)

let tr_variant vi acc =
  let tag_table =
    Param(
      false,
      variant_tag_table_name vi,
      Ref_type(
	Base_type {
	  logic_type_name = tag_table_type_name;
	  logic_type_args = [variant_model_type vi];
	}))
  in
  let alloc_table =
    Param(
      false,
      variant_alloc_table_name vi,
      Ref_type(
	Base_type {
	  logic_type_name = alloc_table_type_name;
	  logic_type_args = [variant_model_type vi];
	}))
  in
  let type_def = Type(variant_type_name vi, []) in
  let axiom_on_tags =
    let v = "x" in
    let tag_table = tag_table_name_vi vi in
    Axiom(
      variant_axiom_on_tags_name vi,
      LForall(
	v,
	pointer_type (JCvariant vi),
	LForall(
	  tag_table,
	  tag_table_type (JCvariant vi),
	  make_or_list
	    (List.map
	       (make_instanceof (LVar tag_table) (LVar v))
	       vi.jc_variant_info_roots)
      )))
  in
  let acc = type_def::alloc_table::tag_table::axiom_on_tags::acc in
  (make_valid_pred (JCvariant vi)) :: acc

(*
  Local Variables: 
  compile-command: "unset LANG; make -j -C .. bin/jessie.byte"
  End: 
*)
