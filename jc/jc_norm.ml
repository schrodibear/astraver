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
open Format

let functions_table = Hashtbl.create 97
let variables_table = Hashtbl.create 97

(* result of test, to be used during translation of lazy boolean operators
   to instructions *)

let true_output = exception_info None "True"
let false_output = exception_info None "False"
let loop_exit = exception_info None "Loop_exit"
let loop_continue = exception_info None "Loop_continue"

let exceptions_table = Jc_typing.exceptions_table

let () = Hashtbl.add exceptions_table "True" true_output
let () = Hashtbl.add exceptions_table "False" false_output
let () = Hashtbl.add exceptions_table "Loop_exit" loop_exit
let () = Hashtbl.add exceptions_table "Loop_continue" loop_continue


(* expressions *)

let make_const loc t c =
  let node = JCEconst c in
  { jc_expr_loc = loc; 
    jc_expr_type = t;
    jc_expr_label = "";
    jc_expr_node = node; }

let void_const loc = make_const loc (JCTnative Tunit) JCCvoid
let true_const loc = make_const loc boolean_type (JCCboolean true)
let false_const loc = make_const loc boolean_type (JCCboolean false)
let one_const loc = make_const loc integer_type (JCCinteger "1")

let make_var loc vi =
  let node = JCEvar vi in
  { jc_expr_loc = loc; 
    jc_expr_type = vi.jc_var_info_type;
    jc_expr_label = "";
    jc_expr_node = node; } 

let make_deref loc e fi =
  let node = JCEderef (e, fi) in
  { jc_expr_loc = loc; 
    jc_expr_type = fi.jc_field_info_type;
    jc_expr_label = "";
    jc_expr_node = node; }

let rec make_or_list_test loc = function
  | [] -> false_const loc
  | [e] -> e
  | e :: r -> 
      let node = JCEbinary (e, Blor, make_or_list_test loc r) in
      { jc_expr_loc = loc; 
        jc_expr_type = boolean_type;
	jc_expr_label = "";
	jc_expr_node = node; } 

(* expressions on the typed AST, not the normalized AST *)

let make_tconst loc c =
  let t,c = Jc_pervasives.const c in
  let node = JCTEconst c in
  { jc_texpr_loc = loc; 
    jc_texpr_type = t; 
    jc_texpr_label = "";
    jc_texpr_node = node; }

let make_tincr_local loc t op vi =
  let node =  JCTEincr_local (op, vi) in
  { jc_texpr_loc = loc; 
    jc_texpr_type = t; 
    jc_texpr_label = "";
    jc_texpr_node = node; }

let make_tincr_heap loc t op e fi =
  let node = JCTEincr_heap (op, e, fi) in
  { jc_texpr_loc = loc; 
    jc_texpr_type = t; 
    jc_texpr_label = "";
    jc_texpr_node = node; }

(* statements *)

let make_node loc node = 
  { jc_statement_loc = loc; jc_statement_node = node; }

let make_assign_var loc vi e =
  make_node loc (JCSassign_var (vi, e))

let make_assign_heap loc e1 fi e2 =
  make_node loc (JCSassign_heap (e1, fi, e2))

let make_block loc sl =
  match sl with 
    | [s] -> s
    | s :: l -> 
	make_node s.jc_statement_loc (JCSblock sl)
    | [] -> 
	make_node loc (JCSblock sl)
	

let make_block_node loc sl snode =
  match sl with
    | [] -> snode
    | _ -> JCSblock (sl @ [make_node loc snode])

let make_call loc vio f el s =
  make_node loc (JCScall (vio, f, el, s)) 

let make_if loc e ts es =
  make_node loc (JCSif (e,ts,es))

let make_throw loc exc e =
  make_node loc (JCSthrow (exc,e))

let make_loop loc la s =
  make_node loc (JCSloop (la,s))

let make_try loc s exl fs =
  make_node loc (JCStry (s, exl, fs))

let make_decl loc vi eo s =
  make_node loc (JCSdecl (vi, eo, s))

let make_decls loc sl tl =
  List.fold_right 
    (fun vi acc -> 
       (* real initial value does not matter *)
       let t,cst =
	 match vi.jc_var_info_type with
	   | JCTnative t ->
	       begin
		 match t with
		   | Tboolean -> boolean_type, JCCboolean false
		   | _ -> integer_type, JCCinteger "0"
	       end
	   | JCTenum _ ->  integer_type, JCCinteger "0"
	   | JCTnull | JCTpointer _ -> JCTnull, JCCnull
	   | JCTlogic _ -> assert false
       in
       make_decl loc vi (Some (make_const loc t cst)) acc)
    tl (make_block loc sl)

let make_return loc t e =
  make_node loc (JCSreturn (t,e))

let make_pack loc si e as_t =
  make_node loc (JCSpack (si, e, as_t))

let make_unpack loc si e from_t =
  make_node loc (JCSunpack (si, e, from_t))

(* statements on the typed AST, not the normalized AST *)

let make_tnode loc node = 
  { jc_tstatement_loc = loc; jc_tstatement_node = node; }

let make_tblock loc sl =
  match sl with 
    | [s] -> s
    | _ -> make_tnode loc (JCTSblock sl)

let make_tif loc e ts es =
  make_tnode loc (JCTSif (e,ts,es))

let make_tthrow loc exc e =
  make_tnode loc (JCTSthrow (exc,e))

let make_binary loc e1 t op e2 =
  let t = match t with
    | JCTenum _ -> integer_type
    | _ -> t
  in
    { jc_expr_node = JCEbinary(e1, op, e2);
      jc_expr_type = t;
      jc_expr_label = "";
      jc_expr_loc = loc }

let make_int_binary loc e1 op e2 = make_binary loc e1 integer_type op e2


let make_incr_local loc op vi =
  make_assign_var loc vi
    (make_int_binary loc (make_var loc vi) op (one_const loc))

let make_incr_heap loc op e fi = 
  let d =
    { jc_expr_loc = loc;
      jc_expr_type = fi.jc_field_info_type;
      jc_expr_label = "";
      jc_expr_node = JCEderef(e,fi) ;
    }
  in
  make_assign_heap loc e fi
    (make_int_binary loc d op (one_const loc))
  

let op_of_incdec = function
  | Prefix_inc | Postfix_inc -> Badd_int 
  | Prefix_dec | Postfix_dec -> Bsub_int


(*
  
  expr e : returns ((sl, tl), ne) where
  
   ne = normalized expression for e, without side-effect
   sl = sequences of statements to execute before e
   tl = sequences of fresh variables needed

  in other words, if tl = x1..xn, e is normalized into :

     t1 x1 = <default value for type t1>;
     ...
     tn xn = <default value for type tn>;
     sl;
     ...ne...

*)

let rec expr e =
  let loc = e.jc_texpr_loc in
  let (sl, tl), ne =
    match e.jc_texpr_node with
    | JCTEconst c -> ([], []), JCEconst c
    | JCTEvar vi -> ([], []), JCEvar vi
    | JCTEunary(op,e1) ->
	let (l1, tl1), e1 = expr e1 in
	(l1, tl1), JCEunary (op, e1)
    | JCTEbinary (e1, op, e2) ->
	let (l1, tl1), e1 = expr e1 in
	let (l2, tl2), e2 = expr e2 in
	  begin
	    match op with
	      | Bland ->
		  let tmp = newrefvar boolean_type in
		  let e1_false_stat = make_assign_var loc tmp (false_const loc) in
		  let e2_false_stat = make_assign_var loc tmp (false_const loc) in
		  let true_stat = make_assign_var loc tmp (true_const loc) in
		  let if_e2_stat = make_if loc e2 true_stat e2_false_stat in
		  let block_e2 = make_block loc (l2 @ [if_e2_stat]) in
		  let if_e1_stat = make_if loc e1 block_e2 e1_false_stat in
		    (l1 @ [if_e1_stat], [tmp]), JCEvar tmp
	      | Blor ->
		  let tmp = newrefvar boolean_type in
		  let e1_true_stat = make_assign_var loc tmp (true_const loc) in
		  let e2_true_stat = make_assign_var loc tmp (true_const loc) in
		  let false_stat = make_assign_var loc tmp (false_const loc) in
		  let if_e2_stat = make_if loc e2 e2_true_stat false_stat in
		  let block_e2 = make_block loc (l2 @ [if_e2_stat]) in
		  let if_e1_stat = make_if loc e1 e1_true_stat block_e2 in
		    (l1 @ [if_e1_stat], [tmp]), JCEvar tmp
	      | _ -> (* Note: no special case for Unot *)
		  (l1@l2, tl1@tl2), JCEbinary (e1, op, e2)
	  end
    | JCTEshift (e1, e2) ->
	let (l1, tl1), e1 = expr e1 in
	let (l2, tl2), e2 = expr e2 in
	(* Translate recursive shifts into single shift. *)
	let e1,e2 = match e1.jc_expr_node with
	  | JCEshift(e3,e4) -> 
	      let adde = JCEbinary(e4,Badd_int,e2) in
	      e3, { e4 with jc_expr_node = adde; }
	  | _ -> e1,e2
	in
	(l1@l2, tl1@tl2), JCEshift (e1, e2)
    | JCTEsub_pointer (e1, e2) ->
	let (l1, tl1), e1 = expr e1 in
	let (l2, tl2), e2 = expr e2 in
	(l1@l2, tl1@tl2), JCEsub_pointer (e1, e2)
    | JCTEderef (e, f) ->
	let (l, tl), e = expr e in
	(l, tl), JCEderef (e, f)
    | JCTEcall (f, el) ->
	let ltl, el = List.split (List.map expr el) in
	let ll, tll = List.split ltl in
	let (l, tl), ecall = call loc f el ~binder:true ll in
	let ecall = match ecall with
	| Some b -> JCEvar b
	| None -> assert false
	in
	(l, tl@(List.flatten tll)), ecall
    | JCTEoffset (k, e, si) -> 
	let (l, tl), e = expr e in
	(l, tl), JCEoffset (k, e, si)
    | JCTEinstanceof (e, s) ->
	let (l, tl), e = expr e in
	(l, tl), JCEinstanceof (e, s)
    | JCTEcast (e, s) ->
	let (l, tl), e = expr e in
	(l, tl), JCEcast (e, s)
    | JCTErange_cast (r, e) ->
	let (l, tl), e = expr e in
	(l, tl), JCErange_cast (r, e)
    | JCTEalloc (e, s) ->
	let (l, tl), e = expr e in
	(l, tl), JCEalloc (e, s)
    | JCTEfree e ->
	let (l, tl), e = expr e in
	(l, tl), JCEfree e
    | JCTEassign_var (vi, e) ->
	let (l, tl), e = expr e in
	let stat = make_assign_var loc vi e in
	(l@[stat], tl), JCEvar vi
    | JCTEassign_var_op (vi,op, e) -> 
	(* 
	   vi op= e becomes:
	   
	   stat0: tmp <- vi
	   <e effects>
           stat: vi <- tmp op e
           ... vi ...
	 *)             
	let tmp = newrefvar vi.jc_var_info_type in
	let stat0 = 
	  make_assign_var loc tmp (make_var loc vi) 
	in
	let (l, tl), e = expr e in
	let e = 
	  make_binary loc (make_var loc tmp) vi.jc_var_info_type op e 
	in
	let stat = make_assign_var loc vi e in
	(stat0::l@[stat], tmp::tl), JCEvar vi
    | JCTEassign_heap (e1, fi, e2) ->
	let (l1, tl1), e1 = expr e1 in
	let (l2, tl2), e2 = expr e2 in
	let stat = make_assign_heap loc e1 fi e2 in
	(l1@l2@[stat], tl1@tl2), JCEderef (e1, fi)
    | JCTEassign_heap_op (e1, fi, op, e2) -> 
	(* 
	   e1.fi op= e2 becomes:
	   
	   <e1 effects>
           stat1: tmp1 <- e1
           <e2 effects>
           stat2: tmp2 <- tmp1.fi op e2
	   stat: tmp1.fi <- tmp2
           ... tmp2 ...
	 *)             
	let (l1, tl1), e1 = expr e1 in
	let tmp1 = newrefvar e1.jc_expr_type in
	let stat1 = make_assign_var loc tmp1 e1 in
	let (l2, tl2), e2 = expr e2 in
	let e3 = 
	  make_binary loc 
	    (make_deref loc (make_var loc tmp1) fi) 
	    fi.jc_field_info_type op e2
	in
	let tmp2 = newrefvar fi.jc_field_info_type in
	let stat2 = make_assign_var loc tmp2 e3 in
	let stat = 
	  make_assign_heap loc (make_var loc tmp1) fi (make_var loc tmp2) 
	in
	(l1@stat1::l2@[stat2; stat], tl1@tmp1::tl2@[tmp2]), JCEvar tmp2
    | JCTEincr_local (op, vi) ->
	begin match op with
	| Prefix_inc | Prefix_dec ->
	    ([make_incr_local loc (op_of_incdec op) vi], []), JCEvar vi
	| Postfix_inc | Postfix_dec ->
	    let tmp = newrefvar vi.jc_var_info_type in
	    let stat0 = 
	      make_assign_var loc tmp (make_var loc vi) 
	    in
	    ([stat0; make_incr_local loc (op_of_incdec op) vi], [tmp]), 
	    JCEvar tmp
	end
    | JCTEincr_heap (op, e, fi) ->
	begin match op with
	| Prefix_inc | Prefix_dec ->
	    let (l, tl), e = expr e in
	    (l@[make_incr_heap loc (op_of_incdec op) e fi], tl), 
	    JCEderef (e, fi)
	| Postfix_inc | Postfix_dec ->
	    let (l, tl), e = expr e in
	    let tmp = newrefvar fi.jc_field_info_type in
	    let stat0 = 
	      make_assign_var loc tmp (make_deref loc e fi) 
	    in
	    (l@stat0::[make_incr_heap loc Badd_int e fi], tl@[tmp]), 
	    JCEvar tmp
	end
    | JCTEif (e1, e2, e3) ->
	let (l1, tl1), e1 = expr e1 in
	let (l2, tl2), e2 = expr e2 in
	let (l3, tl3), e3 = expr e3 in
	let tmp = newrefvar e2.jc_expr_type in
	let assign2 = make_assign_var loc tmp e2 in
	let assign3 = make_assign_var loc tmp e3 in
	let if_e1_stat = 
	  make_if loc e1 
	    (make_block loc (l2 @ [assign2]))
	    (make_block loc (l3 @ [assign3]))
	in
	  (l1@[if_e1_stat], tl1@tl2@tl3@[tmp]), JCEvar tmp
  in 
    (sl, tl), 
  { jc_expr_node = ne;
    jc_expr_type = e.jc_texpr_type;
    jc_expr_label = e.jc_texpr_label;
    jc_expr_loc = e.jc_texpr_loc }
    
and call loc f el ~binder ll = 
  if binder then
    let tmp = newvar f.jc_fun_info_return_type in
    let stat = make_call loc (Some tmp) f el (make_block loc []) in
    (* [tmp] will be declared in a post-treatement of the calls generated *)
    ((List.flatten ll)@[stat], []), Some tmp

  else
    let stat = make_call loc None f el (make_block loc []) in
    ((List.flatten ll)@[stat], []), None

(* [el] is the only part not yet translated *)

and if_statement loc f el st sf =
(*
  if f == and_ then
    let e1,e2 = match el with [e1;e2] -> e1,e2 | _ -> assert false in
    let e1_false_stat = make_tthrow loc false_output 
      (Some (make_tconst loc JCCvoid)) in
    let e2_false_stat = make_tthrow loc false_output
      (Some (make_tconst loc JCCvoid)) in
    let true_stat = make_tthrow loc true_output
      (Some (make_tconst loc JCCvoid)) in
    let if_e2_stat = make_tif loc e2 true_stat e2_false_stat in
    let if_e1_stat = make_tif loc e1 if_e2_stat e1_false_stat in
    let try_body = statement if_e1_stat in
    let catch_list = 
      [(true_output, Some (newvar unit_type), st);
       (false_output, Some (newvar unit_type), sf)] in
    make_try loc try_body catch_list (make_block loc [])
  else 
  if f == or_ then
    let e1,e2 = match el with [e1;e2] -> e1,e2 | _ -> assert false in
    let e1_true_stat = make_tthrow loc true_output
      (Some (make_tconst loc JCCvoid)) in
    let e2_true_stat = make_tthrow loc true_output
      (Some (make_tconst loc JCCvoid)) in
    let false_stat = make_tthrow loc false_output
      (Some (make_tconst loc JCCvoid)) in
    let if_e2_stat = make_tif loc e2 e2_true_stat false_stat in
    let if_e1_stat = make_tif loc e1 e1_true_stat if_e2_stat in
    let try_body = statement if_e1_stat in
    let catch_list = 
      [(true_output, Some (newvar unit_type), st);
       (false_output, Some (newvar unit_type), sf)] in
    make_try loc try_body catch_list (make_block loc [])
    
  else 
if f == not_ then
    let e = match el with [e] -> e | _ -> assert false in
    let true_stat = make_tthrow loc true_output
      (Some (make_tconst loc JCCvoid)) in
    let false_stat = make_tthrow loc false_output
      (Some (make_tconst loc JCCvoid)) in
    let if_stat = make_tif loc e false_stat true_stat in
    let try_body = statement if_stat in
    let catch_list = 
      [(true_output, Some (newvar unit_type), st);
       (false_output, Some (newvar unit_type), sf)] in
    make_try loc try_body catch_list (make_block loc [])

  else 
*)
    let ltl,el = List.split (List.map expr el) in
    let ll,tl = List.split ltl in
    let (l,etl),ecall = call loc f el ~binder:true ll in
    let ecall = match ecall with
      | Some b -> make_var loc b
      | None -> assert false
    in
    let if_stat = make_if loc ecall st sf in
    make_decls loc (l @ [if_stat]) ((List.flatten tl) @ etl) 

      
and statement s =
  let loc = s.jc_tstatement_loc in
  let ns = 
    match s.jc_tstatement_node with
      | JCTSblock sl ->
	  JCSblock (List.map statement sl)
      | JCTSexpr e ->
	  let prefix op = match op with 
	    | Prefix_inc | Postfix_inc -> Prefix_inc
	    | Prefix_dec | Postfix_dec -> Prefix_dec
	  in
	  let sl, tl = 
	    match e.jc_texpr_node with
	      | JCTEcall (f, el) ->
		  let ltl,el = List.split (List.map expr el) in
		  let ll,tl = List.split ltl in
		  let sl,etl = fst (call loc f el ~binder:false ll) in
		  sl, etl @ (List.flatten tl)
	      | JCTEincr_local (op, vi) ->
		  (* avoid creating a useless temporary for postfix version *)
		  let typ = e.jc_texpr_type in
		  let e = make_tincr_local loc typ (prefix op) vi in
		  fst (expr e)
	      | JCTEincr_heap (op, se, fi) ->
		  (* avoid creating a useless temporary for postfix version *)
		  let typ = e.jc_texpr_type in
		  let e = make_tincr_heap loc typ (prefix op) se fi in
		  fst (expr e)
	      | _ -> fst (expr e)
	  in
	  (make_decls loc sl tl).jc_statement_node
      | JCTSassert(id,a) -> JCSassert (id, a)
      | JCTSdecl (vi, Some e, s) ->
	  let (sl,tl),e = expr e in
	  let decl_stat = make_decl loc vi (Some e) (statement s) in
	  (make_decls loc (sl @ [decl_stat]) tl).jc_statement_node
      | JCTSdecl (vi, None, s) ->
	  JCSdecl (vi, None, statement s)
      | JCTSif (e, st, sf) ->
	  let st = statement st in
	  let sf = statement sf in
	  begin match e.jc_texpr_node with
	    | JCTEcall (f, el) ->
		(if_statement loc f el st sf).jc_statement_node
	    | _ -> 
		let (sl,tl),e = expr e in
		let if_stat = make_if loc e st sf in
		(make_decls loc (sl @ [if_stat]) tl).jc_statement_node
	  end
      | JCTSwhile (e, la, body) ->
	  let exit_stat = make_tthrow loc loop_exit None in
	  let if_stat = statement (make_tif loc e body exit_stat) in
	  let continue_stat = make_throw loc loop_continue None in
	  let body = make_block loc [if_stat;continue_stat] in
	  let catch_continue = 
	    [(loop_continue, None, make_block loc [])] in
	  let try_continue = 
	    make_try loc body catch_continue (make_block loc []) in
	  let while_stat = make_loop loc la try_continue in
	  let catch_exit =
	    [(loop_exit, None, make_block loc [])] in
	  let try_exit = 
	    make_try loc while_stat catch_exit (make_block loc []) in
	  try_exit.jc_statement_node
      | JCTSfor (cond, updates, la, body) ->
	  let exit_stat = make_tthrow loc loop_exit None in
	  let if_stat = statement (make_tif loc cond body exit_stat) in
	  let continue_stat = make_throw loc loop_continue None in
	  let body = make_block loc [if_stat;continue_stat] in
	  let updates =
	    List.fold_right
	      (fun e acc -> statement {
		 jc_tstatement_loc = e.jc_texpr_loc;
		 jc_tstatement_node = JCTSexpr e;} :: acc)
	      updates
	      []
	  in		 
	  let catch_continue = 
	    [(loop_continue, None, make_block loc updates)] in
	  let try_continue = 
	    make_try loc body catch_continue (make_block loc []) in
	  let for_stat = make_loop loc la try_continue in
	  let catch_exit =
	    [(loop_exit, None, make_block loc [])] in
	  let try_exit = 
	    make_try loc for_stat catch_exit (make_block loc []) in
	  try_exit.jc_statement_node
	  
      | JCTSreturn_void -> JCSreturn_void  
      | JCTSreturn (t, e) ->
	  let (sl, tl), e = expr e in
	  let return_stat = make_return loc t e in
	    (make_decls loc (sl @ [return_stat]) tl).jc_statement_node
      | JCTSbreak "" -> 
	  JCSthrow (loop_exit, None)
      | JCTSbreak lab -> assert false (* TODO: see Claude *)
      | JCTScontinue lab -> assert false (* TODO: see Claude *)
      | JCTSgoto lab ->
	  let name_exc = "Goto_" ^ lab in
	  let goto_exc = exception_info None name_exc in
	  Hashtbl.add exceptions_table name_exc goto_exc;
	  JCSthrow (goto_exc, None)
      | JCTSlabel (_,s) -> 
	  assert false
	  (* Claude: label disappears ???? -> assert false *)
	  (* (statement s).jc_statement_node *)
      | JCTStry (s, cl, fs) ->
	  let cl = 
	    List.map (fun (ei, vi, s) -> (ei, vi, statement s)) cl in
	  JCStry (statement s, cl, statement fs)
      | JCTSthrow (ei, Some e) -> 
	  let (sl,tl),e = expr e in
	  let throw_stat = make_throw loc ei (Some e) in
	  (make_decls loc (sl @ [throw_stat]) tl).jc_statement_node
      | JCTSthrow (ei, None) ->
	  JCSthrow (ei, None)
      | JCTSpack (si, e, as_t) ->
	  let (sl,tl),e = expr e in
	  let pack_stat = make_pack loc si e as_t in
	  (make_decls loc (sl @ [pack_stat]) tl).jc_statement_node
      | JCTSunpack (si, e, from_t) ->
	  let (sl,tl),e = expr e in
	  let unpack_stat = make_unpack loc si e from_t in
	  (make_decls loc (sl @ [unpack_stat]) tl).jc_statement_node
      | JCTSswitch (e, csl) ->
	  let (sl,tl),e = expr e in
	  let test_one_case ~(neg:bool) c = 
	    (* test for case considered *)
	    let (slc,tlc),c = expr c in
	    assert (slc = [] && tlc = []); 
	    if neg then
	      make_int_binary loc e Bneq_int c
	    else
	      make_int_binary loc e Beq_int c
	  in
	  let collect_neg_case c = 
	    List.fold_right (fun c l -> match c with
	    | Some c -> test_one_case ~neg:true c :: l
	    | None -> l) c []
	  in
	  let all_neg_cases csl = 
	    List.fold_right (fun (c,_) l -> collect_neg_case c @ l) csl []
	  in
	  let test_one_case_or_default = function
	    | Some c -> test_one_case ~neg:false c
	    | None -> make_or_list_test loc (all_neg_cases csl)
	  in
	  let test_case_or_default c = 
	    let el = List.map test_one_case_or_default c in
	    make_or_list_test loc el
	  in
	  let _,ncsl = List.fold_left
	    (fun (previous_c,statl) (c,sl) -> 
	      (* statement list in case considered *)
	      let sl = List.map statement sl in
	      let block_stat = make_block loc sl in
	      let empty_block = make_block loc [] in
	      let current_c = previous_c @ c in
	      let etest = test_case_or_default current_c in
	      (* case translated into if-statement *)
	      let if_stat = make_if loc etest block_stat empty_block in
	      current_c, if_stat :: statl
	    ) ([],[]) csl 
	  in
	  let ncsl = List.rev ncsl in
	  let dummy_throw = make_throw loc loop_exit None in
	  let switch_stat = make_decls loc (sl @ ncsl @ [dummy_throw]) tl in
	  let catch_exit =
	    [(loop_exit, None, make_block loc [])] in
	  let try_exit = 
	    make_try loc switch_stat catch_exit (make_block loc []) in
	  try_exit.jc_statement_node

  in { jc_statement_node = ns;
       jc_statement_loc = loc }

and block_statement statements =
  let rec block = function
    | [] -> 
	[],[]
    | { jc_tstatement_node = JCTSlabel(lab,st) } as s :: bl ->
	let loc = s.jc_tstatement_loc in
	let (be,bl) = block (st::bl) in
	let name_exc = "Goto_" ^ lab in
	let goto_exc = exception_info None name_exc in
	Hashtbl.add exceptions_table name_exc goto_exc;
	[make_throw loc goto_exc None],(goto_exc,make_block loc be)::bl
    | s :: bl ->
	let append_block e (f,l) = (e :: f,l) in
	append_block (statement s) (block bl)
  in
  let be,bl = block statements in
  List.fold_left 
    (fun acc (goto_exc,s) ->
       let loc = s.jc_statement_loc in
       let catch_goto =
	 [(goto_exc, None, make_block loc [])] in
       make_try loc acc catch_goto (make_block loc [])
    ) (make_block Loc.dummy_position be) bl
       
(*
and assertion a =
  let loc = a.jc_tassertion_loc in
  let na =
    match a.jc_tassertion_node with
      | JCTAtrue ->
	  JCAtrue
      | JCTAfalse ->
	  JCAfalse
      | JCTAand al ->
	  JCAand (List.map assertion al)
      | JCTAor al ->
	  JCAor (List.map assertion al)
      | JCTAimplies (a1, a2) ->
	  JCAimplies (assertion a1, assertion a2)
      | JCTAiff (a1, a2) ->
	  JCAiff (assertion a1, assertion a2)
      | JCTAnot a ->
	  JCAnot (assertion a)
      | JCTArelation (t1, op, t2) ->
	  JCArelation (term t1, op, term t2)
      | JCTAapp (li, tl) ->
	  JCAapp (li, List.map term tl)
      | JCTAquantifier(q, vi, a) ->
	  JCAquantifier(q,vi, assertion a)
      | JCTAold a ->
	  JCAold (assertion a)
      | JCTAinstanceof (t, si) ->
	  JCAinstanceof (term t, si)
      | JCTAbool_term t ->
	  JCAbool_term (term t)
      | JCTAif (t, at, af) ->
	  JCAif (term t, assertion at, assertion af)
      | JCTAmutable (t, st, v) ->
	  JCAmutable (term t, st, tag v)
      | JCTAtagequality (t1, t2, h) ->
	  JCAtagequality (tag t1, tag t2, h)

  in { jc_assertion_node = na;
       jc_assertion_loc =  loc }

and tag t =
  let loc = t.jc_ttag_loc in
  let tag = match t.jc_ttag_node with
    | JCTTtag st -> JCTtag st
    | JCTTbottom -> JCTbottom
    | JCTTtypeof(t, st) -> JCTtypeof(term t, st)
  in {
    jc_tag_node = tag;
    jc_tag_loc = loc;
  }

and term t =
  let loc = t.jc_tterm_loc in
  let nt = 
    match t.jc_tterm_node with
      | JCTTconst c -> JCTconst c
      | JCTTvar vi -> JCTvar vi
      | JCTTunary(op,t1) -> JCTunary (op, term t1)
      | JCTTbinary (t1, op, t2) -> JCTbinary (term t1, op, term t2)
      | JCTTshift (t1, t2) -> JCTshift (term t1, term t2)
      | JCTTderef (t, fi) -> JCTderef (term t, fi)
      | JCTTapp (li, tl) -> JCTapp (li, List.map term tl)
      | JCTTold (t) -> JCTold (term t)
      | JCTToffset(k, t, si) -> JCToffset(k, term t, si)
      | JCTTinstanceof (t, si) -> JCTinstanceof (term t, si)
      | JCTTcast (t, si) -> JCTcast (term t, si)
      | JCTTif (t1, t2, t3) -> JCTif (term t1, term t2, term t3)
      | JCTTrange (t1, t2) -> JCTrange (term t1, term t2)
  in { jc_term_node = nt;
       jc_term_type = t.jc_tterm_type;
       jc_term_loc =  loc }

and loop_annot la =
  {
    jc_loop_invariant = assertion la.jc_tloop_invariant;
    jc_loop_variant = term la.jc_tloop_variant;
  }
    
and location_set ls=
  match ls with
    | JCTLSvar vi -> JCLSvar vi
    | JCTLSderef (ls, fi) -> JCLSderef (location_set ls, fi)
    | JCTLSrange (ls, t1, t2) -> JCLSrange (location_set ls, term t1, term t2)


and location l =
  match l with
    | JCTLvar vi -> JCLvar vi
    | JCTLderef (ls, fi) -> JCLderef (location_set ls, fi)


and behavior b =
  let a = match b.jc_tbehavior_assumes with
    | None -> None
    | Some a -> Some (assertion a)
  in
(*
  let requires = match b.jc_tbehavior_requires with
    | None -> None
    | Some a -> Some (assertion a)
  in
*)
  let assigns = match b.jc_tbehavior_assigns with
    | None -> None
    | Some ll -> Some (List.map location ll)
  in
  { 
    jc_behavior_throws = b.jc_tbehavior_throws;
    jc_behavior_assumes = a;
(*
    jc_behavior_requires = requires;
*)
    jc_behavior_assigns = assigns;
    jc_behavior_ensures = assertion b.jc_tbehavior_ensures;
  }

and fun_spec spec =
  {
    jc_fun_requires = assertion spec.jc_tfun_requires;
    jc_fun_behavior = 
      List.map (fun (s, b) -> (s, behavior b)) spec.jc_tfun_behavior;
  }
*)


let statement s =
  let s = statement s in

  let rec link_call s slnext =
    let loc = s.jc_statement_loc in
    match s.jc_statement_node with
      | JCScall (Some vi, f, el, s) -> 
	  begin match s.jc_statement_node with 
	    | JCSblock [] ->
		(* call may be created as the result of an
		   intermediate computation. In any case, moving the
		   statements that follow is correct. *)
		[make_call loc (Some vi) f el (make_block loc slnext)]
	    | _ -> 
		(make_call loc (Some vi) f el (link_stat s)) :: slnext
	  end
      | JCSdecl (vi, eo, s) ->
	  begin match s.jc_statement_node with 
	    | JCSblock [] ->
		(* declaration may be created as the result of an
		   intermediate computation. In any case, moving the
		   statements that follow is correct. *)
		[make_decl loc vi eo (make_block loc slnext)]
	    | _ -> 
		(make_decl loc vi eo (link_stat s)) :: slnext
	  end
      | _ -> (link_stat s) :: slnext

  and link_stat s =
    let loc = s.jc_statement_loc in
    let ns =
      match s.jc_statement_node with
	| JCScall (vio, fi, el, s) ->
	    JCScall (vio, fi, el, link_stat s)
	| JCSblock sl ->
	    JCSblock (List.fold_right link_call sl [])
	| JCSassign_var (_, _)
	| JCSassign_heap (_, _, _)
	| JCSassert _ 
	| JCSreturn_void  
	| JCSreturn _ 
	| JCSthrow (_, _)
	| JCSpack (_, _, _)
	| JCSunpack (_, _, _) as node -> node
	| JCSdecl (vi, eo, s) ->
	    JCSdecl (vi, eo, link_stat s)
	| JCSif (e, st, sf) ->
	    JCSif (e, link_stat st, link_stat sf)
	| JCSloop (la, s) ->
	    JCSloop (la, link_stat s)
	| JCStry (s, cl, fs) ->
	    let cl = 
	      List.map (fun (ei, vio, s) -> (ei, vio, link_stat s)) cl in
	    JCStry (link_stat s, cl, link_stat fs)

    in { jc_statement_node = ns;
	 jc_statement_loc = loc }

  in link_stat s

let code_function (spec, sl) =
  (spec, Option_misc.map (List.map statement) sl)

let static_variable (v,e) =
  match e with
    | None -> v,None
    | Some e ->
	let (sl,tl),e = expr e in
	match sl,tl with
	  | [],[] -> v, Some e
	  | _ -> assert false (* TODO *)

(*
let logic_function t =
  match t with 
    | JCTAssertion p -> JCAssertion ertion p) 
    | JCTReads r -> JCReads (List.map location r)
    | JCTTerm t -> JCTerm (term t)
*)

(*
  Local Variables: 
  compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
  End: 
*)
