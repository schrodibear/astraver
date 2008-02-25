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

(* $Id: jc_norm.ml,v 1.83 2008-02-25 07:16:51 moy Exp $ *)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Format
open Jc_region

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

let make_const loc c =
  let t,tr,c = Jc_pervasives.const c in
  let node = JCEconst c in
  { jc_expr_loc = loc; 
    jc_expr_type = t;
    jc_expr_region = tr;
    jc_expr_label = "";
    jc_expr_node = node; }

let void_const loc = make_const loc JCCvoid
let true_const loc = make_const loc (JCCboolean true)
let false_const loc = make_const loc (JCCboolean false)
let one_const loc = make_const loc (JCCinteger "1")

let make_var loc vi =
  let node = JCEvar vi in
  { jc_expr_loc = loc; 
    jc_expr_type = vi.jc_var_info_type;
    jc_expr_region = vi.jc_var_info_region;
    jc_expr_label = "";
    jc_expr_node = node; } 

let make_deref loc e fi =
  let node = JCEderef (e, fi) in
  { jc_expr_loc = loc; 
    jc_expr_type = fi.jc_field_info_type;
    jc_expr_region = Region.make_field e.jc_expr_region fi;
    jc_expr_label = "";
    jc_expr_node = node; }

let rec make_or_list_test loc = function
  | [] -> false_const loc
  | [e] -> e
  | e :: r -> 
      let node = JCEbinary (e, Blor, make_or_list_test loc r) in
      { jc_expr_loc = loc; 
        jc_expr_type = boolean_type;
        jc_expr_region = dummy_region;
	jc_expr_label = "";
	jc_expr_node = node; } 

let rec make_and_list_test loc = function
  | [] -> true_const loc
  | [e] -> e
  | e :: r -> 
      let node = JCEbinary (e, Bland, make_and_list_test loc r) in
      { jc_expr_loc = loc; 
        jc_expr_type = boolean_type;
	jc_expr_region = dummy_region;
	jc_expr_label = "";
	jc_expr_node = node; } 

(* expressions on the typed AST, not the normalized AST *)

let make_tconst loc c =
  let t,tr,c = Jc_pervasives.const c in
  let node = JCTEconst c in
  { jc_texpr_loc = loc; 
    jc_texpr_type = t; 
    jc_texpr_region = tr; 
    jc_texpr_label = "";
    jc_texpr_node = node; }

let make_tincr_local lab loc t op vi =
  let node =  JCTEincr_local (op, vi) in
  { jc_texpr_loc = loc; 
    jc_texpr_type = t; 
    jc_texpr_region = vi.jc_var_info_region; 
    jc_texpr_label = lab;
    jc_texpr_node = node; }

let make_tincr_heap lab loc t op e fi =
  let node = JCTEincr_heap (op, e, fi) in
  { jc_texpr_loc = loc; 
    jc_texpr_type = t; 
    jc_texpr_region = Region.make_field e.jc_texpr_region fi; 
    jc_texpr_label = lab;
    jc_texpr_node = node; }

(* statements *)

let make_node lab loc node = 
(*
  Format.eprintf "Jc_norm.make_node: lab = '%s'@." lab;
*)
  { jc_statement_loc = loc; 
    jc_statement_label = lab;
    jc_statement_node = node; }

let make_assign_var loc vi e =
  make_node "Lassign_var" loc (JCSassign_var (vi, e))

let make_assign_heap loc e1 fi e2 =
  make_node "Lassign_heap" loc (JCSassign_heap (e1, fi, e2))

let make_block loc sl =
  match sl with 
    | [s] -> s
    | s :: l -> 
	make_node s.jc_statement_label s.jc_statement_loc (JCSblock sl)
    | [] -> 
	make_node "Lempty_block" loc (JCSblock sl)
	

let make_block_node lab loc sl snode =
  match sl with
    | [] -> snode
    | _ -> JCSblock (sl @ [make_node lab loc snode])

let make_call lab loc vio f el s =
(*
  Format.eprintf "Jc_norm.make_call: lab for call = '%s'@."
    lab;
*)
  let call = {
    jc_call_fun = f;
    jc_call_args = el;
    jc_call_region_assoc = [];
  } in
  make_node lab loc (JCScall (vio, call, s)) 

let make_if loc e ts es =
  make_node "Lif" loc (JCSif (e,ts,es))

let make_match loc e psl =
  make_node "Lmatch" loc (JCSmatch (e, psl))

let make_throw loc exc e =
  make_node "Lthrow" loc (JCSthrow (exc,e))

let make_loop lab loc la s =
  make_node lab loc (JCSloop (la,s))

let make_try loc s exl fs =
  make_node "Ltry" loc (JCStry (s, exl, fs))

let make_decl loc vi eo s =
  make_node "Ldecl" loc (JCSdecl (vi, eo, s))

let make_decls loc sl tl =
  List.fold_right 
    (fun vi acc -> 
       (* real initial value does not matter *)
       let t, cst =
	 match vi.jc_var_info_type with
	   | JCTnative t ->
	       begin
		 match t with
		   | Tboolean -> boolean_type, JCCboolean false
		   | Tunit -> unit_type, JCCvoid
		   | Tinteger -> integer_type, JCCinteger "0"
		   | Treal -> real_type, JCCreal "0.0"
	       end
	   | JCTenum _ ->  integer_type, JCCinteger "0"
	   | JCTnull | JCTpointer _ -> JCTnull, JCCnull
	   | JCTlogic _ -> assert false
       in
	 make_decl loc vi (Some (make_const loc cst)) acc)
    tl (make_block loc sl)

let make_return loc t e =
  make_node "Lreturn" loc (JCSreturn (t,e))

let make_pack loc si e as_t =
  make_node "Lpack" loc (JCSpack (si, e, as_t))

let make_unpack loc si e from_t =
  make_node "Lunpack" loc (JCSunpack (si, e, from_t))

(* statements on the typed AST, not the normalized AST *)

let make_tnode loc node = 
  { jc_tstatement_loc = loc; jc_tstatement_node = node; }

let make_tif loc e ts es =
  make_tnode loc (JCTSif (e,ts,es))

let make_tblock loc sl =
  match sl with 
    | [s] -> s
    | _ -> make_tnode loc (JCTSblock sl)

let make_tassign_var loc vi e =
  let node = JCTEassign_var(vi, e) in
  let assign = 
    { jc_texpr_loc = loc; 
    jc_texpr_type = unit_type; 
    jc_texpr_region = dummy_region; 
    jc_texpr_label = "";
    jc_texpr_node = node; }
  in
  make_tnode loc (JCTSexpr assign)

let make_tthrow loc exc e =
  make_tnode loc (JCTSthrow (exc,e))

let make_binary lab loc e1 t op e2 =
  let t = match t with
    | JCTenum _ -> integer_type
    | _ -> t
  in
  assert(not(is_pointer_type t));
    { jc_expr_node = JCEbinary(e1, op, e2);
      jc_expr_type = t;
      jc_expr_region = dummy_region;
      jc_expr_label = lab;
      jc_expr_loc = loc }

let make_int_binary lab loc e1 op e2 = make_binary lab loc e1 integer_type op e2


let make_incr_local lab loc op vi =
  make_assign_var loc vi
    (make_int_binary lab loc (make_var loc vi) op (one_const loc))

let make_incr_heap lab loc op e fi = 
  let d =
    { jc_expr_loc = loc;
      jc_expr_type = fi.jc_field_info_type;
      jc_expr_region = Region.make_field e.jc_expr_region fi;
      jc_expr_label = "";
      jc_expr_node = JCEderef(e,fi) ;
    }
  in
  make_assign_heap loc e fi
    (make_int_binary lab loc d op (one_const loc))
  

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
  let lab = e.jc_texpr_label in
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
		    (l1 @ [if_e1_stat], [tmp] @ tl1 @ tl2), JCEvar tmp
	      | Blor ->
		  let tmp = newrefvar boolean_type in
		  let e1_true_stat = make_assign_var loc tmp (true_const loc) in
		  let e2_true_stat = make_assign_var loc tmp (true_const loc) in
		  let false_stat = make_assign_var loc tmp (false_const loc) in
		  let if_e2_stat = make_if loc e2 e2_true_stat false_stat in
		  let block_e2 = make_block loc (l2 @ [if_e2_stat]) in
		  let if_e1_stat = make_if loc e1 e1_true_stat block_e2 in
		    (l1 @ [if_e1_stat], [tmp] @ tl1 @ tl2), JCEvar tmp
	      | _ -> (* Note: no special case for Unot *)
		  (l1 @ l2, tl1 @ tl2), JCEbinary (e1, op, e2)
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
(*
	Format.eprintf "Jc_norm.expr: lab for call = '%s'@." lab;
*)
	let (l, tl), ecall = call lab loc f el ~binder:true ll in
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
    | JCTErange_cast (e,r) ->
	let (l, tl), e = expr e in
	(l, tl), JCErange_cast (e,r)
    | JCTEreal_cast (e,rc) ->
	let (l, tl), e = expr e in
	(l, tl), JCEreal_cast (e,rc)
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
	  make_binary lab loc (make_var loc tmp) vi.jc_var_info_type op e 
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
	  make_binary lab loc 
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
	    ([make_incr_local lab loc (op_of_incdec op) vi], []), JCEvar vi
	| Postfix_inc | Postfix_dec ->
	    let tmp = newrefvar vi.jc_var_info_type in
	    let stat0 = 
	      make_assign_var loc tmp (make_var loc vi) 
	    in
	    ([stat0; make_incr_local lab loc (op_of_incdec op) vi], [tmp]), 
	    JCEvar tmp
	end
    | JCTEincr_heap (op, e, fi) ->
	begin match op with
	| Prefix_inc | Prefix_dec ->
	    let (l, tl), e = expr e in
	    (l@[make_incr_heap lab loc (op_of_incdec op) e fi], tl), 
	    JCEderef (e, fi)
	| Postfix_inc | Postfix_dec ->
	    let (l, tl), e = expr e in
	    let tmp = newrefvar fi.jc_field_info_type in
	    let stat0 = 
	      make_assign_var loc tmp (make_deref loc e fi) 
	    in
	    (l@stat0::[make_incr_heap lab loc Badd_int e fi], tl@[tmp]), 
	    JCEvar tmp
	end
    | JCTEif (e1, e2, e3) ->
	let (l1, tl1), e1 = expr e1 in
	let (l2, tl2), e2 = expr e2 in
	let (l3, tl3), e3 = expr e3 in
	let tmp = newrefvar e.jc_texpr_type in
	let assign2 = make_assign_var loc tmp e2 in
	let assign3 = make_assign_var loc tmp e3 in
	let if_e1_stat = 
	  make_if loc e1 
	    (make_block loc (l2 @ [assign2]))
	    (make_block loc (l3 @ [assign3]))
	in
	  (l1@[if_e1_stat], tl1@tl2@tl3@[tmp]), JCEvar tmp
    | JCTElet(vi,e1,e2) -> 
	let (l1, tl1), e1' = expr e1 in
	let (l2, tl2), e2' = expr e2 in
	vi.jc_var_info_assigned <- true;
	let assign = make_assign_var loc vi e1' in
	(l1@[assign]@l2, tl1@[vi]@tl2), e2'.jc_expr_node
    | JCTEmatch(e1, pel) ->
	let (l1, tl1), e1 = expr e1 in
	let tmp = newrefvar e.jc_texpr_type in
	let pel_tl, psl = List.fold_left
	  (fun (acctl, accpsl) (p, e) ->
	     let (l, tl), e = expr e in
	     let assign = make_assign_var loc tmp e in
	     let block = make_block loc (l@[assign]) in
	     tl@acctl, (p, block)::accpsl)
	  ([], [])
	  (List.rev pel)
	in
	let match_st = make_match loc e1 psl in
	(l1@[match_st], tl1@pel_tl@[tmp]), JCEvar tmp
  in 
(*
  Format.eprintf "Jc_norm.expr: lab for returned expr = '%s'@." lab;
*)
  (sl, tl), 
  { jc_expr_node = ne;
    jc_expr_type = e.jc_texpr_type;
    jc_expr_region = e.jc_texpr_region;
    jc_expr_label = lab;
    jc_expr_loc = loc }
    
and call lab loc f el ~binder ll = 
  if binder then
    let tmp = newvar f.jc_fun_info_result.jc_var_info_type in
    let stat = make_call lab loc (Some tmp) f el (make_block loc []) in
      (* [tmp] will be declared in a post-treatement of the calls generated *)
      ((List.flatten ll)@[stat], []), Some tmp
  else
    let stat = make_call lab loc None f el (make_block loc []) in
      ((List.flatten ll)@[stat], []), None
	
(* [el] is the only part not yet translated *)

and if_statement lab loc f el st sf =
  let ltl, el = List.split (List.map expr el) in
  let ll, tl = List.split ltl in
  let (l, etl), ecall = call lab loc f el ~binder:true ll in
  let ecall = match ecall with
    | Some b -> make_var loc b
    | None -> assert false
  in
  let if_stat = make_if loc ecall st sf in
    make_decls loc (l @ [if_stat]) ((List.flatten tl) @ etl)

and statement s =
  let loc = s.jc_tstatement_loc in
  let lab = ref "" in
  let ns = 
    match s.jc_tstatement_node with
      | JCTSblock sl ->
	  JCSblock [block_statement sl]
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
		  let sl,etl = fst (call e.jc_texpr_label loc 
				      f el ~binder:false ll) in
		  sl, etl @ (List.flatten tl)
	      | JCTEincr_local (op, vi) ->
		  (* avoid creating a useless temporary for postfix version *)
		  let typ = e.jc_texpr_type in
		  let e = make_tincr_local e.jc_texpr_label loc typ (prefix op) vi in
		  fst (expr e)
	      | JCTEincr_heap (op, se, fi) ->
		  (* avoid creating a useless temporary for postfix version *)
		  let typ = e.jc_texpr_type in
		  let e = make_tincr_heap e.jc_texpr_label loc typ (prefix op) se fi in
		  fst (expr e)
	      | _ -> fst (expr e)
	  in
	  (make_decls loc sl tl).jc_statement_node
      | JCTSassert a -> JCSassert a
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
		  (if_statement e.jc_texpr_label loc f el st sf).jc_statement_node
	      | _ -> 
		  let (sl, tl), e = expr e in
		  let if_stat = make_if loc e st sf in
		    (make_decls loc (sl @ [if_stat]) tl).jc_statement_node
	    end
      | JCTSwhile (lab, e, la, body) ->
	  let body = match e.jc_texpr_node with
	    | JCTEconst(JCCboolean true) ->
		(* Special case of an infinite loop [while(true)].
		 * Then, no condition needs to be tested. This form is expected
		 * for some assertions to be recognized as loop invariants
		 * later on, in annotation inference.
		 *)
		let body_stat = statement body in
		let continue_stat = make_throw loc loop_continue None in
		make_block loc [body_stat;continue_stat] 
	    | _ ->
		let exit_stat = make_tthrow loc loop_exit None in
		let if_stat = statement (make_tif loc e body exit_stat) in
		let continue_stat = make_throw loc loop_continue None in
		make_block loc [if_stat;continue_stat] 
	  in
	  let catch_continue = 
	    [(loop_continue, None, make_block loc [])] in
	  let try_continue = 
	    make_try loc body catch_continue (make_block loc []) in
	  let while_stat = make_loop lab loc la try_continue in
	  let catch_exit =
	    [(loop_exit, None, make_block loc [])] in
	  let try_exit = 
	    make_try loc while_stat catch_exit (make_block loc []) in
	  try_exit.jc_statement_node
      | JCTSfor (lab, cond, updates, la, body) ->
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
	  let for_stat = make_loop lab loc la try_continue in
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
      | JCTSbreak { label_info_name = "" } -> 
	  JCSthrow (loop_exit, None)
      | JCTSbreak lab -> assert false (* TODO: see Claude *)
      | JCTScontinue lab -> assert false (* TODO: see Claude *)
      | JCTSgoto lab ->
	  let name_exc = "Goto_" ^ lab.label_info_name in
	  let goto_exc = exception_info None name_exc in
	  Hashtbl.add exceptions_table name_exc goto_exc;
	  JCSthrow (goto_exc, None)
      | JCTSlabel (l,s) -> 
	  lab := l.label_info_name;
	  JCSlabel(l,statement s)
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
	  (* Give a temporary name to the switch expression, so that modifying
	   * a variable on which this expression depends does not interfere 
	   * with the control-flow. 
	   *)
	  let tmp = newvar e.jc_expr_type in
	  let tmpe = make_var loc tmp in
	  let test_one_case ~(neg:bool) c = 
	    (* test for case considered *)
	    let (slc,tlc),c = expr c in
	    assert (slc = [] && tlc = []); 
	    if neg then
	      make_int_binary "" loc tmpe Bneq_int c
	    else
	      make_int_binary "" loc tmpe Beq_int c
	  in
	  let collect_neg_case c = 
	    List.fold_right (fun c l -> match c with
	    | Some c -> test_one_case ~neg:true c :: l
	    | None -> l) c []
	  in
	  (* Collect negative tests for [default] case. *)
	  let all_neg_cases csl = 
	    fst (List.fold_left (fun (l,after_default) (c,_)  -> 
	      if after_default then
		collect_neg_case c @ l,after_default
	      else		
		let has_default = List.exists (fun c -> c = None) c in
		l,has_default
	    ) ([],false) csl)
	  in
	  let test_one_case_or_default = function
	    | Some c -> test_one_case ~neg:false c
	    | None -> make_and_list_test loc (all_neg_cases csl)
	  in
	  let test_case_or_default c = 
	    let el = List.map test_one_case_or_default c in
	    make_or_list_test loc el
	  in
	  let rec cannot_fall_trough s = 
	    match s.jc_statement_node with
	      | JCSblock [] -> 
		  false
	      | JCSblock sl -> 
		  cannot_fall_trough (List.hd (List.rev sl))
	      | JCSthrow _ | JCSreturn_void | JCSreturn _ | JCSloop _ -> 
		  true
	      | JCSif(_,st,sf) ->
		  cannot_fall_trough st && cannot_fall_trough sf
	      | _ -> false
	  in
	  let rec fold_case (previous_c,statl) = 
	    function [] -> List.rev statl | (c,sl) :: next_cases ->
	      (* statement list in case considered *)
	      let block_stat = block_statement sl in
	      let has_default = List.exists (fun c -> c = None) c in
	      let current_c = if has_default then c else previous_c @ c in
	      let etest = test_case_or_default current_c in
	      (* case translated into if-statement *)
	      if cannot_fall_trough block_stat then
		let next_statl = fold_case ([],[]) next_cases in
		let next_block = make_block loc next_statl in
		let if_stat = make_if loc etest block_stat next_block in
		List.rev (if_stat :: statl)
	      else
		let empty_block = make_block loc [] in
		let if_stat = make_if loc etest block_stat empty_block in
		fold_case (current_c, if_stat :: statl) next_cases
	  in
	  let ncsl = fold_case ([],[]) csl in
	  let dummy_throw = make_throw loc loop_exit None in
	  let switch_stat = make_block loc (ncsl @ [dummy_throw]) in
	  let catch_exit =
	    [(loop_exit, None, make_block loc [])] in
	  let try_exit = 
	    make_try loc switch_stat catch_exit (make_block loc []) in
	  let tmp_assign = make_decl loc tmp (Some e) (make_block loc []) in
	  (make_decls loc (sl @ [tmp_assign;try_exit]) tl).jc_statement_node
      | JCTSmatch (e, psl) ->
	  let (sl, tl), e = expr e in
	  let psl = List.map (fun (p, sl) -> p, block_statement sl) psl in
	  let match_node = make_match loc e psl in
	  (make_decls loc (sl @ [match_node]) tl).jc_statement_node

  in { jc_statement_node = ns;
       jc_statement_label = !lab;
       jc_statement_loc = loc }

and block_statement statements =
  let add_var_decl v (f,l,vs) = (f,l,VarSet.add v vs) in
  let rec block = function
    | [] -> [],[],VarSet.empty
    | s :: bl ->
	match s.jc_tstatement_node with
	  | JCTSlabel(lab,st) ->
	      let loc = s.jc_tstatement_loc in
	      let (be,bl,vs) = block (st::bl) in
	      let be = 
		VarSet.fold (fun vi s -> 
		  make_decl s.jc_statement_loc vi None s) vs (make_block loc be)
	      in
	      let name_exc = "Goto_" ^ lab.label_info_name in
	      let goto_exc = exception_info None name_exc in
	      Hashtbl.add exceptions_table name_exc goto_exc;
	      [make_throw loc goto_exc None],
	      (goto_exc,be)::bl,
	      VarSet.empty
	  | JCTSdecl(vi,None,s) ->
	      let b = match s.jc_tstatement_node with
		| JCTSblock sl -> block (sl @ bl)
		| _ -> block (s :: bl)
	      in
	      add_var_decl vi b
	  | JCTSdecl(vi,Some e,s) ->
	      let set = make_tassign_var s.jc_tstatement_loc vi e in
	      vi.jc_var_info_assigned <- true;
	      let b = match s.jc_tstatement_node with
		| JCTSblock sl -> block (set :: sl @ bl)
		| _ -> block (set :: s :: bl)
	      in
	      add_var_decl vi b
	  | JCTSblock sl ->
	      block (sl @ bl)
	  | _ ->
	      let append_block e (f,l,vs) = (e :: f,l,vs) in
	      append_block (statement s) (block bl)
  in
  let be,bl,vs = block statements in
  let s = 
    List.fold_left 
      (fun acc (goto_exc,s) ->
	let loc = s.jc_statement_loc in
	let catch_goto =
	  [(goto_exc, None, make_block loc [])] in
	make_try loc acc catch_goto (make_block loc [])
      ) (make_block Loc.dummy_position be) bl
  in
  let s = 
    VarSet.fold (fun vi s -> make_decl s.jc_statement_loc vi None s) vs s
  in
  match s.jc_statement_node with
    | JCSblock [s] -> s
    | _ -> s


let statement s =

  let rec link_call s slnext =
    let loc = s.jc_statement_loc in
    match s.jc_statement_node with
      | JCScall (Some vi, call, s') -> 
	  begin match s'.jc_statement_node with 
	    | JCSblock [] ->
		(* call may be created as the result of an
		   intermediate computation. In any case, moving the
		   statements that follow is correct. *)
(*
		Format.eprintf "Jc_interp.link_call(1): lab for call = '%s'@."
		  s.jc_statement_label;
*)
		[make_call s.jc_statement_label loc (Some vi) 
		   call.jc_call_fun call.jc_call_args (make_block loc slnext)]
	    | _ -> 
(*
		Format.eprintf "Jc_interp.link_call(2): lab for call = '%s'@."
		  s.jc_statement_label;
*)
		(make_call s.jc_statement_label loc (Some vi) 
		  call.jc_call_fun call.jc_call_args (link_stat s')) :: slnext
	  end
      | JCSdecl (vi, eo, s') ->
	  begin match s'.jc_statement_node with 
	    | JCSblock [] ->
		(* declaration may be created as the result of an
		   intermediate computation. In any case, moving the
		   statements that follow is correct. *)
		[make_decl loc vi eo (make_block loc slnext)]
	    | _ -> 
		(make_decl loc vi eo (link_stat s')) :: slnext
	  end
      | _ -> (link_stat s) :: slnext

  and link_stat s =
    let loc = s.jc_statement_loc in
    let ns =
      match s.jc_statement_node with
	| JCScall (vio, call, s) ->
	    JCScall (vio, call, link_stat s)
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
	| JCSlabel(lab,s) ->
	    JCSlabel(lab,link_stat s)
	| JCStry (s, cl, fs) ->
	    let cl = 
	      List.map (fun (ei, vio, s) -> (ei, vio, link_stat s)) cl in
	    JCStry (link_stat s, cl, link_stat fs)
	| JCSmatch (e, psl) ->
	    JCSmatch (e, List.map (fun (p, s) -> p, link_stat s) psl)

    in { jc_statement_node = ns;
	 jc_statement_label = s.jc_statement_label;
	 jc_statement_loc = loc }

  in link_stat (statement s)


let rec invariant_for_struct this si =
  let (_, invs) = 
    Hashtbl.find Jc_typing.structs_table si.jc_struct_info_name 
  in
  let invs = make_and
    (List.map 
       (fun (li, _) -> 
	  let a = { jc_app_fun = li;
		    jc_app_args = [this];
		    jc_app_label_assoc = [];
		    jc_app_region_assoc = [] }
	  in
	  raw_asrt (JCAapp a)) invs) 
  in
    match si.jc_struct_info_parent with
      | None -> invs
      | Some si -> (* add invariants from the type hierarchy *)
	  let this =
	    match this.jc_term_type with
	      | JCTpointer (_, a, b) ->
		  { this with jc_term_type = JCTpointer (JCtag si, a, b) }
	      | _ -> assert false (* never happen *)
	  in
	    make_and [invs; (invariant_for_struct this si)]


let code_function (fi, fs, sl) vil =
  begin
    match !Jc_common_options.inv_sem with
      | InvArguments ->
	  (* apply arguments invariant policy *)
	  let invariants =
	    (* Calculate global invariants. *)
	    let vitl = 
	      List.map 
		(fun vi -> term_no_loc (JCTvar vi) 
		   vi.jc_var_info_type) vil 
	    in
	    let global_invariants =
	      Hashtbl.fold
		(fun li _ acc -> 
		   li.jc_logic_info_parameters <- vil;
		   let a = { jc_app_fun = li;
			     jc_app_args = vitl;
			     jc_app_label_assoc = [];
			     jc_app_region_assoc = [] }
		   in
		     (raw_asrt (JCAapp a)) :: acc)
		Jc_typing.global_invariants_table []
	    in
	    let global_invariants = make_and global_invariants in
	      (* Calculate invariants for each parameter. *)
	    let invariants =
	      List.fold_left
		(fun acc vi ->
		   match vi.jc_var_info_type with
		     | JCTpointer (JCtag st, _, _) ->
			 make_and 
			   [acc; (invariant_for_struct 
				    (term_no_loc (JCTvar vi) vi.jc_var_info_type) st)]
		     | _ -> acc)
		(raw_asrt JCAtrue)
		fi.jc_fun_info_parameters
	    in
	      make_and [global_invariants; invariants]
	  in
	    (* add invariants to the function precondition *)
	    fs.jc_fun_requires <- make_and [fs.jc_fun_requires; invariants];
	    (* add invariants to the function postcondition *)
	    if is_purely_exceptional_fun fs then () else
	      let safety_exists = ref false in
	      let post = invariants in
		List.iter
		  (fun (_, s, b) ->
		     if s = "safety" then safety_exists := true;
		     b.jc_behavior_ensures <- make_and [b.jc_behavior_ensures; post])
		  fs.jc_fun_behavior;
		(* add the 'safety' spec if it does not exist (e.g. from Krakatoa) *)
		if not !safety_exists then 
		  let safety_b = { default_behavior with jc_behavior_ensures = post } in
		    fs.jc_fun_behavior <- 
		      (Loc.dummy_position, "safety", safety_b) :: fs.jc_fun_behavior;
      | _ -> ()
  end;
    (* normalization of the function body *)
  let bs = Option_misc.map (make_tblock Loc.dummy_position) sl in
(*   begin match bs with None -> ()  *)
(*     | Some bs -> Format.printf "%a@." Jc_output.statement bs  *)
(*   end; *)
  (fs, Option_misc.map (fun bs -> [statement bs]) bs)
    
let static_variable (vi, eo) =
  match eo with
    | None -> vi, None
    | Some e ->
	let (sl, tl), e = expr e in
	  match sl, tl with
	    | [], [] -> vi, Some e
	    | _ -> assert false (* TODO *)
		  
		  
(*
  Local Variables: 
  compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
  End: 
*)
