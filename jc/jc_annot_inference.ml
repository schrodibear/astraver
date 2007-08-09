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

(*

open Apron
open Format
open Jc_ast
open Jc_env
open Jc_fenv
open Jc_options
open Jc_pervasives
open Coeff
open Interval
open Lincons1


(*

  usage: jessie -ai [other_options] f 
  
  ai behaviour with other jessie options:
  
  -v prints inferred annotations
  -d prints awful debug info
 
 *)
  

let terms_vars_table = Hashtbl.create 97

let calls_changed = ref false;;


let make_term loc node t = 
  { jc_term_node = node; jc_term_type = t; jc_term_loc = loc }
;;

let make_term_no_loc node t = 
  { jc_term_node = node; jc_term_type = t; jc_term_loc = Loc.dummy_position }
;;


let make_assertion loc node =
  { jc_assertion_node = node; jc_assertion_loc = loc }
;;

let make_assertion_no_loc node =
  { jc_assertion_node = node; jc_assertion_loc = Loc.dummy_position }
;;


let make_and loc al =
  let al =
    List.filter
      (fun a -> a.jc_assertion_node <> JCAtrue)
      al
  in
  make_assertion loc (JCAand al)
;;


let term_of_coeff c =
  match c with
  | Scalar scalar -> 
      let s = Scalar.to_string scalar in
      s, make_term_no_loc (JCTconst (JCCinteger s)) (JCTnative Tinteger)
  | Interval i ->
      assert false (* TODO ? *)
;;

let term_of_lincons1 lincons =
  let vl = Array.to_list (fst (Environment.vars lincons.env)) in
  let c = Lincons1.get_cst lincons in
  let s, t = term_of_coeff c in
  let t =
    List.fold_left
      (fun acc v ->
	let s, c = term_of_coeff (Lincons1.get_coeff lincons v) in
	try
	  let t = Hashtbl.find terms_vars_table v in
	  let t = 
	    match s with 
	    | "0." -> None
	    | "1" -> Some t
	    | "-1" -> 
		Some 
		  (make_term_no_loc 
		     (JCTunary (Uminus_int, t)) 
		     (JCTnative Tinteger))
	    | _ -> 
		Some 
		  (make_term_no_loc 
		     (JCTbinary (c, Bmul_int, t)) 
		     (JCTnative Tinteger))
	  in
	  match acc, t with
	  | _, None -> acc
	  | None, _ -> t
	  | Some acc, Some t -> 
	      Some
		(make_term_no_loc 
		   (JCTbinary (t, Badd_int, acc)) 
		   (JCTnative Tinteger))
	with Not_found ->
	  assert false (* should never happen *))
      (if s = "0" then None else Some t)
      vl
  in
  match t with 
  | None -> assert false (* should never happen *)
  | Some t -> t
;;

let bin_op_and_rvalue_of_lincons1 lincons =
  match (Lincons1.get_typ lincons) with
  | EQ -> Beq_int, JCCinteger "0"
  | SUPEQ -> Bge_int, JCCinteger "0"
  | SUP -> Bgt_int, JCCinteger "0"
  | DISEQ -> Bneq_int, JCCinteger "0"
  | EQMOD scalar -> Bmod_int, JCCinteger (Scalar.to_string scalar)
;;

let absvalue_to_assertion man loc env a =
  if debug then printf "absvalue_to_assertion...@.";
  let lincons = Abstract1.to_lincons_array man a in
  let lincons1l = 
    List.fold_left
      (fun acc lincons0 -> ({ lincons0 = lincons0; env = lincons.array_env })::acc)
      []
      (Array.to_list lincons.lincons0_array)
  in
  let al = 
    List.map
      (fun lincons ->
	let t1 = term_of_lincons1 lincons in
	let op, t2 = bin_op_and_rvalue_of_lincons1 lincons in
	make_assertion_no_loc 
	  (JCArelation (t1, op, 
			(make_term_no_loc 
			   (JCTconst t2)
			   (JCTnative Tinteger)))))
      lincons1l
  in
  make_assertion_no_loc (JCAand al)
;;


let abstract_vars_of_vi vi =
  match vi.jc_var_info_type with
  | JCTnative nt ->
      begin
        match nt with
        | Tunit ->
	    []
	| Tboolean | Tinteger -> 
	    let v = Var.of_string vi.jc_var_info_name in
	    Hashtbl.add terms_vars_table
	      v (make_term_no_loc (JCTvar vi) vi.jc_var_info_type);
	    [v]
	| Treal ->
	    []
      end
  | JCTlogic _ -> assert false (* should never happen *)
  | JCTenum ei ->
      let v = Var.of_string vi.jc_var_info_name in
      Hashtbl.add terms_vars_table
	v (make_term_no_loc (JCTvar vi) vi.jc_var_info_type);
      (* TODO: restrict v to the intervalle [min; max] *)
      [v]
  | JCTpointer (si, n1, n2) ->
      let s = vi.jc_var_info_name in
      let v1 = Var.of_string (s ^ "_offset_min") in
      let t1 = 
	make_term_no_loc 
	  (JCToffset (Offset_min, 
		      make_term_no_loc (JCTvar vi) vi.jc_var_info_type, 
		      si))
	  (JCTnative Tinteger) 
      in
      Hashtbl.add terms_vars_table v1 t1;
      let v2 = Var.of_string (s ^ "_offset_max") in
      let t2 = 
	make_term_no_loc 
	  (JCToffset (Offset_max, 
		      make_term_no_loc (JCTvar vi) vi.jc_var_info_type,
		      si))
	  (JCTnative Tinteger) 
      in	       
      Hashtbl.add terms_vars_table v2 t2;
      [v1; v2]
  | JCTnull -> assert false (* should never happen *)
;;

let fresh_variable man env pre vi =
  (* create a new variable *)
  let v = Var.of_string vi.jc_var_info_name in
  Hashtbl.add terms_vars_table v
    (make_term_no_loc (JCTvar vi) vi.jc_var_info_type);
  (* add the variable to env *)
  try
    (env, pre)
  with Failure _ ->
    assert false (* should never happen *)
;;


let rec not_expr e =
  if debug then printf "not_expr...@.";
  let expr_node = 
    match e.jc_expr_node with
    | JCEconst c ->
	if debug then printf "  JCEconst...@.";
	begin
	  match c with
          | JCCvoid -> assert false (* TODO ? *)
          | JCCnull -> assert false (* TODO ? *)
          | JCCboolean b -> JCEunary (Unot, e)
          | JCCinteger s -> assert false (* TODO ? *)
          | JCCreal s -> assert false (* TODO ? *)
	end
    | JCEvar vi ->
	if debug then printf "  JCEvar...@.";
	begin
	  match vi.jc_var_info_type with
	  | JCTnative nt ->
	      begin
		match nt with 
		| Tunit -> assert false (* TODO *)
		| Tboolean -> JCEunary (Unot, e)
		| Tinteger -> assert false (* TODO *)
		| Treal -> assert false (* TODO *)
	      end
	  | JCTlogic s -> assert false (* TODO *)
	  | JCTenum ei -> assert false (* TODO *)
	  | JCTpointer (si, n1, n2) -> assert false (* TODO *)
	  | JCTnull -> assert false (* TODO *)
	end
    | JCEbinary (e1, bop, e2) ->
	if debug then printf "  JCEbinary...@.";
	begin
	  match bop with
	  | Blt_int -> JCEbinary (e1, Bge_int, e2)
	  | Bgt_int -> JCEbinary (e1, Ble_int, e2)
	  | Ble_int -> JCEbinary (e1, Bgt_int, e2)
	  | Bge_int -> JCEbinary (e1, Blt_int, e2)
	  | Beq_int -> (* fails because != not supported by apron0.9.6 *)
	      JCEbinary (e1, Bneq_int, e2) 
	  | Bneq_int -> assert false (* TO DO *)
	  | Blt_real -> assert false (* TO DO *)
	  | Bgt_real -> assert false (* TO DO *)
	  | Ble_real -> assert false (* TO DO *)
	  | Bge_real -> assert false (* TO DO *)
	  | Beq_real -> assert false (* TO DO *)
	  | Bneq_real -> assert false (* TO DO *)
	  | Badd_int -> assert false (* TO DO *)
	  | Bsub_int -> assert false (* TO DO *)
	  | Bmul_int -> assert false (* TO DO *)
	  | Bdiv_int -> assert false (* TO DO *)
	  | Bmod_int -> assert false (* TO DO *)
	  | Badd_real -> assert false (* TO DO *)
	  | Bsub_real -> assert false (* TO DO *)
	  | Bmul_real -> assert false (* TO DO *)
	  | Bdiv_real -> assert false (* TO DO *)
	  | Bland -> assert false (* TO DO *)
	  | Blor -> assert false (* TO DO *)
	  | Bimplies -> assert false (* TO DO *)
	  | Biff -> assert false (* TO DO *)
	  | Beq_pointer -> assert false (* TO DO *)
	  | Bneq_pointer -> assert false (* TO DO *)
	  | Bbw_and -> assert false (* TO DO *)
	  | Bbw_or -> assert false (* TO DO *)
	  | Bbw_xor -> assert false (* TO DO *)
	  | Bshift_left -> assert false (* TO DO *)
	  | Bshift_right -> assert false (* TO DO *)
	end
    | JCEunary (uop, e) -> assert false (* TO DO *)
    | JCEshift (e1, e2) -> assert false (* TO DO *)
    | JCEderef _ ->
	if debug then printf "  JCEderef...@.";
	JCEunary (Unot, e)
    | JCEinstanceof _ ->
	if debug then printf "  JCEinstanceof...@.";
	JCEunary (Unot, e)
    | JCEcast (e, si) -> assert false (* TO DO *)
    | JCErange_cast (ei, e) -> assert false (* TO DO *)
    | JCEif (e1, e2, e3) -> assert false (* TO DO *)
    | JCEoffset (ok, e, si) -> assert false (* TO DO *)
    | JCEalloc (e1, si) -> assert false (* TO DO *)
    | JCEfree e -> assert false (* TO DO *)
  in
  { e with jc_expr_node = expr_node }
;;


let rec expr man env pre e =
  if debug then printf "expr...@.";
  match e.jc_expr_node with
  | JCEconst c ->
      if debug then printf "  JCEconst...@.";
      begin
	match c with
        | JCCvoid -> assert false (* TODO ? *)
        | JCCnull -> env, pre, ["0"; "-1"]
        | JCCboolean b -> env, pre, [if b then "1" else "0"]
        | JCCinteger s -> env, pre, [s]
        | JCCreal _ -> env, pre, []
      end
  | JCEvar vi -> 
      if debug then printf "  JCEvar...@.";
      begin
	match vi.jc_var_info_type with
	| JCTnative nt ->
	    begin
	      match nt with
	      | Tunit -> assert false (* should never happen *)
	      | Tboolean -> env, pre, [vi.jc_var_info_name ^ " = 1"]
	      | Tinteger -> env, pre, [vi.jc_var_info_name]
	      | Treal -> assert false (* TODO *)
	    end
	| JCTlogic _ -> assert false (* should never happen *)
	| JCTenum ei ->
	    env, pre, [vi.jc_var_info_name]
	| JCTpointer (si, n1, n2) -> 
	    env, pre, [Num.string_of_num n1; Num.string_of_num n2]
	| JCTnull -> assert false (* should never happen *)
      end
  | JCEbinary (e1, bop, e2) ->
      if debug then printf "  JCEbinary...@.";
      let env, pre, e1 = expr man env pre e1 in
      if e1 = [] then env, pre, [] else 
      let env, pre, e2 = expr man env pre e2 in
      if e2 = [] then env, pre, [] else
      begin
	match bop with
	| Blt_int | Blt_real -> 
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "<" ^ e2) e1 e2
	| Bgt_int | Bgt_real -> 
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ ">" ^ e2) e1 e2
	| Ble_int | Ble_real -> 
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "<=" ^ e2) e1 e2
	| Bge_int | Bge_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ ">=" ^ e2) e1 e2
	| Beq_int | Beq_real | Beq_pointer ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "=" ^ e2) e1 e2
	| Bneq_int | Bneq_real | Bneq_pointer ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "!=" ^ e2) e1 e2
	| Badd_int | Badd_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "+" ^ e2) e1 e2
	| Bsub_int | Bsub_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "-" ^ e2) e1 e2
	| Bmul_int | Bmul_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "*" ^ e2) e1 e2
	| Bdiv_int ->
	    env, pre, List.map2 (fun e1 e2 -> "1/" ^ e2 ^ "*" ^ e1) e1 e2
	| Bdiv_real -> assert false (* TODO ? *)
	| Bmod_int -> assert false (* TODO ? *)
	| Bland | Blor -> assert false (* should never happen *)
	| Bimplies -> assert false (* should never happen *)
	| Biff -> assert false (* should never happen *)
	| Bbw_and -> assert false (* TODO ? *)
	| Bbw_or -> assert false (* TODO *)
	| Bbw_xor -> assert false (* TODO *)
	| Bshift_left -> assert false (* TODO *)
	| Bshift_right -> assert false (* TODO *)
      end
  | JCEunary (uop, e) ->
      if debug then printf "  JCEunary...@.";
      let env, pre, strl = expr man env pre e in
      begin
	match uop with
	| Uplus_int -> assert false (* TODO ? *)
	| Uminus_int -> assert false (* TODO ? *)
	| Uplus_real -> assert false (* TODO ? *)
	| Uminus_real -> assert false (* TODO ? *)
	| Unot ->
	    begin
	      match e.jc_expr_node with
	      | JCEvar vi -> env, pre, [vi.jc_var_info_name ^ "= 0"]
	      | _ ->
		  let strl = 
		    List.map 
		      (fun str -> 
			if str = "0" then "1" else
			if str = "1" then "0" else
			str ^ "= 0")
		      strl
		  in
		  env, pre, strl
	    end
	| Ubw_not -> assert false (* TODO ? *)
      end
  | JCEshift (e1, e2) ->
      if debug then printf "  JCEshift...@.";
      env, pre, []
  | JCEderef (e, fi) ->
      if debug then printf "  JCEderef...@.";
      env, pre, []
  | JCEinstanceof (e, si) ->
      env, pre, []
  | JCEcast (e, si) ->
      if debug then printf "  JCEcast...@.";
      let env, pre, strl = expr man env pre e in
      env, pre, strl
  | JCErange_cast (ei, e) -> assert false (* TO DO *)
  | JCEif (e1, e2, e3) -> assert false (* TO DO *)
  | JCEoffset (ok, e, si) ->
      if debug then printf "  JCEoffset...@.";
      let s =
	match e.jc_expr_node with
	| JCEconst c -> assert false (* TO DO *)
	| JCEvar vi -> 
	    begin
	      match ok with
	      | Offset_max -> vi.jc_var_info_name ^ "_offset_max"
	      | Offset_min -> vi.jc_var_info_name ^ "_offset_min"
	    end
	| JCEbinary (e1, op, e2) -> assert false (* TO DO *)
	| JCEunary (op, e) -> assert false (* TO DO *)
	| JCEshift (e1, e2) -> assert false (* TO DO *)
	| JCEderef (e, fi) -> assert false (* TO DO *)
	| JCEinstanceof (e, si) -> assert false (* TO DO *)
	| JCEcast (e, si) -> assert false (* TO DO *)
	| JCErange_cast (ei, e) -> assert false (* TO DO *)
	| JCEif (e1, e2, e3) -> assert false (* TO DO *)
	| JCEoffset (ok, e, si) -> assert false (* TO DO *)
	| JCEalloc (e, si) -> assert false (* TO DO *)
	| JCEfree e -> assert false (* TO DO *)
      in
      env, pre, [s]
  | JCEalloc (e, si) ->
      if debug then printf "  JCEalloc...@.";
      (* TODO: understand how to handle e *)
      (* let env, pre, s = expr man env pre e1 in *)
      env, pre, ["0" ; "0"] (* values of \offset_min and \offset_max ? *)
  | JCEfree (e) -> assert false (* TODO ? *)
;;


let rec loop_condition man pre e sb se la fil =
  (* make the constraint from the loop condition *)
  let pre = Abstract1.join man (Abstract1.bottom man (Abstract1.env pre)) pre in (* Useless ? *)
  let env, pre, strl = expr man (Abstract1.env pre) pre e in
  let absvalue =
    (* TODO: special case of *while(false)* *)
    (* special case of *while(true)* *)
    if List.length strl = 1 && List.hd strl = "1" then
      Abstract1.top man env
    else
      let lincons = Parser.lincons1_of_lstring env strl in
      Abstract1.of_lincons_array man env lincons
  in
  if debug then printf "loop condition: %a@." Abstract1.print absvalue;
  let pre = Abstract1.meet man pre absvalue in
  let sb, body, _ = statement man pre true None fil sb in
  (* compute loop invariant *)
  let body = Abstract1.change_environment man body (Abstract1.env pre) false in
  let loop_inv = Abstract1.widening man pre body in
  if debug then printf "after widening: %a@." Abstract1.print loop_inv;
  (* update env in absvalue *)
  let loop_inv = 
    Abstract1.change_environment man loop_inv (Abstract1.env absvalue) false
  in
  let loop_inv = Abstract1.meet man loop_inv absvalue in
  if debug then printf "2nd loop_condition: %a@." Abstract1.print loop_inv;
  let sb, body, _ = statement man loop_inv false None fil sb in
  let body = Abstract1.change_environment man body (Abstract1.env pre) false in
  let loop_inv = Abstract1.join man pre body in
  if verbose then printf "    inferred loop invariant: %a@." Abstract1.print loop_inv;
  let loop_invariant = la.jc_loop_invariant in
  let inferred_loop_inv = 
    absvalue_to_assertion man (loop_invariant.jc_assertion_loc) (Abstract1.env loop_inv) loop_inv
  in
  let la = 
    { la with 
      jc_loop_invariant = make_and 
	(loop_invariant.jc_assertion_loc)
	[loop_invariant; inferred_loop_inv] }
  in
  let env, pre, strl = expr man env pre (not_expr e) in
  let absvalue = 
    (* special case of *while(true)* exit *)
    if List.length strl = 1 && List.hd strl = "0" then
      Abstract1.bottom man env
    (* TODO: special case of *while(false)* exit *)
    else
    let lincons = Parser.lincons1_of_lstring (Abstract1.env pre) strl in
    Abstract1.of_lincons_array man (Abstract1.env pre) lincons
  in
  let post = Abstract1.meet man loop_inv absvalue in
  JCSif (e, sb, se), post, Some la

and statement man pre fv lao fil s =
  if debug then printf "statement ...@.";
  let jc_statement_node, post, lao =
    match s.jc_statement_node with
    | JCScall (vio, fi, el, s) ->
        if debug then printf "  JCScall ...@.";
	let fi =
	  if List.mem fi fil then
	    begin
	      let new_params =
		List.map2
		  (fun vi e ->
		    match vi.jc_var_info_type with
		    | JCTnative _ -> vi (* TODO ? *)
		    | JCTlogic _ -> assert false (* should never happen *)
		    | JCTenum _ -> vi (* TODO ? *)
		    | JCTpointer (si, n1, n2) ->
			if Num.le_num n1 n2 then
			  begin
			    match e.jc_expr_node with
			    | JCEconst c ->
				begin
				  match c with
				  | JCCvoid -> vi (* TODO ? *)
				  | JCCnull ->
				      calls_changed := true;
				      { vi with jc_var_info_type = JCTpointer (si, Num.Int 0, Num.Int (-1)) }
				  | JCCboolean _ -> vi (* TODO ? *)
				  | JCCinteger _ -> vi (* TODO ? *)
				  | JCCreal _ -> vi (* TODO ? *)
				end
			    | JCEvar vi ->
				let v = 
				  Hashtbl.fold
				    (fun v t acc ->
				      match t.jc_term_node with
				      | JCTvar vi' ->
					  if vi'.jc_var_info_name = vi.jc_var_info_name then
					    v
					  else
					    acc
				      | _ -> acc)
				    terms_vars_table
				    (Var.of_string "")
				in
				let interval = Abstract1.bound_variable man pre v in
				let inf = Num.num_of_string (Scalar.to_string interval.inf) in
				let sup = Num.num_of_string (Scalar.to_string interval.sup) in
				let n1 = Num.min_num n1 inf in
				let n2 = Num.min_num n2 sup in
				calls_changed := true;
				{ vi with jc_var_info_type = JCTpointer (si, n1, n2) }
			  | JCEbinary (e1, bop, e2) -> vi (* TODO ? *)
			  | JCEunary (uop, e) -> vi (* TODO ? *)
			  | JCEshift (e1, e2) -> vi (* TODO ? *)
			  | JCEderef (e, fi) -> vi (* TODO ? *)
			  | JCEinstanceof (e, si) -> vi (* TODO ? *)
			  | JCEcast (e, si) -> vi (* TODO ? *)
			  | JCErange_cast (ei, e) -> vi (* TODO ? *)
			  | JCEif (e1, e2, e3) -> vi (* TODO ? *)
			  | JCEoffset (ok, e, si) -> vi (* TODO ? *)
			  | JCEalloc (e, si) -> vi (* TODO ? *)
			  | JCEfree e -> vi (* TODO ? *)			
			end
		      else
			(* the type is the more general => nothing to be done *)
			vi
		    | JCTnull -> vi (* TODO ? *))
		  fi.jc_fun_info_parameters
		  el
	      in
	      { fi with jc_fun_info_parameters = new_params }
	    end
	  else
	    fi
	in
	let (_, fs, bo) = Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag in
	Hashtbl.replace Jc_norm.functions_table fi.jc_fun_info_tag (fi, fs, bo);
        begin
          match vio with
          | None -> 
	      (* TODO: add the post of f if any + 
		 check the parameters and store the info *)
	      JCScall (None, fi, el, s), pre, lao
          | Some vi -> 
              begin
		match fi.jc_fun_info_name with
		| "shift" -> 
                    (* cases to distinguish parameters ? *)
                    (* just add the fresh variable to env *)
                    let env, pre = 
		      if fv then fresh_variable man (Abstract1.env pre) pre vi 
		      else (Abstract1.env pre), pre
		    in
                    let s, post, lao = statement man pre fv lao fil s in
                    JCScall (vio, fi, el, s), post, lao
		| _ -> (* TODO?: add the post of fi to pre *)
		    JCScall (vio, fi, el, s), pre, lao
              end
        end
    | JCSassign_var (vi, e) ->
	if debug then printf "  JCSassign_var ...%s@." vi.jc_var_info_name;
	let env, pre, strl = expr man (Abstract1.env pre) pre e in
	if strl = [] then JCSassign_var (vi, e), pre, lao else
	let vl = abstract_vars_of_vi vi in
	let linexprl = 
	  List.map 
	    (Parser.linexpr1_of_string (Abstract1.env pre))
	    strl
	in
	let post = 
	  Abstract1.assign_linexpr_array man pre 
	    (Array.of_list vl)
	    (Array.of_list linexprl) 
	    None
	in
	JCSassign_var (vi, e), post, lao
    | JCSassign_heap (e1, fi, e2) ->
	if debug then printf "  JCSassign_heap ...@.";
	JCSassign_heap(e1, fi, e2), pre, lao
    | JCSassert (so, a) ->
	(* TODO ? : add assertion *a* to pre *)
	JCSassert (so, a), pre, lao
    | JCSblock sl ->
	if debug then printf "  JCSblock ...@.";
	let sl, post, lao =
          List.fold_left
            (fun (sl, pre, lao) s ->
              let s, post, lao = statement man pre fv lao fil s in
              (List.rev (s::(List.rev sl)), post, lao) ) 
            ([], pre, lao) 
            sl
	in
	JCSblock sl, post, lao
    | JCSdecl (vi, eo, s) ->
	if debug then printf "  JCSdecl ...@.";
	let vl = abstract_vars_of_vi vi in
	let env = Environment.add (Abstract1.env pre) (Array.of_list vl) [||] in 
	let pre = Abstract1.change_environment man pre env false in
        begin
          match eo with
          | None ->
              let s, post, lao = statement man pre fv lao fil s in
              (* TO DO ? : update env in pre *)
              JCSdecl (vi, eo, s), post, lao
          | Some e ->
	      let env, pre, strl = expr man env pre e in
	      if strl = [] then JCSdecl (vi, eo, s), pre, lao else
	      let linexprl =
		List.map
		  (Parser.linexpr1_of_string env)
		  strl
	      in
	      let post = 
		Abstract1.assign_linexpr_array man pre
		  (Array.of_list vl) 
		  (Array.of_list linexprl) 
		  None
	      in
 (*             let post = Abstract1.meet_lincons_array man pre lincons in *)
              let s, post, lao = statement man post fv lao fil s in
              JCSdecl (vi, eo, s), post, lao
        end;
    | JCSif (e, s1, s2) ->
        if debug then printf "  JCSif ...@.";
	begin
	  match lao with
	  | None -> (* a 'true' *if* *)
	      (* Step 1: if branch *)
	      let env, pre, strl = expr man (Abstract1.env pre) pre e in
	      let lincons = Parser.lincons1_of_lstring env strl in
	      let absvalue = Abstract1.of_lincons_array man env lincons in
	      if debug then printf "if condition: %a@." Abstract1.print absvalue;
	      let if_pre = Abstract1.meet man pre absvalue in
	      let s1, post1, lao = statement man if_pre fv lao fil s1 in
	      (* Step 2: else branch *)
	      let env, pre, strl = expr man (Abstract1.env pre) pre (not_expr e) in
	      let lincons = Parser.lincons1_of_lstring env strl in
	      let absvalue = Abstract1.of_lincons_array man env lincons in
	      if debug then printf "else condition: %a@." Abstract1.print absvalue;
	      let else_pre = Abstract1.meet man pre absvalue in
	      let s2, post2, lao = statement man else_pre fv lao fil s2 in
	      (* Step 3: join the two branches *)
	      Abstract1.change_environment_with man post1 (Abstract1.env pre) false;
	      Abstract1.change_environment_with man post2 (Abstract1.env pre) false;
	      let post = Abstract1.join man post1 post2 in
	      JCSif (e, s1, s2), post, lao
	  | Some la -> (* the *if* is actually a *loop condition* *)
	      if debug then printf "   the if is a loop_condition @.";
	      loop_condition man pre e s1 s2 la fil
	end
    | JCSloop (la, s) ->
        if debug then printf "  JCSloop ...@.";
	let s, post, la = 
	  let s, post, lao = statement man pre fv (Some la) fil s in
	  s, post, 
	  match lao with 
	  | None -> assert false (* should never happen *) 
	  | Some la -> la
	in
	JCSloop (la, s), post, lao
    | JCSreturn_void ->
	JCSreturn_void, pre, lao
    | JCSreturn (t, e) ->
	(* TODO: postcondition on result ? *)
	JCSreturn (t, e), pre, lao
    | JCStry (sb, catchl, sf) ->
	if debug then printf "  JCStry ...@.";
	let sb, post, lao = statement man pre true lao fil sb in
	let catchl, postl =
	  List.fold_left
	    (fun (acc1, acc2) (ei, vio, s) ->
	      let env, post = 
		match vio with
		| None -> Abstract1.env post, post
		| Some vi -> fresh_variable man (Abstract1.env post) post vi
	      in
	      let s, post, lao = statement man post true lao fil s in
	      (ei, vio, s)::acc1, post::acc2)
	    ([], [])
	    catchl
	in
	let pref = Abstract1.join_array man (Array.of_list (post::postl)) in
	let sf, post, lao = statement man pref true lao fil sf in
	JCStry (sb, catchl, sf), post, lao
    | JCSthrow (ei, eo) ->
        if debug then printf "  JCSthrow ...@.";
	JCSthrow (ei, eo), pre, lao
    | JCSpack (si1, e, si2) ->
	JCSpack (si1, e, si2), pre, lao
    | JCSunpack (si1, e, si2) ->
	JCSunpack (si1, e, si2), pre, lao
  in
  { s with jc_statement_node = jc_statement_node }, post, lao
									   ;;

*)
									   
let code_function fi bo = assert false
(*  if debug then printf "code_function...@.";
  if verbose then printf "  function %s@." fi.jc_fun_info_name;
  try
    (* let man = Box.manager_alloc () in *) (* Intervalles abstract domain *)
    let man = Oct.manager_alloc () in (* Octagon abstract domain *)
    (* let man = Polka.manager_alloc_strict () in *) (* Polyhedra abstract domain *)
    let env = Environment.make [||] [||] in
    
    (* add global variables as abstract variables in env *)
    let vars =
      Hashtbl.fold
	(fun tag (vi, eo) acc -> 
	  let vl = abstract_vars_of_vi vi in	
	  vl@acc)
	Jc_norm.variables_table
	[]
    in
    let env = Environment.add env (Array.of_list vars) [||] in
    
    (* add parameters as abstract variables in env *)
    let params =
      List.fold_left
        (fun acc vi ->
	  let vl = abstract_vars_of_vi vi in
	  vl@acc)
        []
        fi.jc_fun_info_parameters
    in
    let env = Environment.add env (Array.of_list params) [||] in
    
    match bo with
    | None -> None
    | Some sl ->
	(* annotation inference on the function body *)
	Some
	  (fst
	     (List.fold_left
		(fun (sl, pre) s ->
		  let s, post, _ = statement man pre true None fi.jc_fun_info_calls s in
		  (List.rev (s::(List.rev sl)), post)) 
		([], Abstract1.top man env)
		sl))
  with Manager.Error e ->
    Manager.print_exclog std_formatter e;
    bo
;;


let rec calls_infer fi fs bo =
  let bo = code_function fi bo in
  let (fi, _, _) = Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag in
  Hashtbl.replace Jc_norm.functions_table fi.jc_fun_info_tag (fi, fs, bo);
  List.iter
    (fun fi ->
      let fi, fs, bo =
	try 
	  Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag
	with Not_found -> assert false (* should never happen *)
      in
      calls_infer fi fs bo)
    fi.jc_fun_info_calls
;;

*)

let rec main_function fi fs bo = assert false
(*  calls_infer fi fs bo;
  if !calls_changed then 
    main_function fi fs bo
  else
    ()
;;


(* TODO : cas appels récursifs (direct ou indirect) *)


*)


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
