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


open Apron
open Format
open Jc_ast
open Jc_env
open Jc_fenv
open Jc_pervasives


let variables_table = Hashtbl.create 97
let expr_table = Hashtbl.create 97


let make_term loc node t = 
  { jc_term_node = node; jc_term_type = t; jc_term_loc = loc }
;;


let make_assertion loc node =
  { jc_assertion_node = node; jc_assertion_loc = loc }
;;


let make_and loc al =
  let al =
    List.filter
      (fun a -> a.jc_assertion_node <> JCAtrue)
      al
  in
  make_assertion loc (JCAand al)
;;


let absvalue_to_assertion man loc env a =
  let vars = fst (Environment.vars env) in
  let ia = Array.map (Abstract1.bound_variable man a) vars in
  List.fold_left2
    (fun a v i ->
       let vi = Hashtbl.find variables_table v in 
       Interval.print str_formatter i;
       let i = flush_str_formatter () in
       printf "%s@." i;
       let s = String.index i ';' in 
       let inf = String.sub i 1 (s - 1) in
       let la = 
         make_assertion 
           loc 
           (JCArelation(make_term loc (JCTconst (JCCinteger inf)) (JCTnative Tinteger),
			Ble_int,
			make_term loc (JCTvar vi) (JCTnative Tinteger))) in
       let sup = String.sub i (s + 2) (String.length i - (s + 3)) in
       let ra = make_assertion loc (JCArelation(make_term loc (JCTvar vi) (JCTnative Tinteger),
						Ble_int,
						make_term loc (JCTconst (JCCinteger sup)) (JCTnative Tinteger))) in
       make_and loc ([a; make_and loc [la; ra]]))
    (make_assertion loc JCAtrue)
    (Array.to_list vars)
    (Array.to_list ia)
;;


let fresh_variable man env pre vi =
  (* create a new variable *)
  let v = Var.of_string vi.jc_var_info_name in
  Hashtbl.add variables_table v vi;
  (* add the variable to env *)
  let env = Environment.add env [|v|] [||] in (* TO DO ?: raise Failure in case of name conflict -> should not occur *)
  (* update env in pre *)
  let pre = Abstract1.change_environment man pre env false in
  (env, pre)
;;


let rec not_expr e =
  let expr_node = 
    match e.jc_expr_node with
    | JCEconst c -> assert false (* TO DO *)
    | JCEvar vi -> assert false (* TO DO *)
    | JCEbinary(e1, bop, e2) ->
      begin
      match bop with
      | Blt_int -> JCEbinary (e1, Bge_int, e2)
      | Bgt_int -> JCEbinary (e1, Ble_int, e2)
      | Ble_int -> JCEbinary (e1, Bgt_int, e2)
      | Bge_int -> assert false (* TO DO *)
      | Beq_int -> assert false (* TO DO *)
	  (* JCEbinary (e1, Bneq_int, e2) *) (* != not supported by apron0.9.6 *)
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
    | JCEunary(uop, e) -> assert false (* TO DO *)
    | JCEshift(e1, e2) -> assert false (* TO DO *)
    | JCEderef(e, fi) -> assert false (* TO DO *)
    | JCEinstanceof(e, si) -> assert false (* TO DO *)
    | JCEcast(e, si) -> assert false (* TO DO *)
    | JCEif(e1, e2, e3) -> assert false (* TO DO *)
    | JCEoffset(ok, e, si) -> assert false (* TO DO *)
    | JCEalloc(e1, si) -> assert false (* TO DO *)
    | JCEfree(e) -> assert false (* TO DO *)
  in
  { e with jc_expr_node = expr_node }
;;


let rec expr man env pre e =
  match e.jc_expr_node with
  | JCEconst c ->
      begin
	match c with
        | JCCvoid -> assert false (* TO DO *)
        | JCCnull -> assert false (* TO DO *)
        | JCCboolean b -> assert false (* TO DO *)
        | JCCinteger s -> env, pre, s
        | JCCreal s -> assert false (* TO DO *)
      end
  | JCEvar vi -> env, pre, vi.jc_var_info_name
  | JCEbinary(e1, bop, e2) ->
      let env, pre, e1 = expr man env pre e1 in
      let env, pre, e2 = expr man env pre e2 in
      begin
	match bop with
	| Blt_int | Blt_real -> env, pre, e1 ^ "<" ^ e2
	| Bgt_int | Bgt_real -> env, pre, e1 ^ ">" ^ e2
	| Ble_int | Ble_real -> env, pre, e1 ^ "<=" ^ e2
	| Bge_int | Bge_real -> env, pre, e1 ^ ">=" ^ e2
	| Beq_int | Beq_real -> env, pre, e1 ^ "=" ^ e2
	| Bneq_int | Bneq_real | Beq_pointer -> env, pre, e1 ^ "!=" ^ e2
	| Badd_int | Badd_real | Bneq_pointer -> env, pre, e1 ^ "+" ^ e2
	| Bsub_int | Bsub_real -> env, pre, e1 ^ "-" ^ e2
	| Bmul_int | Bmul_real -> env, pre, e1 ^ "*" ^ e2
	| Bdiv_int -> env, pre, "1/" ^ e2 ^ "*" ^ e1
	| Bdiv_real -> assert false (* TO DO *)
	| Bmod_int -> assert false (* TO DO *)
	| Bland | Blor -> assert false (* should never happen *)
	| Bimplies -> assert false (* should never happen *)
	| Biff -> assert false (* should never happen *)
	| Bbw_and -> assert false (* TO DO *)
	| Bbw_or -> assert false (* TO DO *)
	| Bbw_xor -> assert false (* TO DO *)
	| Bshift_left -> assert false (* TO DO *)
	| Bshift_right -> assert false (* TO DO *)
      end
  | JCEunary(uop, e) -> assert false (* TO DO *)
  | JCEshift(e1, e2) -> 
      let env, pre, s1 = expr man env pre e1 in
      let env, pre, s2 = expr man env pre e2 in
      env, pre, s1 ^ "_" ^ s2
  | JCEderef(e, fi) ->
      begin
	match e.jc_expr_node with
	| JCEshift (e1, e2) ->
	    let env, pre, s = expr man env pre e in
	    let v = Var.of_string s in
	    if Hashtbl.mem expr_table v then
	      (env, pre, s)
	    else
	      (* create a new variable *)
	      let v = Var.of_string s in
	      Hashtbl.add expr_table v e;
	      (* add the variable to env *)
	      let env = Environment.add env [|v|] [||] in (* TO DO ?: raise Failure in case of name conflict -> should not occur *)
	      (* update env in pre *)
	      let pre = Abstract1.change_environment man pre env false in
	      (env, pre, s)
	| _ -> assert false (* TO DO *)
      end
  | JCEinstanceof(e, si) -> assert false (* TO DO *)
  | JCEcast(e, si) -> assert false (* TO DO *)
  | JCEif(e1, e2, e3) -> assert false (* TO DO *)
  | JCEoffset(ok, e, si) -> assert false (* TO DO *)
  | JCEalloc(e1, si) -> assert false (* TO DO *)
  | JCEfree(e) -> assert false (* TO DO *)
;;


let rec statement man pre s fv (* Uselesss ? *) =
  printf "statement ...@.";
  let jc_statement_node, post =
    match s.jc_statement_node with
      (* instructions *)
    | JCScall(vio, fi, el, s) ->
        printf "  JCScall ...@.";
        begin
          match vio with
          | None -> assert false (* TO DO *)
          | Some vi -> 
              begin
		match fi.jc_fun_info_name with
		| "shift" -> 
                    (* cases to distinguish parameters ? *)
                    (* just add the fresh variable to env *)
                    let env, pre = if fv then fresh_variable man (Abstract1.env pre) pre vi else (Abstract1.env pre), pre in
                    let s, post = statement man pre s fv in
                    (JCScall(vio, fi, el, s), post)
		| _ -> assert false (* TO DO *)
              end
        end
    | JCSassign_var(vi, e) ->
	printf "  JCSassign_var ...@.";
	(* make the constraint from the expr *)
	let v = Var.of_string vi.jc_var_info_name in
(*      let fv = Var.of_string (vi.jc_var_info_name ^ "_fresh") in *)
(*      let env = Environment.add (Abstract1.env pre) [|fv|] [||] in *)
	let env, pre, s = expr man (Abstract1.env pre) pre e in
	let linexpr = Parser.linexpr1_of_string (Abstract1.env pre) s in
	(* compute the new abstract value *)
	let post = Abstract1.assign_linexpr man pre v linexpr None in
(*      let post = Abstract1.rename_array man post [|fv|] [|v|] in *)
(*      let env = Environment.remove (Abstract1.env post) [|v|] [||] in *)
(*      let post = Abstract1.of_lincons_array man env (Abstract1.to_lincons_array man post) in *)
	(JCSassign_var(vi, e), post)       
    | JCSassign_heap(e1, fi, e2) ->
	printf "  JCSassign_heap ...@.";
	(JCSassign_heap(e1, fi, e2), pre)
	  (* statements *)
    | JCSassert(so, a) -> assert false (* TO DO *)
    | JCSblock sl ->
	printf "  JCSblock ...@.";
	let sl, post =
          List.fold_left
            (fun (sl, pre) s ->
              let s, post = statement man pre s fv in
              (List.rev (s::(List.rev sl)), post) ) 
            ([], pre) 
            sl
	in
	(JCSblock sl, post)
    | JCSdecl(vi, eo, s) ->
	printf "  JCSdecl ...@.";
        let env, pre = fresh_variable man (Abstract1.env pre) pre vi in
        begin
          match eo with
          | None ->
              (* no initial value => just give the new env *)
              let (s, post) = statement man pre s fv in
              (* TO DO ? : update env in pre (i.e. like in fresh_variable) *)
              (JCSdecl(vi, eo, s), post) 
          | Some e -> 
              (* initial value *)
              (* make the constraint from the expr *)
	      let env, pre, str = expr man env pre e in
              let lincons = Parser.lincons1_of_lstring env [vi.jc_var_info_name ^ "=" ^ str] in
              (* compute the new abstract value *)
              let post = Abstract1.meet_lincons_array man pre lincons in
              let (s, post) = statement man post s fv in
              (JCSdecl(vi, eo, s), post)
        end;
    | JCSif(e, s1, s2) ->
	(* Step 1: if branch *)
	let env, pre, s = expr man (Abstract1.env pre) pre e in
	let lincons = Parser.lincons1_of_lstring (Abstract1.env pre) [s] in
	let absvalue = Abstract1.of_lincons_array man (Abstract1.env pre) lincons in
	printf "if condition: %a@." Abstract1.print absvalue;
	let if_pre = Abstract1.meet man pre absvalue in
	let (s1, post1) = statement man if_pre s1 fv in
	(* Step 2: else branch *)
	let env, pre, s = expr man env pre (not_expr e) in
	let lincons = Parser.lincons1_of_lstring (Abstract1.env pre) [s] in
	let absvalue = Abstract1.of_lincons_array man (Abstract1.env pre) lincons in
	printf "else condition: %a@." Abstract1.print absvalue;
	let else_pre = Abstract1.meet man pre absvalue in
	let (s2, post2) = statement man else_pre s2 fv in
	(* Step 3: join the two branches *)
	let post = Abstract1.join man post1 post2 in
	(JCSif(e, s1, s2), post)
    | JCSloop(la, s) -> 
	assert false 
	  (* this case is treated in JCStry as every loop in normalized AST is enclosed within a try statement*)
    | JCSreturn_void -> assert false (* TO DO *)
    | JCSreturn(t, e) -> assert false (* TO DO *)
	  (* loop *)
    | JCStry(sb, [(ei, vio, s)], sf) ->
	printf "  JCStry ...@.";
	let sb, post =
          let jc_statement_node, post =
            match sb.jc_statement_node with
            | JCSloop(la, sb) ->
		let sb, post, la =
		  let jc_statement_node, post, la =
                    match sb.jc_statement_node with 
                    | JCStry(sb, cl, sf) ->
			let sb, post, la =
			  let jc_statement_node, post, la =
			    match sb.jc_statement_node with
			    | JCSblock(sl) -> 
				let sl, post, la =
				  match sl with
				  | [s1; s2] ->
				      let s1, post, la =
					let jc_statement_node, post, la =
					  match s1.jc_statement_node with
					  | JCSif(e, sb, se) -> 
					      (* make the constraint from the loop condition *)
					      (* printf "loop pre: %a@." Abstract1.print pre; *)
					      let pre = Abstract1.join man (Abstract1.bottom man (Abstract1.env pre)) pre in (* Useless ? *)
					      (* printf "pre(loop_condition): %a@." Abstract1.print pre; *)
					      let env, pre, s = expr man (Abstract1.env pre) pre e in
					      let lincons = Parser.lincons1_of_lstring (Abstract1.env pre) [s] in
					      let absvalue = Abstract1.of_lincons_array man (Abstract1.env pre) lincons in
					      printf "loop condition: %a@." Abstract1.print absvalue;
					      let pre = Abstract1.meet man pre absvalue in
					      (* printf "post(loop_condition): %a@." Abstract1.print pre; *)
					      let (sb, body) = statement man pre sb true in
					      (* printf "loop body: %a@." Abstract1.print body; *)
					      (* compute loop invariant *)
					      (* let pre = Abstract1.of_lincons_array man (Abstract1.env body) (Abstract1.to_lincons_array man pre) in *)
					      let body = Abstract1.change_environment man body (Abstract1.env pre) false in
					      (* printf "widen pre body : %a %a@." Abstract1.print pre Abstract1.print body; *)
					      let loop_inv = Abstract1.widening man pre body in
					      printf "after widening: %a@." Abstract1.print loop_inv;
					      (* update env in absvalue *)
					      let loop_inv = 
						Abstract1.change_environment man loop_inv (Abstract1.env absvalue) false
					      in
					      let loop_inv = Abstract1.meet man loop_inv absvalue in
					      printf "2nd loop_condition: %a@." Abstract1.print loop_inv;
					      let (sb, body) = statement man loop_inv sb false in
					      (* printf "2nd loop_body: %a@." Abstract1.print body; *)
					      let body = Abstract1.change_environment man body (Abstract1.env pre) false in
					      let loop_inv = Abstract1.join man pre body in
					      printf "computed loop invariant: %a@." Abstract1.print loop_inv;
					      let loop_invariant = la.jc_loop_invariant in
					      let infered_loop_inv = 
						absvalue_to_assertion man (loop_invariant.jc_assertion_loc) (Abstract1.env loop_inv) loop_inv
					      in
					      let la = 
						{ la with jc_loop_invariant = make_and (loop_invariant.jc_assertion_loc) [loop_invariant; infered_loop_inv] }
					      in
					      let env, pre, s = expr man env pre (not_expr e) in
					      printf "not e : %s@." s;
					      let lincons = Parser.lincons1_of_lstring (Abstract1.env pre) [s] in
					      let absvalue = Abstract1.of_lincons_array man (Abstract1.env pre) lincons in
					      let post = Abstract1.meet man loop_inv absvalue in
					      (JCSif(e, sb, se), post, la)
					  | _ -> assert false (* shoud never happen *)
					in
					({ s1 with jc_statement_node = jc_statement_node }, post, la)
				      in
				      ([s1; s2], post, la)
				  | _ -> assert false (* should never occur *)
				in
				(JCSblock(sl), post, la)
			    | _ -> assert false (* should never happen *)
			  in
			  ({ sb with jc_statement_node = jc_statement_node }, post, la)
			in
			(JCStry(sb, cl, sf), post, la)
                    | _ -> assert false (* should never happen *)
		  in
		  ({ sb with jc_statement_node = jc_statement_node }, post, la)
		in
		(JCSloop(la, sb), post)
            | _ -> assert false (* should never happen *)
          in
          ({ sb with jc_statement_node = jc_statement_node }, post)
	in
	let (s, post) = statement man post s true in
	(JCStry(sb, [(ei, vio, s)], sf), post)
	  (* 'true' try statement *)
    | JCStry(s1, cl, s2) -> assert false (* TO DO *)
    | JCSthrow(ei, eo) -> assert false (* TO DO *)
    | JCSpack(si1, e, si2) -> assert false (* TO DO *)
    | JCSunpack(si1, e, si2) -> assert false (* TO DO *)
  in
   ({ s with jc_statement_node = jc_statement_node }, post)
;;


let code_function fi slo =
  try
    let man = Box.manager_alloc () in
    (* let man = Oct.manager_alloc () in *)
    let env = Environment.make [||] [||] in

    (* add parameters as variables in env *)
    let params =
      List.fold_left
        (fun acc vi ->
           match vi.jc_var_info_type with
           | JCTnative nt ->
             begin
             match nt with
             | Tunit -> acc (* TO DO *)
	     | Tboolean -> acc (* TO DO *)
             | Tinteger -> (Var.of_string vi.jc_var_info_name)::acc
	     | Treal -> acc (* TO DO *)
             end
           | JCTlogic s -> acc (* TO DO *)
           | JCTenum ei -> acc (* TO DO *)
           | JCTpointer(si, n1, n2) -> acc (* TO DO *)
           | JCTnull -> acc (* TO DO *))
        []
        fi.jc_fun_info_parameters
    in
    let env = Environment.add env (Array.of_list params) [||] in

    match slo with
    | None -> None
    | Some sl ->
	(* annotation inference on the function body *)
	Some
	  (fst
	     (List.fold_left
		(fun (sl, pre) s ->
		  let s, post = statement man pre s true in
		  (List.rev (s::(List.rev sl)), post) ) 
		([], Abstract1.top man env) 
		sl))
  with Manager.Error e ->
    Manager.print_exclog std_formatter e;
    slo
;;


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
