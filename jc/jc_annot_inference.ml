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

(* $Id: jc_annot_inference.ml,v 1.84 2007-12-18 08:55:18 moy Exp $ *)

open Pp
open Format
open Jc_ast
open Jc_env
open Jc_envset
open Jc_fenv
open Jc_options
open Jc_pervasives
open Jc_iterators
open Jc_region

open Apron
open Coeff
open Interval
open Lincons1


module TermTable = 
  Hashtbl.Make(struct type t = term 
		      let equal = raw_term_equal
		      let hash = Hashtbl.hash end)

module TermSet =
  Set.Make(struct type t = term 
		  let compare = raw_term_compare end)

module TermMap =
  Map.Make(struct type t = term 
		  let compare = raw_term_compare end)

(*
  usage: jessie -ai <box,oct,pol,wp,boxwp,octwp,polwp>
  
  ai behaviour with other jessie options:
  
  -v prints inferred annotations
  -d prints debug info
*)


(* Variables used in the interprocedural analysis *)
let inspected_functions = ref []
let state_changed = ref false


(* Constructors *)

let full_term t ty r loc = {
  jc_term_node = t;
  jc_term_type = ty;
  jc_term_region = r;
  jc_term_loc = loc;
  jc_term_label = "";
}

let full_asrt a loc = {
  jc_assertion_node = a;
  jc_assertion_loc = loc;
  jc_assertion_label = "";
}

let var_expr vi = {
  jc_expr_node = JCEvar vi;
  jc_expr_type = vi.jc_var_info_type;
  jc_expr_region = vi.jc_var_info_region;
  jc_expr_loc = Loc.dummy_position;
  jc_expr_label = "";
}

let type_expr e ty = {
  jc_expr_node = e;
  jc_expr_type = ty;
  jc_expr_region = dummy_region; (* TODO *)
  jc_expr_loc = Loc.dummy_position;
  jc_expr_label = "";
}

let loc_expr e loc = {
  jc_expr_node = e;
  jc_expr_type = unit_type;
  jc_expr_region = dummy_region; (* TODO *)
  jc_expr_loc = loc;
  jc_expr_label = "";
}

let full_expr e ty loc = {
  jc_expr_node = e;
  jc_expr_type = ty;
  jc_expr_region = dummy_region; (* TODO *)
  jc_expr_loc = loc;
  jc_expr_label = "";
}

(* Utility functions *)
  
(* return the struct_info of (assumed) pointer t *)
let struct_of_term t =
  match t.jc_term_type with
    | JCTpointer(st,_,_) -> st
    | _ -> 
      if debug then printf "[struct_of_term] %a@." Jc_output.term t;
      assert false

let rec conjuncts a = match a.jc_assertion_node with
  | JCAand al -> List.flatten(List.map conjuncts al)
  | _ -> [a]

let rec disjuncts a = match a.jc_assertion_node with
  | JCAor al -> List.flatten(List.map disjuncts al)
  | _ -> [a]

let rec without_disjunct a = 
  fold_assertion (fun acc a -> match a.jc_assertion_node with
    | JCAor _ -> false
    | _ -> acc) true a

let normalize_term t =
  post_map_term (fun t -> 
    let tnode = match t.jc_term_node with
      | JCToffset(off,t',st) as tnode ->
	  begin match t'.jc_term_node with
	    | JCTshift(t1,t2) ->
		let offt1 = { t with jc_term_node = JCToffset(off,t1,st); } in
		JCTbinary(offt1,Bsub_int,t2)
	    | _ -> tnode
	  end
      | tnode -> tnode
    in
    { t with jc_term_node = tnode; }) t

let normalize_assertion a =
  let a = post_map_term_in_assertion normalize_term a in
  post_map_assertion (fun a -> 
    let anode = match a.jc_assertion_node with
      | JCAand al ->
	  JCAand(List.flatten (List.map conjuncts al))
      | JCAor al ->
	  JCAor(List.flatten (List.map disjuncts al))
      | anode -> anode
    in
    { a with jc_assertion_node = anode; }) a

let is_integral_type = function
  | JCTnative ty ->
      begin match ty with
	| Tunit | Treal | Tboolean -> false
	| Tinteger -> true
      end
  | JCTenum _ -> true
  | JCTpointer _ | JCTlogic _ | JCTnull -> false

let equality_operator_for_type = function
  | JCTnative ty ->
      begin match ty with
	| Tunit -> assert false
	| Treal -> Beq_real
	| Tboolean -> Biff
	| Tinteger -> Beq_int
      end
  | JCTlogic _ -> assert false
  | JCTenum _ -> Beq_int
  | JCTpointer _ -> Beq_pointer
  | JCTnull -> Beq_pointer

(*
let make_and al = 
  (* optimization *)
  let al = List.filter (fun a -> not (is_true a)) al in
  let anode = match al with
    | [] -> JCAtrue
    | [a] -> a.jc_assertion_node
    | a::tl -> JCAand al
  in
  raw_asrt anode
*)

let make_or al = 
  let anode = match al with
    | [] -> JCAfalse
    | [a] -> a.jc_assertion_node
    | al -> JCAor al
  in
  raw_asrt anode

let make_not a =
  raw_asrt(JCAnot a)

let rec term_name =
  let string_explode s = 
    let rec next acc i = 
      if i >= 0 then next (s.[i] :: acc) (i-1) else acc
    in
    next [] (String.length s - 1)
  in
  let string_implode ls =
    let s = String.create (List.length ls) in
    ignore (List.fold_left (fun i c -> s.[i] <- c; i + 1) 0 ls);
    s
  in
  let filter_alphanumeric s =
    let alphanum c = 
      String.contains "abcdefghijklmnopqrstuvwxyz" c
      || String.contains "ABCDEFGHIJKLMNOPQRSTUVWXYZ" c
      || String.contains "0123456789" c
      || c = '_'
    in
    string_implode (List.filter alphanum (string_explode s))
  in
  function t ->
    match t.jc_term_node with
      | JCTconst c ->
	  begin match c with
	    | JCCinteger s -> filter_alphanumeric s
	    | JCCboolean b -> if b then "true" else "false"
	    | JCCvoid -> "void"
	    | JCCnull -> "null" 
	    | JCCreal s -> filter_alphanumeric s
	  end
      | JCTvar vi -> filter_alphanumeric vi.jc_var_info_final_name
      | JCTbinary(t1,bop,t2) ->
	  let bop_name = match bop with
	    | Blt_int | Blt_real -> "inf"
	    | Bgt_int | Bgt_real -> "sup"
	    | Ble_int | Ble_real -> "infeq"
	    | Bge_int | Bge_real -> "supeq"
	    | Beq_int | Beq_real | Beq_bool | Beq_pointer -> "eq"
	    | Bneq_int | Bneq_real | Bneq_bool | Bneq_pointer -> "neq"
	    | Badd_int | Badd_real -> "plus"
	    | Bsub_int | Bsub_real -> "minus"
	    | Bmul_int | Bmul_real -> "times"
	    | Bdiv_int | Bdiv_real -> "div"
	    | Bmod_int -> "mod"
	    | Bland -> "and"
	    | Blor -> "or"
	    | Bimplies -> "implies"
	    | Biff -> "iff"
	    | Bbw_and -> "bwand"
	    | Bbw_or -> "bwor"
	    | Bbw_xor -> "bwxor"
	    | Bshift_left -> "shiftleft"		
	    | Blogical_shift_right -> "logicalshiftright"
	    | Barith_shift_right -> "arithshiftright"
	  in
	  term_name t1 ^ "_" ^ bop_name ^ "_" ^ (term_name t2)
      | JCTunary(uop,t1) ->
	  let uop_name = match uop with
	    | Uplus_int | Uplus_real -> "plus"
	    | Uminus_int | Uminus_real -> "minus"
	    | Unot -> "not"
	    | Ubw_not -> "bwnot"
	  in
	  uop_name ^ "_" ^ (term_name t1)
      | JCTshift (t1, t2) ->
	  term_name t1 ^ "_shift_" ^ (term_name t2)
      | JCTsub_pointer(t1,t2) ->
	  term_name t1 ^ "_sub_pointer_" ^ (term_name t2)
      | JCTderef (t1, fi) ->
	  term_name t1 ^ "_field_" ^ fi.jc_field_info_final_name
      | JCTapp(li,tl) ->
	  li.jc_logic_info_name ^ "_of_" ^ 
	    List.fold_right(fun t acc ->
	      if acc = "" then term_name t
	      else term_name t ^ "_and_" ^ acc
	    ) tl ""
      | JCTold t ->
	  "old_" ^ (term_name t)
      | JCToffset(Offset_max,t,st) ->
	  "offset_max_" ^ (term_name t)
      | JCToffset(Offset_min,t,st) ->
	  "offset_min_" ^ (term_name t)
      | JCTinstanceof(t,st) ->
	  (term_name t) ^ "_instanceof_" ^ st.jc_struct_info_name
      | JCTcast(t,st) ->
	  (term_name t) ^ "_cast_" ^ st.jc_struct_info_name
      | JCTif(t1,t2,t3) ->
	  "if_" ^ (term_name t1) ^ "_then_" ^ (term_name t2) 
	  ^ "_else_" ^ (term_name t3)
      | JCTrange(Some t1,Some t2) ->
	  (term_name t1) ^ "_range_" ^ (term_name t2)
      | JCTrange(Some t1,None) ->
	  (term_name t1) ^ "_range_none"
      | JCTrange(None,Some t2) ->
	  "none_range_" ^ (term_name t2)
      | JCTrange(None,None) ->
	  "none_range_none"

(* support of <new> (Nicolas) *)
let rec destruct_alloc t = 
  match t.jc_term_node with
    | JCTconst (JCCinteger str) -> None, Some t 
    | JCTvar vi -> Some vi, None
    | JCTbinary (t1, Bsub_int, t2) ->
	begin
	  match destruct_alloc t1 with
	    | None, None ->
		None, Some 
		  (term_no_loc
		    (JCTunary (Uminus_int, term_no_loc (JCTconst (JCCinteger "-1")) integer_type))
		    integer_type)
	    | Some vi, None ->
		None, Some 
		  (term_no_loc
		    (JCTbinary	(term_no_loc (JCTvar vi) integer_type,
		    Bsub_int,
		    term_no_loc (JCTconst (JCCinteger "-1")) integer_type))
		    integer_type)
	    | vio, Some offt ->
		let t3 = JCTbinary (offt, Bsub_int, t2) in
		let offt = full_term t3 integer_type dummy_region t1.jc_term_loc in
		vio, Some offt 
	end
    | _ -> assert false

(* Deconstruct a pointer term into a base pointer term and an integer offset.
 *)
let rec destruct_pointer t = 
  match t.jc_term_node with
    | JCTconst JCCnull ->
        (* If changing this, make sure [struct_of_term] is not called on
         * a null term.
         *)
        None,None
    | JCTvar _ | JCTderef _ ->
        Some t,None
    | JCTshift(t1,t2) ->
	begin match destruct_pointer t1 with
	  | topt,None -> topt,Some t2
	  | topt,Some offt -> 
	      let tnode = JCTbinary(offt,Badd_int,t2) in
	      let offt = full_term tnode integer_type dummy_region t2.jc_term_loc in
	      topt,Some offt
	end
    | JCTcast(t,_) -> 
        (* Pointer arithmetic in Jessie is not related to the size of 
	 * the underlying type, like in C. This makes it possible to commute
	 * cast and arithmetic.
         *)
        destruct_pointer t
    | JCTapp _ | JCTold _ | JCTif _ | JCTrange _ -> 
        (* Not supported yet. *)
        assert false
    | JCTconst _ | JCTsub_pointer _ | JCTbinary _ 
    | JCTunary _ | JCToffset _ | JCTinstanceof _ -> 
        (* Not of a pointer type. *)
        assert false

let rec term_depends_on_term t1 t2 =
  raw_sub_term t2 t1 ||
    match t2.jc_term_node with
      | JCTderef(t2',fi) ->
	  let t2' = select_option (fst(destruct_pointer t2')) t2' in
	  begin match t1.jc_term_node with
	    | JCTapp(f,tls) -> 
		List.fold_left2 (fun acc param arg -> acc ||
		  term_depends_on_term arg t2'
		  && 
		  VarSet.mem param 
		  f.jc_logic_info_effects.jc_effect_through_params
		) false f.jc_logic_info_parameters tls
	    | JCTderef(t1',fj) ->
		(fi.jc_field_info_tag = fj.jc_field_info_tag)
		&& term_depends_on_term t1' t2'
	    | _ -> false
	  end
      | _ -> false


(*****************************************************************************)
(* Types.                                                                    *)
(*****************************************************************************)

(* Assertion to be checked at some program point. *)
type target_assertion = {
  jc_target_statement : statement;
  jc_target_location : Loc.position;
  mutable jc_target_assertion : assertion;
  mutable jc_target_regular_invariant : assertion;
  mutable jc_target_propagated_invariant : assertion;
}

(* Abstract value made up of 2 parts:
 * - regular abstract value
 * - abstract value refined by previous assertions on the execution path
 * Both are mutable in order to get in place widening.
 *)
type 'a abstract_value = {
  mutable jc_absval_regular : 'a Abstract1.t;
  mutable jc_absval_propagated : 'a Abstract1.t;
}
    
(* Type of current invariant in abstract interpretation, made up of 3 parts:
 * - abstract value at current program point
 * - associative list of exceptions and abstract values obtained after throwing
 *   an exception of this type. It is mutable so that it can be changed in 
 *   place.
 * - abstract value after returning from the function. It is a reference so that
 *   it can be shared among all abstract invariants in a function.
 *)
type 'a abstract_invariants = {
  jc_absinv_normal : 'a abstract_value;
  mutable jc_absinv_exceptional : (exception_info * 'a abstract_value) list;
  jc_absinv_return : 'a abstract_value ref;
}

(* Parameters of an abstract interpretation. *)
type 'a abstract_interpreter = {
  jc_absint_manager : 'a Manager.t;
  jc_absint_function_environment : Environment.t;
  jc_absint_function_name : string;
  jc_absint_widening_threshold : int;
  jc_absint_loop_invariants : (int,'a abstract_invariants) Hashtbl.t;
  jc_absint_loop_initial_invariants : (int,'a abstract_invariants) Hashtbl.t;
  jc_absint_loop_iterations : (int,int) Hashtbl.t;
  jc_absint_loop_entry_invs : (int, 'a abstract_invariants) Hashtbl.t;
  jc_absint_target_assertions : target_assertion list;
}

(* Parameters of an interprocedural abstract interpretation. *)
type 'a interprocedural_ai = {
  jc_interai_manager : 'a Manager.t;
  jc_interai_function_preconditions : (int, 'a Abstract1.t) Hashtbl.t
}
    
(* Type of current postcondition in weakest precondition computation:
 * - postcondition at current program point
 * - associative list of exceptions and postconditions that should be satisfied
 *   when an exception of this type is caught
 * - stack of sets of modified variables, each set except the first one 
 *   corresponding to an enclosed loop
 *)
type weakest_postconditions = {
  jc_post_normal : assertion option;
  jc_post_exceptional : (exception_info * assertion) list;
  jc_post_inflexion_vars : VarSet.t ref;
  jc_post_modified_vars : VarSet.t list;
}

type weakest_precondition_computation = {
  jc_weakpre_loop_invariants : (int,assertion) Hashtbl.t;
}


(*****************************************************************************)
(* Debug.                                                                    *)
(*****************************************************************************)

let print_abstract_value fmt absval =
  fprintf fmt "@[<v 2>{regular: %a@\npropagated: %a@\n}@]"
    Abstract1.print absval.jc_absval_regular 
    Abstract1.print absval.jc_absval_propagated

let print_abstract_invariants fmt invs =
  fprintf fmt "@[<v 2>{@\nnormal: %a@\nexceptional: %a@\nreturn: %a@\n}@]"
    print_abstract_value invs.jc_absinv_normal
    (print_list comma (fun fmt (ei,absval) -> 
      fprintf fmt "(%s,%a)" ei.jc_exception_info_name
	print_abstract_value absval))
    invs.jc_absinv_exceptional
    print_abstract_value !(invs.jc_absinv_return)


let print_modified_vars fmt posts =
  fprintf fmt "modified vars: %a" 
    (print_list comma (fun fmt vi -> fprintf fmt "%s" vi.jc_var_info_name))
    (VarSet.elements (List.hd posts.jc_post_modified_vars))


(*****************************************************************************)
(* From expressions to terms and assertions.                                 *)
(*****************************************************************************)

let term_of_expr e =
  let rec term e = 
    let tnode = match e.jc_expr_node with
      | JCEconst c -> JCTconst c
      | JCEvar vi -> JCTvar vi
      | JCEbinary (e1, bop, e2) -> JCTbinary(term e1, bop, term e2)
      | JCEunary (uop, e1) -> JCTunary (uop, term e1)
      | JCEshift (e1, e2) -> JCTshift(term e1, term e2)
      | JCEsub_pointer (e1, e2) -> JCTsub_pointer (term e1, term e2)
      | JCEderef (e1, fi) -> JCTderef (term e1, fi)
      | JCEinstanceof (e1, st) -> JCTinstanceof (term e1, st)
      | JCEcast (e1, st) -> JCTcast (term e1, st)
      | JCErange_cast(_,e1) -> 
	  (* range does not modify term value *)
	  (term e1).jc_term_node 
      | JCEif (e1, e2, e3) -> JCTif (term e1, term e2, term e3)
      | JCEoffset (off, e1, st) -> JCToffset (off, term e1, st)
      | JCEalloc (e, _) -> (* support of <new> (nicolas) *)
	  (* Note: \offset_max(t) = length(t) - 1 *)
	  JCTbinary (term e, Bsub_int, term_no_loc (JCTconst (JCCinteger "1")) integer_type)
      | JCEfree _ -> failwith "Not a term"
    in
    full_term tnode e.jc_expr_type e.jc_expr_region e.jc_expr_loc 
  in
  try Some (term e) with Failure _ -> None
    
let rec asrt_of_expr e =
  let anode = match e.jc_expr_node with
    | JCEconst (JCCboolean true) -> JCAtrue
    | JCEconst (JCCboolean false) -> JCAfalse
    | JCEconst _ -> assert false
    | JCEvar vi ->
	begin match vi.jc_var_info_type with
	  | JCTnative Tboolean ->
	      let t = term_of_expr e in
	      begin match t with
		| None -> assert false
		| Some t -> JCAbool_term t
	      end
	  | _ -> assert false
	end
    | JCEbinary (e1, bop, e2) ->
	if is_relation_binary_op bop then
	  match term_of_expr e1,term_of_expr e2 with
	    | Some t1, Some t2 -> JCArelation (t1, bop, t2)
	    | _ -> JCAtrue
	else if is_logical_binary_op bop then
	  match bop with
	    | Bland -> JCAand [asrt_of_expr e1;asrt_of_expr e2]
	    | Blor -> JCAor [asrt_of_expr e1;asrt_of_expr e2]
	    | Bimplies -> JCAimplies(asrt_of_expr e1,asrt_of_expr e2)
	    | Biff -> JCAiff(asrt_of_expr e1,asrt_of_expr e2)
	    | _ -> assert false
	else assert false
    | JCEunary(uop,e1) ->
	if is_logical_unary_op uop then
	  match uop with
	    | Unot -> JCAnot(asrt_of_expr e1)
	    | _ -> assert false
	else assert false
    | JCEinstanceof(e1,st) ->
	begin match term_of_expr e1 with
	  | Some t1 -> JCAinstanceof(t1,st)
	  | None -> JCAtrue 
	end
    | JCEif(e1,e2,e3) -> 
	begin match term_of_expr e1 with
	  | Some t1 -> JCAif(t1,asrt_of_expr e2,asrt_of_expr e3)
	  | None -> JCAtrue 
	end
    | JCEderef _ -> 
	begin match term_of_expr e with
	  | Some t -> JCAbool_term t
	  | None -> JCAtrue 
	end
    | JCEcast _ | JCErange_cast _ | JCEshift _ | JCEsub_pointer _ 
    | JCEoffset _ | JCEalloc _ | JCEfree _ -> assert false
  in
  raw_asrt anode

let raw_asrt_of_expr = asrt_of_expr


(*****************************************************************************)
(* Replacing variables in terms and assertions.                              *)
(*****************************************************************************)

let rec replace_term_in_term ~source ~target t = 
  pre_map_term 
    (fun t -> if raw_term_equal source t then Some target else None) t
    
let rec replace_term_in_assertion srct targett a = 
  let term = replace_term_in_term ~source:srct ~target:targett in
  let asrt = replace_term_in_assertion srct targett in
  let anode = match a.jc_assertion_node with
    | JCArelation(t1,bop,t2) ->
	JCArelation(term t1,bop,term t2)
    | JCAnot a -> 
	JCAnot (asrt a)
    | JCAand al ->
	JCAand(List.map asrt al)
    | JCAor al ->
	JCAor(List.map asrt al)
    | JCAimplies(a1,a2) ->
	JCAimplies(asrt a1,asrt a2)
    | JCAiff(a1,a2) ->
	JCAiff(asrt a1,asrt a2)
    | JCAapp(li,tl) ->
	JCAapp(li,List.map term tl)
    | JCAquantifier(qt,vi,a) ->
	JCAquantifier(qt,vi,asrt a)
    | JCAold a ->
	JCAold(asrt a)      
    | JCAinstanceof(t,st) ->
	JCAinstanceof(term t,st)
    | JCAbool_term t ->
	JCAbool_term(term t)
    | JCAif(t,a1,a2) ->
	JCAif(term t,asrt a1,asrt a2)
    | JCAmutable(t,st,tag) ->
	JCAmutable(term t,st,tag)
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
  in
  { a with jc_assertion_node = anode; }


let rec replace_vi_in_assertion srcvi targett a = 
  let term = replace_term_in_term 
    ~source:(term_no_loc (JCTvar srcvi) srcvi.jc_var_info_type) 
    ~target:targett.jc_term_node in
  let asrt = replace_vi_in_assertion srcvi targett in
  let anode = match a.jc_assertion_node with
    | JCArelation (t1, bop, t2) ->
	JCArelation (term t1, bop, term t2)
    | JCAnot a -> 
	JCAnot (asrt a)
    | JCAand al ->
	JCAand (List.map asrt al)
    | JCAor al ->
	JCAor (List.map asrt al)
    | JCAimplies (a1, a2) ->
	JCAimplies (asrt a1, asrt a2)
    | JCAiff (a1, a2) ->
	JCAiff (asrt a1, asrt a2)
    | JCAapp (li, tl) ->
	JCAapp (li, List.map term tl)
    | JCAquantifier (qt, vi, a) ->
	JCAquantifier (qt, vi, asrt a)
    | JCAold a ->
	JCAold (asrt a)      
    | JCAinstanceof (t, st) ->
	JCAinstanceof (term t, st)
    | JCAbool_term t ->
	JCAbool_term (term t)
    | JCAif (t, a1, a2) ->
	JCAif (term t, asrt a1, asrt a2)
    | JCAmutable (t, st, tag) ->
	JCAmutable (term t, st, tag)
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
  in
  { a with jc_assertion_node = anode; }


(* comparison on names (vs. comparison by tag in 'replace_term_in_term' ) *)
let rec switch_vis_in_term srcvi targetvi t =
  let term = switch_vis_in_term srcvi targetvi in
  let node = match t.jc_term_node with
    | JCTconst c -> JCTconst c
    | JCTvar vi -> 
	if vi.jc_var_info_name = srcvi.jc_var_info_name then
	  JCTvar targetvi else JCTvar vi
    | JCTshift (t1, t2) -> JCTshift (term t1, term t2)
    | JCTsub_pointer (t1, t2) -> JCTsub_pointer (term t1, term t2)
    | JCTderef (t, fi) -> JCTderef (t, fi)
    | JCTbinary (t1, bop, t2) -> JCTbinary (term t1, bop, term t2)
    | JCTunary (op, t) -> JCTunary (op, term t)
    | JCTapp (li, tl) -> JCTapp (li, List.map term tl)
    | JCTold t -> JCTold (term t)
    | JCToffset (ok, t, si) -> JCToffset (ok, term t, si)
    | JCTinstanceof (t, si) -> JCTinstanceof (term t, si)
    | JCTcast (t, si) -> JCTcast (term t, si)
    | JCTif (t1, t2, t3) -> JCTif (t1, t2, t3)
    | JCTrange (to1, to2) -> JCTrange (Option_misc.map term to1, Option_misc.map term to2)
  in
  { t with jc_term_node = node; }
    
let rec switch_vis_in_assertion srcvi targetvi a = 
  let term = switch_vis_in_term srcvi targetvi in
  let asrt = switch_vis_in_assertion srcvi targetvi in
  let anode = match a.jc_assertion_node with
    | JCArelation (t1, bop, t2) ->
	JCArelation (term t1, bop, term t2)
    | JCAnot a -> 
	JCAnot (asrt a)
    | JCAand al ->
	JCAand (List.map asrt al)
    | JCAor al ->
	JCAor (List.map asrt al)
    | JCAimplies (a1, a2) ->
	JCAimplies (asrt a1, asrt a2)
    | JCAiff (a1, a2) ->
	JCAiff (asrt a1, asrt a2)
    | JCAapp (li, tl) ->
	JCAapp (li, List.map term tl)
    | JCAquantifier (qt, vi, a) ->
	JCAquantifier (qt, vi, asrt a)
    | JCAold a ->
	JCAold (asrt a)      
    | JCAinstanceof (t, st) ->
	JCAinstanceof (term t, st)
    | JCAbool_term t ->
	JCAbool_term (term t)
    | JCAif (t, a1, a2) ->
	JCAif (term t, asrt a1, asrt a2)
    | JCAmutable (t, st, tag) ->
	JCAmutable (term t, st, tag)
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
  in
  { a with jc_assertion_node = anode; }


(*****************************************************************************)
(* Abstract variables naming and creation.                                   *)
(*****************************************************************************)

module Vai : sig

  val has_variable : term -> bool
  val has_offset_min_variable : term -> bool
  val has_offset_max_variable : term -> bool

  val variable : term -> Var.t
  val offset_min_variable : term -> Var.t
  val offset_max_variable : term -> Var.t
  val all_variables : term -> Var.t list

  val term : Var.t -> term
  val variable_of_term : term -> Var.t

end = struct
  
  let variable_table = TermTable.create 0
  let offset_min_variable_table = TermTable.create 0
  let offset_max_variable_table = TermTable.create 0
  let term_table = Hashtbl.create 0

  let has_variable t =
    match t.jc_term_type with
      | JCTnative ty ->
	  begin match ty with
	    | Tunit | Treal -> false
	    | Tboolean | Tinteger -> true
	  end
      | JCTenum _ -> true
      | JCTpointer _ | JCTlogic _ | JCTnull -> false

  let has_offset_min_variable t =
    match t.jc_term_type with
      | JCTpointer _ -> true
      | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull -> false

  let has_offset_max_variable = has_offset_min_variable

  let variable t =
    try
      TermTable.find variable_table t
    with Not_found ->
      let va = Var.of_string (term_name t) in
      TermTable.add variable_table t va;
      Hashtbl.add term_table va t;
      va
	
  let offset_min_variable t =
    try
      TermTable.find offset_min_variable_table t
    with Not_found ->
      let va = Var.of_string ("__jc_offset_min_" ^ (term_name t)) in
      TermTable.add offset_min_variable_table t va;
      let st = struct_of_term t in
      let tmin = term_no_loc (JCToffset(Offset_min,t,st)) integer_type in
      Hashtbl.add term_table va tmin;
      va
	
  let offset_max_variable t = 
    try
      TermTable.find offset_max_variable_table t
    with Not_found ->
      let va = Var.of_string ("__jc_offset_max_" ^ (term_name t)) in
      TermTable.add offset_max_variable_table t va;
      let st = struct_of_term t in
      let tmax = term_no_loc (JCToffset(Offset_max,t,st)) integer_type in
      Hashtbl.add term_table va tmax;
      va

  let all_variables t =
    (if has_variable t then [variable t] else [])
    @ (if has_offset_min_variable t then [offset_min_variable t] else [])
    @ (if has_offset_max_variable t then [offset_max_variable t] else [])

  let term va = Hashtbl.find term_table va

  let variable_of_term t =
    match t.jc_term_node with
      | JCToffset(Offset_min,t,_) ->
	  begin match t.jc_term_node with
	    | JCTvar _ | JCTderef _ -> offset_min_variable t
	    | _ -> (*assert false*) offset_min_variable t
	  end
      | JCToffset(Offset_max,t,_) ->
	  begin match t.jc_term_node with
	    | JCTvar _ | JCTderef _ -> offset_max_variable t
	    | _ -> (*assert false*) offset_max_variable t
	  end
      | _ -> variable t
	  
end      


(*****************************************************************************)
(* Conversions between assertions and DNF form.                              *)
(*****************************************************************************)

module Dnf = struct

  type dnf = string list list

  let false_ = []
  let true_ = [[]]

  let is_false = function [] -> true | _ -> false
  let is_true = function [[]] -> true | _ -> false

  let num_disjuncts (dnf : dnf) = List.length dnf

  let is_singleton_disjunct dnf = num_disjuncts dnf = 1

  let get_singleton_disjunct = function
    | [[x]] -> x
    | _ -> assert false

  let rec make_and =
    let pair_and dnf1 dnf2 = 
      if is_false dnf1 || is_false dnf2 then
	false_
      else
	List.fold_left (fun acc conj1 ->
	  List.fold_left (fun acc conj2 ->
	    (conj1 @ conj2) :: acc
	  ) acc dnf2
	) [] dnf1
    in
    function
      | [] -> true_
      | dnf::r -> pair_and dnf (make_and r)

  let make_or = List.concat

  let print fmt dnf =
    fprintf fmt "dnf : %a" 
      (fun fmt disj -> 
	fprintf fmt "[%a]" (print_list comma 
	  (fun fmt conj -> fprintf fmt "[%a]" 
	    (print_list comma (fun fmt s -> fprintf fmt "%s" s)) 
	    conj)) disj) dnf

  let test mgr pre dnf =
    if debug then printf "[Dnf.test] %a@." Abstract1.print pre;
    if debug then printf "[Dnf.test] %a@." print dnf;
    let env = Abstract1.env pre in
    let test_conj copy_pre conj =
      let lincons =
	try Parser.lincons1_of_lstring env conj
	with Parser.Error msg -> printf "%s@." msg; assert false
      in
      Abstract1.meet_lincons_array_with mgr copy_pre lincons
    in
    if is_false dnf then
      (* Make [pre] be the bottom abstract value. *)
      let bot = Abstract1.bottom mgr env in
      Abstract1.meet_with mgr pre bot
    else if is_true dnf then
      ()
    else
      (* Test each disjunct separately and then join them. *)
      let copy_array = 
	Array.init (num_disjuncts dnf) 
	  (fun i -> if i = 0 then pre else Abstract1.copy mgr pre)
      in
      let copy_list = Array.to_list copy_array in
      List.iter2 test_conj copy_list dnf;
      begin match copy_list with
	| first::rest ->
	    assert (first == pre);
	    List.iter (fun absval -> Abstract1.join_with mgr pre absval) rest
	| _ -> assert false
      end

end

let assertion_of_dnf dnf = 
  let disjunct al = 
    let anode = match al with
      | [] -> JCAtrue
      | [a] -> a.jc_assertion_node
      | _ -> JCAand al
    in
    raw_asrt anode    
  in
  let anode = match dnf with
    | [] -> JCAfalse
    | [[]] -> JCAtrue
    | [al] -> (disjunct al).jc_assertion_node
    | _ -> JCAor (List.map disjunct dnf)
  in
  raw_asrt anode


(*****************************************************************************)
(* Extracting linear expressions and constraints from AST expressions.       *)
(*****************************************************************************)
    
let rec not_asrt a =
  let anode = match a.jc_assertion_node with
    | JCAtrue -> JCAfalse
    | JCAfalse -> JCAtrue
    | JCArelation (t1, bop, t2) ->
	begin match bop with
	  | Blt_int -> JCArelation (t1, Bge_int, t2)
	  | Bgt_int -> JCArelation (t1, Ble_int, t2)
	  | Ble_int -> JCArelation (t1, Bgt_int, t2)
	  | Bge_int -> JCArelation (t1, Blt_int, t2)
	  | Beq_int -> JCArelation (t1, Bneq_int, t2)
	  | Bneq_int -> JCArelation (t1, Beq_int, t2)
	  | Blt_real -> JCArelation (t1, Bge_real, t2)
	  | Bgt_real -> JCArelation (t1, Ble_real, t2)
	  | Ble_real -> JCArelation (t1, Bgt_real, t2)
	  | Bge_real -> JCArelation (t1, Blt_real, t2)
	  | Beq_real -> JCArelation (t1, Bneq_real, t2)
	  | Bneq_real -> JCArelation (t1, Beq_real, t2)
	  | Beq_bool -> JCArelation (t1, Bneq_bool, t2)
	  | Bneq_bool -> JCArelation (t1, Beq_bool, t2)
	  | Beq_pointer -> JCArelation (t1, Bneq_pointer, t2)
	  | Bneq_pointer -> JCArelation (t1, Beq_pointer, t2)
	  | Badd_int | Bsub_int | Bmul_int | Bdiv_int | Bmod_int
	  | Badd_real | Bsub_real | Bmul_real | Bdiv_real
	  | Bland | Blor | Bimplies | Biff
	  | Bbw_and | Bbw_or | Bbw_xor | Bshift_left
	  | Blogical_shift_right | Barith_shift_right -> assert false
	end
    | JCAnot a -> 
	a.jc_assertion_node
    | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _ | JCAapp _ 
    | JCAquantifier _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAtagequality _ ->
	JCAnot a
  in
  { a with jc_assertion_node = anode; }

let raw_not_asrt = not_asrt

let rec linearize t =
  match t.jc_term_node with
    | JCTconst c ->
	begin match c with
	  | JCCinteger s -> (TermMap.empty, int_of_string s)
	  | JCCboolean _ | JCCvoid | JCCnull | JCCreal _ ->
	      failwith "Not linear"
	end
    | JCTvar _ | JCTderef _ ->
	(TermMap.add t 1 TermMap.empty, 0)
    | JCTbinary (t1, bop, t2) ->
	if is_arithmetic_binary_op bop then
	  let coeffs1, cst1 = linearize t1 in
	  let coeffs2, cst2 = linearize t2 in
          begin match bop with
	    | Badd_int ->
		let coeffs = 
		  TermMap.fold (fun vt1 c1 acc ->
		    try 
		      let c2 = TermMap.find vt1 coeffs2 in
		      TermMap.add vt1 (c1 + c2) acc
		    with Not_found -> TermMap.add vt1 c1 acc
		  ) coeffs1 TermMap.empty
		in
		let coeffs = 
		  TermMap.fold (fun vt2 c2 acc ->
		    if TermMap.mem vt2 coeffs then acc
		    else TermMap.add vt2 c2 acc
		  ) coeffs2 coeffs
		in
		(coeffs, cst1 + cst2)
	    | Bsub_int ->
		let coeffs = 
		  TermMap.fold (fun vt1 c1 acc ->
		    try 
		      let c2 = TermMap.find vt1 coeffs2 in
		      TermMap.add vt1 (c1 - c2) acc
		    with Not_found -> TermMap.add vt1 c1 acc
		  ) coeffs1 TermMap.empty
		in
		let coeffs = 
		  TermMap.fold (fun vt2 c2 acc ->
		    if TermMap.mem vt2 coeffs then acc
		    else TermMap.add vt2 (- c2) acc
		  ) coeffs2 coeffs
		in
		(coeffs, cst1 - cst2)
	    | Bmul_int ->
		begin match 
		  TermMap.is_empty coeffs1,cst1,
		  TermMap.is_empty coeffs2,cst2 with
		    | true,_,true,_ -> (TermMap.empty,cst1 * cst2)
		    | true,cstmul,_,cstadd ->
			let coeffs = TermMap.map (fun c -> c*cstmul) coeffs2 in
			(coeffs,cstadd * cstmul)
		    | _,cstadd,true,cstmul -> 
			let coeffs = TermMap.map (fun c -> c*cstmul) coeffs1 in
			(coeffs,cstadd * cstmul)
		    | _ -> 
			(* Consider non-linear term as abstract variable. *)
			(TermMap.add t 1 TermMap.empty,0)
		end
	    | Badd_real | Bsub_real | Bmul_real | Bdiv_real ->
		failwith "Not integer"
	    | Bdiv_int | Bmod_int -> 
		failwith "Not linear"
	    | _ -> assert false
	  end
	else failwith "Not linear"
    | JCTunary(uop,t1) ->
	if is_arithmetic_unary_op uop then
	  let coeffs1,cst1 = linearize t1 in
	  begin match uop with
	    | Uplus_int -> 
		(coeffs1,cst1)
	    | Uminus_int -> 
		let coeffs = TermMap.map (fun c -> -c) coeffs1 in
		(coeffs,- cst1)
	    | Uplus_real | Uminus_real ->
		failwith "Not integer"
	    | _ -> assert false
	  end
	else failwith "Not linear"
    | JCToffset(_,vt,_) ->
	begin match vt.jc_term_node with
	  | JCTvar _ | JCTderef _ -> (TermMap.add t 1 TermMap.empty,0)
	  | _ -> (*assert false*) (TermMap.add t 1 TermMap.empty,0)
	end
    | JCTapp(f,_) -> (TermMap.add t 1 TermMap.empty,0)
    | JCTshift _ | JCTsub_pointer _ | JCTinstanceof _
    | JCTold _ | JCTcast _ | JCTrange _ | JCTif _ -> 
	failwith "Not linear"

type zero_bounds = {
  zlow : term;
  zup : term;
  zmulcst : int;
  zconstrs : assertion list;
}

let rec zero_bounds_term t =
  let auto_bounds t = 
    [ { zlow = t; zup = t; zmulcst = 1; zconstrs = []; }]
  in
  match t.jc_term_node with
    | JCTbinary (t1, bop, t2) ->
	if is_arithmetic_binary_op bop then
          begin match bop with
	    | Badd_int ->
		let add_zb zb1 zb2 =
		  if zb1.zmulcst = zb2.zmulcst then
		    let lb = term_no_loc (JCTbinary (zb1.zlow, Badd_int, zb2.zlow)) integer_type in
		    let rb = term_no_loc (JCTbinary (zb1.zup, Badd_int, zb2.zup)) integer_type in
		    { zlow = lb; zup = rb; zmulcst = zb1.zmulcst; 
		    zconstrs = zb1.zconstrs @ zb2.zconstrs; }
		  else
		    let cst1 =
		      term_no_loc (JCTconst(JCCinteger(string_of_int zb1.zmulcst))) integer_type in
		    let cst2 =
		      term_no_loc (JCTconst(JCCinteger(string_of_int zb2.zmulcst))) integer_type in
		    let lb1 = term_no_loc (JCTbinary(zb1.zlow,Bmul_int,cst2)) integer_type in
		    let lb2 = term_no_loc (JCTbinary(zb2.zlow,Bmul_int,cst1)) integer_type in
		    let rb1 = term_no_loc (JCTbinary(zb1.zup,Bmul_int,cst2)) integer_type in
		    let rb2 = term_no_loc (JCTbinary(zb2.zup,Bmul_int,cst1)) integer_type in
		    let lb = term_no_loc (JCTbinary(lb1,Badd_int,lb2)) integer_type in
		    let rb = term_no_loc (JCTbinary(rb1,Badd_int,rb2)) integer_type in
		    { zlow = lb; zup = rb; zmulcst = zb1.zmulcst * zb2.zmulcst; 
		    zconstrs = zb1.zconstrs @ zb2.zconstrs; }
		in
		let zbs1 = zero_bounds_term t1 in
		let zbs2 = zero_bounds_term t2 in
		let zbs = List.map (fun zb1 -> List.map (add_zb zb1) zbs2) zbs1 in
		List.flatten zbs
	    | Bsub_int ->
		let t2 = term_no_loc (JCTunary (Uminus_int, t2)) integer_type in
		let t = term_no_loc (JCTbinary(t1, Badd_int, t2)) integer_type in
		zero_bounds_term t
	    | Bmul_int ->
		(* TODO: refine when one operand is constant *)
		auto_bounds t
	    | Badd_real | Bsub_real | Bmul_real | Bdiv_real ->
		auto_bounds t
	    | Bdiv_int ->
		let div_zb t cst zb =
		  let cstt =
		    term_no_loc (JCTconst(JCCinteger(string_of_int (cst-1)))) integer_type in
		  let zero = term_no_loc (JCTconst(JCCinteger "0")) integer_type in
		  let zbpos = {
		    zlow = term_no_loc (JCTbinary(zb.zlow,Bsub_int,cstt)) integer_type;
		    zup = zb.zup; 
		    zmulcst = zb.zmulcst * cst; 
		    zconstrs = 
		      raw_asrt(JCArelation(t,Bge_int,zero)) :: zb.zconstrs; 
		  } in
		  let zbneg = {
		    zlow = zb.zlow;
		    zup = term_no_loc (JCTbinary(zb.zup,Badd_int,cstt)) integer_type; 
		    zmulcst = zb.zmulcst * cst; 
		    zconstrs = 
		      raw_asrt(JCArelation(t,Blt_int,zero)) :: zb.zconstrs; 
		  } in
		  [zbpos; zbneg]
		in
		begin match t2.jc_term_node with
		  | JCTconst c ->
		      begin match c with
			| JCCinteger s ->
			    let mulcst2 = int_of_string s in
			    let neg = mulcst2 < 0 in
			    let mulcst2 = abs mulcst2 in
			    let t1 =
			      if neg then term_no_loc (JCTunary(Uminus_int,t1)) integer_type else t1
			    in
			    let zbs1 = zero_bounds_term t1 in
			    List.flatten (List.map (div_zb t1 mulcst2) zbs1)
			| JCCboolean _ | JCCvoid | JCCnull | JCCreal _ ->
			    auto_bounds t
		      end
		  | _ -> auto_bounds t
		end
	    | Bmod_int ->
		auto_bounds t
	    | _ -> assert false
	  end
	else auto_bounds t
    | JCTunary (uop, t1) ->
	if is_arithmetic_unary_op uop then
	  begin match uop with
	    | Uplus_int ->
		zero_bounds_term t1
	    | Uminus_int ->
		let minus_zb zb =
		  let lb1 = term_no_loc (JCTunary (Uminus_int, zb.zlow)) integer_type in
		  let rb1 = term_no_loc (JCTunary (Uminus_int, zb.zup)) integer_type in
		  { zb with zlow = rb1; zup = lb1; }
		in
		let zbs = zero_bounds_term t1 in
		List.map minus_zb zbs
	    | Uplus_real | Uminus_real ->
		auto_bounds t
	    | _ -> assert false
	  end
	else auto_bounds t
    | JCTconst _ | JCTvar _ | JCTderef _ | JCToffset _
    | JCTapp _ | JCTshift _ | JCTsub_pointer _ | JCTinstanceof _
    | JCTold _ | JCTcast _ | JCTrange _ | JCTif _ ->
	auto_bounds t
	  
let linstr_of_term env t =
  let mkmulstr = function
    | (va, 0) -> ""
    | (va, c) -> string_of_int c ^ " * " ^ va 
  in
  let rec mkaddstr = function
    | [] -> ""
    | [va,c] -> mkmulstr (va,c)
    | (va,c) :: r -> 
	match mkmulstr (va,c), mkaddstr r with
	  | "","" -> ""
	  | s,"" | "",s -> s
	  | s1,s2 -> s1 ^ " + " ^ s2
  in
  try
    let coeffs, cst = linearize t in
    let env = 
      TermMap.fold (fun t _ env  ->
	let va = Vai.variable_of_term t in
	if Environment.mem_var env va then env
	else Environment.add env [|va|] [||]
      ) coeffs env 
    in
    let coeffs = 
      TermMap.fold (fun t c acc ->
	let va = Vai.variable_of_term t in (Var.to_string va,c)::acc
      ) coeffs []
    in
    Some (env, mkaddstr coeffs, cst)
  with Failure _ -> None

type offset_kind = Offset_min_kind | Offset_max_kind    

let offset_linstr_of_term env ok t =
  match destruct_pointer t with
    | None, _ -> None
    | Some ptrt, offt ->
	let st = struct_of_term ptrt in
	let minmaxt = match ok with
	  | Offset_min_kind ->  
	      term_no_loc (JCToffset(Offset_min,ptrt,st)) integer_type
	  | Offset_max_kind -> 
	      term_no_loc (JCToffset(Offset_max,ptrt,st)) integer_type
	in
	let t = match offt with None -> minmaxt | Some offt -> 
	  term_no_loc (JCTbinary(minmaxt,Bsub_int,offt)) integer_type
	in
	linstr_of_term env t
	  
let rec stronger_assertion a = 
  match a.jc_assertion_node with
    | JCArelation(t1,bop,t2) ->
	let subt = term_no_loc (JCTbinary (t1, Bsub_int, t2)) integer_type in
	let zbs = zero_bounds_term subt in
	let zero = term_no_loc (JCTconst (JCCinteger "0")) integer_type in
	let dnf = match bop with
	  | Beq_int ->
	      List.map (fun zb ->
		let lwcstr = 
		  raw_asrt(JCArelation(zb.zlow,Beq_int,zero)) in
		let upcstr = 
		  raw_asrt(JCArelation(zb.zup,Beq_int,zero)) in
		lwcstr :: upcstr :: zb.zconstrs
	      ) zbs
	  | Bneq_int -> []
	  | Ble_int | Blt_int ->
	      List.map (fun zb ->
		let lwcstr = 
		  raw_asrt(JCArelation(zb.zup,bop,zero)) in
		lwcstr :: zb.zconstrs
	      ) zbs
	  | Bge_int | Bgt_int ->
	      List.map (fun zb ->
		let upcstr = 
		  raw_asrt(JCArelation(zb.zlow,Bge_int,zero)) in
		upcstr :: zb.zconstrs
	      ) zbs
	  | _ -> assert false (* TODO *)
	in assertion_of_dnf dnf
    | _ -> a
	
(* Returns a dnf. *)
let rec linstr_of_assertion env a =
  match a.jc_assertion_node with
    | JCAtrue -> env, Dnf.true_
    | JCAfalse -> env, Dnf.false_
    | JCArelation (t1, bop, t2) ->
	let subt = term_no_loc (JCTbinary (t1, Bsub_int, t2)) integer_type in
	begin match linstr_of_term env subt with
	  | Some (env,str,cst) ->
	      let cstr = string_of_int (- cst) in
	      (* Do not use < and > with APRON. Convert to equivalent non-strict. *)
	      let str = match bop with
		| Blt_int -> [[str ^ " <= " ^ (string_of_int ((- cst) - 1))]]
		| Bgt_int -> [[str ^ " >= " ^ (string_of_int ((- cst) + 1))]]
		| Ble_int -> [[str ^ " <= " ^ cstr]]
		| Bge_int -> [[str ^ " >= " ^ cstr]]
		| Beq_int -> [[str ^ " = " ^ cstr]]
		| Blt_real | Bgt_real | Ble_real | Bge_real
		| Beq_bool | Bneq_bool | Beq_real | Beq_pointer
		| Bneq_int | Bneq_real | Bneq_pointer -> Dnf.true_
		| _ -> assert false
	      in
	      env, str
	  | None -> 
	      let zbs = zero_bounds_term subt in
	      let zero = term_no_loc (JCTconst(JCCinteger "0")) integer_type in
	      if List.length zbs <= 1 then 
		(* If [zero_bounds_term] found an integer division on which 
		   to split, length of resulting list must be pair, 
		   and thus >= 2. *)
		env, Dnf.true_
	      else
		let str_of_conjunct env conj =
		  List.fold_left (fun (env,strconj) a -> 
		    let env,dnf = linstr_of_assertion env a in
		    if Dnf.is_false dnf then
		      assert false (* TODO *)
		    else if Dnf.is_true dnf then
		      env,strconj
		    else if Dnf.is_singleton_disjunct dnf then
		      env,Dnf.get_singleton_disjunct dnf :: strconj (* base case *)
		    else assert false (* TODO *)
		  ) (env,[]) conj
		in
		let strdnf_of_dnf env adnf =
		  let env,strdnf = 
		    List.fold_left (fun (env,strdnf) conj ->
		      let env,strconj = str_of_conjunct env conj in
		      match strconj with
			| [] -> env, strdnf
			| _ -> env, strconj :: strdnf
		    ) (env,[]) adnf
		  in
		  let strdnf = match strdnf with
		    | [] -> Dnf.true_
		    | dnf -> dnf
		  in
		  env,strdnf
		in
		begin match bop with
		  | Beq_int ->
		      let adnf = 
			List.map (fun zb ->
			  let lwcstr = 
			    raw_asrt(JCArelation(zb.zlow,Ble_int,zero)) in
			  let upcstr = 
			    raw_asrt(JCArelation(zb.zup,Bge_int,zero)) in
			  lwcstr :: upcstr :: zb.zconstrs
			) zbs
		      in strdnf_of_dnf env adnf
		  | Bneq_int -> env,Dnf.true_
		  | Ble_int | Blt_int ->
		      let adnf = 
			List.map (fun zb ->
			  let lwcstr = 
			    raw_asrt(JCArelation(zb.zlow,bop,zero)) in
			  lwcstr :: zb.zconstrs
			) zbs
		      in strdnf_of_dnf env adnf
		  | Bge_int | Bgt_int ->
		      let adnf = 
			List.map (fun zb ->
			  let upcstr = 
			    raw_asrt(JCArelation(zb.zup,Bge_int,zero)) in
			  upcstr :: zb.zconstrs
			) zbs
		      in strdnf_of_dnf env adnf
		  | _ -> assert false (* TODO *)
		end
	end
    | JCAnot a ->
	let nota = not_asrt a in
	begin match nota.jc_assertion_node with
	  | JCAnot _ -> env, Dnf.true_
	  | _ -> linstr_of_assertion env nota
	end
    | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _ | JCAapp _ 
    | JCAquantifier _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAtagequality _ -> env, Dnf.true_
	
let unique_linstr_of_assertion env a =
  match snd (linstr_of_assertion env a) with
    | [[str]] -> str
    | _ -> assert false

let offset_min_linstr_of_assertion env a = env,[[]] (* TODO *)
let offset_max_linstr_of_assertion env a = env,[[]] (* TODO *)

let linstr_of_expr env e = 
  match term_of_expr e with
    | None -> None
    | Some t ->
	match linstr_of_term env t with
	  | None -> None
	  | Some (env,"",cst) -> Some (env,string_of_int cst)
	  | Some (env,str,cst) -> Some (env,str ^ " + " ^ (string_of_int cst))

let offset_linstr_of_expr env ok e = 
  match e.jc_expr_node with
    | JCEalloc _ -> 
	if ok = Offset_min_kind then Some (env, "0") else
	  (* Note: support of offset_max was skipped ? it seems to work well (Nicolas) *)
	  if ok = Offset_max_kind then
	    match term_of_expr e with
	      | None -> None
	      | Some t -> 
		  match linstr_of_term env t with
		    | None -> None
		    | Some (env,"",cst) -> Some (env,string_of_int cst)
		    | Some (env,str,cst) -> Some (env,str ^ " + " ^ (string_of_int cst))
	  else None
    | _ ->
	match term_of_expr e with
	  | None -> None
	  | Some t -> 
	      match offset_linstr_of_term env ok t with
		| None -> None
		| Some (env,"",cst) -> Some (env,string_of_int cst)
		| Some (env,str,cst) -> Some (env,str ^ " + " ^ (string_of_int cst))
		    
let is_null_term t = 
  match t.jc_term_node with
    | JCTconst (JCCinteger "0") -> true
    | _ -> false


(*****************************************************************************)
(* Building assertions from inferred invariants.                             *)
(*****************************************************************************)

let mkterm linexpr =
  let vars = 
    Array.to_list (fst (Environment.vars (Linexpr1.get_env linexpr))) 
  in
  let rec add_term t va =
    match Linexpr1.get_coeff linexpr va with
      | Scalar s ->
	  let vt = match Scalar.to_string s with
	    | "0." | "0" -> None
	    | "1" -> Some (Vai.term va)
	    | "-1" -> 
		let tnode = JCTunary (Uminus_int, Vai.term va) in
		let t = term_no_loc tnode integer_type in
		Some t
	    | s -> 
		let ctnode = JCTconst (JCCinteger s) in
		let ct = term_no_loc ctnode integer_type in
		let tnode = JCTbinary (ct, Bmul_int, Vai.term va) in
		let t = term_no_loc tnode integer_type in
		Some t
	  in
	  begin match t,vt with
	    | None,vt -> vt
	    | t,None -> t
	    | Some t,Some vt ->
		let tnode = JCTbinary (t, Badd_int, vt) in
		let t = term_no_loc tnode integer_type in
		Some t
	  end
      | Interval _ -> assert false
  in
  let cst = match Linexpr1.get_cst linexpr with
    | Scalar s ->
	begin match Scalar.to_string s with
	  | "0." | "0" -> None
	  | s -> 
	      let ctnode = JCTconst (JCCinteger s) in
	      let ct = term_no_loc ctnode integer_type in
	      Some ct
	end
    | Interval _ -> assert false
  in
  match List.fold_left add_term cst vars with
    | None -> assert false
    | Some t -> t
	
let mkassertion lincons =
  let t1 = mkterm (Lincons1.get_linexpr1 lincons) in
  let op,c2 = match Lincons1.get_typ lincons with
    | EQ -> Beq_int, JCCinteger "0"
    | SUPEQ -> Bge_int, JCCinteger "0"
    | SUP -> Bgt_int, JCCinteger "0"
    | DISEQ -> Bneq_int, JCCinteger "0"
    | EQMOD scalar -> Bmod_int, JCCinteger (Scalar.to_string scalar)
  in
  let t2 = term_no_loc (JCTconst c2) integer_type in
  raw_asrt (JCArelation(t1,op,t2)) 

let presentify a =
  let rec linterms_of_term t =
    let mkmulterm = function
      | (t,0) -> None
      | (t,1) -> Some t
      | (t,-1) ->
	  Some(term_no_loc (JCTunary(Uminus_int,t)) integer_type)
      | (t,c) ->
	  let c = term_no_loc (JCTconst(JCCinteger(string_of_int c))) integer_type in
	  Some(term_no_loc (JCTbinary(c,Bmul_int,t)) integer_type)
    in
    let rec mkaddterm = function
      | [] -> None
      | [t,c] -> mkmulterm (t,c)
      | (t,c) :: r ->
	  match mkmulterm (t,c), mkaddterm r with
	    | None,None -> None
	    | Some t,None | None,Some t -> Some t
	    | Some t1,Some t2 -> Some(term_no_loc (JCTbinary(t1,Badd_int,t2)) integer_type)
    in
    try
      let coeffs,cst = linearize t in
      let posl,negl =
	TermMap.fold (fun t c (pl,nl) ->
	  if c > 0 then (t,c) :: pl, nl
	  else if c < 0 then pl, (t,-c) :: nl
	  else pl, nl
	) coeffs ([],[])
      in
      let cstt = term_no_loc (JCTconst(JCCinteger(string_of_int(abs cst)))) integer_type in
      let post = match mkaddterm posl with
	| None -> 
	    if cst > 0 then cstt else term_no_loc (JCTconst(JCCinteger "0")) integer_type
	| Some t -> 
	    if cst > 0 then term_no_loc (JCTbinary(t,Badd_int,cstt)) integer_type else t
      in
      let negt = match mkaddterm negl with
	| None ->
	    if cst < 0 then cstt else term_no_loc (JCTconst(JCCinteger "0")) integer_type
	| Some t ->
	    if cst < 0 then term_no_loc (JCTbinary(t,Badd_int,cstt)) integer_type else t
      in
      Some (post,negt)
    with Failure _ -> None
  in
  let rec linasrt_of_assertion a =
    match a.jc_assertion_node with
      | JCArelation(t1,bop,t2) ->
	  let subt = term_no_loc (JCTbinary(t1,Bsub_int,t2)) integer_type in
	  begin match linterms_of_term subt with
	    | None -> a
	    | Some (post,negt) -> raw_asrt(JCArelation(post,bop,negt))
	  end
      | JCAnot a ->
	  let nota = not_asrt a in
	  begin match nota.jc_assertion_node with
	    | JCAnot _ -> a
	    | _ -> linasrt_of_assertion nota
	  end
      | JCAtrue | JCAfalse | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _
      | JCAapp _ | JCAquantifier _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
      | JCAif _ | JCAmutable _ | JCAtagequality _ -> a
  in
  linasrt_of_assertion a

let mkinvariant mgr absval =
  if Abstract1.is_top mgr absval = Manager.True then
    raw_asrt JCAtrue    
  else if Abstract1.is_bottom mgr absval = Manager.True then
    raw_asrt JCAfalse
  else
    let linconsarr = Abstract1.to_lincons_array mgr absval in
    let rec mkrec acc i = 
      if i >= 0 then
	mkrec (mkassertion (Lincons1.array_get linconsarr i) :: acc) (i-1)
      else acc
    in
    let asserts = mkrec [] (Lincons1.array_length linconsarr - 1) in
    make_and (List.map presentify asserts)


(*****************************************************************************)
(* Collecting assertions.                                                    *)
(*****************************************************************************)
      
(* Collect safety assertions from the evaluation of expression [e]. 
 * Currently, 3 kinds of assertions are collected, that check for:
 * - memory safety 
 * - no integer overflows
 * - no division by zero
 *)
let collect_expr_asserts e =
  (* Collect memory safety assertions. *)
  let collect_memory_access e1 fi =
    match term_of_expr e1 with None -> [] | Some t1 ->
      match destruct_pointer t1 with None,_ -> [] | Some ptrt,offopt ->
	let offt = match offopt with
	  | None -> term_no_loc (JCTconst(JCCinteger"0")) integer_type
	  | Some offt -> offt
	in
	let st = struct_of_term ptrt in
	let mint = term_no_loc (JCToffset(Offset_min,ptrt,st)) integer_type in
	let maxt = term_no_loc (JCToffset(Offset_max,ptrt,st)) integer_type in
	let mina = raw_asrt(JCArelation(mint,Ble_int,offt)) in
	let maxa = raw_asrt(JCArelation(offt,Ble_int,maxt)) in
	let mina = stronger_assertion mina in
	let maxa = stronger_assertion maxa in
	[mina;maxa]
  in
  (* Collect absence of integer overflow assertions. *)
  let collect_integer_overflow ei e1 =
    match term_of_expr e1 with None -> [] | Some t1 ->
      let mint = term_no_loc
	(JCTconst (JCCinteger (Num.string_of_num ei.jc_enum_info_min)))
	integer_type
      in
      let maxt = term_no_loc
	(JCTconst(JCCinteger (Num.string_of_num ei.jc_enum_info_max)))
	integer_type
      in
      let mina = raw_asrt (JCArelation (mint, Ble_int, t1)) in
      let maxa = raw_asrt (JCArelation (t1, Ble_int, maxt)) in
      let mina = stronger_assertion mina in
      let maxa = stronger_assertion maxa in
      [mina; maxa]
  in
  (* Collect absence of division by zero assertions. *)
  let collect_zero_division e =
    match term_of_expr e with None -> [] | Some t ->
      let zero = term_no_loc (JCTconst(JCCinteger "0")) integer_type in
      [raw_asrt(JCArelation(t,Bneq_int,zero))]
  in
  let collect e = 
    match e.jc_expr_node with
      | JCEderef(e1,fi) -> collect_memory_access e1 fi
      | JCErange_cast(ei,e1) -> collect_integer_overflow ei e1
      | JCEbinary(_,Bdiv_int,e2) -> collect_zero_division e2
      | _ -> []
  in
  fold_expr (fun acc e -> collect e @ acc) [] e

let collect_statement_asserts s = 
  match s.jc_statement_node with
    | JCSdecl(_,Some e1,_)
    | JCSassign_var(_,e1) | JCSpack(_,e1,_) | JCSunpack(_,e1,_) ->
	collect_expr_asserts e1
    | JCScall(_,call,s) ->
	let fi = call.jc_call_fun in
	let els = call.jc_call_args in
	let _,_,fs,_ = 
          Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag 
        in
        (* Collect preconditions of functions called. *)
        let reqa = fs.jc_fun_requires in
        let reqa = 
	   List.fold_left2 (fun a param arg ->
             match term_of_expr arg with None -> raw_asrt JCAtrue | Some targ ->
               replace_term_in_assertion (term_var_no_loc param) targ.jc_term_node a
	   ) reqa fi.jc_fun_info_parameters els
        in
        (conjuncts reqa)
	@ List.flatten (List.map collect_expr_asserts els)
    | JCSassert a when a.jc_assertion_label = "hint" -> 
	(* Hints are not to be proved by abstract interpretation, 
	   only added to help it. *)
	[]
    | JCSassert a -> 
	(* Consider separately each conjunct in a conjunction. *)
	conjuncts a
    | JCSassign_heap (e1, fi, e2) ->
	let derefe = loc_expr (JCEderef (e1, fi)) s.jc_statement_loc in
	(collect_expr_asserts derefe) @ (collect_expr_asserts e2)
    | JCSdecl(_,None,_) | JCSblock _ | JCSif _ | JCStry _ | JCSloop _
    | JCSreturn_void | JCSreturn _ | JCSthrow _ ->
	[]
	  
let target_of_assertion s loc a = 
  { 
    jc_target_statement = s;
    jc_target_location = loc;
    jc_target_assertion = a;
    jc_target_regular_invariant = raw_asrt JCAfalse;
    jc_target_propagated_invariant = raw_asrt JCAfalse;
  }

let collect_expr_targets s e = 
  let asrts = collect_expr_asserts e in
  let asrts = List.map normalize_assertion asrts in
  List.map (target_of_assertion s e.jc_expr_loc) asrts

let rec collect_targets filter_asrt targets s =
  let rec collect targets s =
    let asrts = collect_statement_asserts s in
    let asrts = List.map normalize_assertion asrts in
    
    if debug then printf "[collecting] %a@." 
      (print_list comma Jc_output.assertion) asrts;

    let targets = 
      (List.map (target_of_assertion s s.jc_statement_loc) asrts) @ targets in
    match s.jc_statement_node with
      | JCSdecl(_,_,s) | JCScall(_,_,s) -> 
	  collect targets s
      | JCSblock sl ->
	  List.fold_left collect targets sl
      | JCSif(e,ts,fs) ->
	  collect (collect 
	    (collect_expr_targets s e @ targets) ts) fs
      | JCStry(s,hl,fs) ->
	  let targets = collect targets s in
	  let targets = 
	    List.fold_left 
	      (fun targets (_,_,s) -> collect targets s) targets hl
	  in
	  collect targets fs
      | JCSloop(_,ls) ->
	  collect targets ls
      | JCSreturn(_,e) | JCSthrow(_,Some e) ->
	  collect_expr_targets s e @ targets
      | JCSassert _ | JCSassign_var _ | JCSthrow(_,None)
      | JCSassign_heap _ | JCSpack _ | JCSunpack _ | JCSreturn_void ->
	  targets
  in
  let candidates = List.rev (collect targets s) in
  List.filter (fun target -> filter_asrt target.jc_target_assertion) candidates


(*****************************************************************************)
(* Performing abstract interpretation.                                       *)
(*****************************************************************************)
    
let rec test_assertion mgr pre a =
  let env = Abstract1.env pre in
  let rec extract_environment_and_dnf env a =
    match a.jc_assertion_node with
      | JCAtrue -> env,Dnf.true_
      | JCAfalse -> env,Dnf.false_
      | _ when is_constant_assertion a ->
	  (* 'constant' assertions (eg: 0 <= 1) do not have to be tested
	     (Nicolas) *)
	  env,Dnf.true_ 
      | JCArelation(t1,Bneq_int,t2) ->
	  let infa = raw_asrt(JCArelation(t1,Blt_int,t2)) in
	  let supa = raw_asrt(JCArelation(t1,Bgt_int,t2)) in
	  let env,dnf1 = extract_environment_and_dnf env infa in
	  let env,dnf2 = extract_environment_and_dnf env supa in
	  env,Dnf.make_or [dnf1;dnf2]
(* A VOIR AVEC NICOLAS. Yannick *)
(*       | JCArelation (t1, Bneq_pointer, t2)  *)
(* 	  when t2.jc_term_node = JCTconst JCCnull -> (\* case <t != null> *\) *)
(* 	  let si = struct_of_term t1 in *)
(* 	  let offset_mint = term_no_loc (JCToffset (Offset_min, t1, si)) integer_type in *)
(* 	  let offset_mina = raw_asrt (JCArelation (offset_mint, Ble_int, zerot)) in *)
(* 	  let offset_maxt = term_no_loc (JCToffset (Offset_max, t1, si)) integer_type in *)
(* 	  let offset_maxa = raw_asrt (JCArelation (offset_maxt, Bge_int, zerot)) in *)
(* 	  let a = raw_asrt (JCAand [offset_mina; offset_maxa]) in *)
(* 	  extract_environment_and_dnf env a *)
      | JCArelation _ ->
	  let env, be = linstr_of_assertion env a in
	  let env, bemin = offset_min_linstr_of_assertion env a in
	  let env, bemax = offset_max_linstr_of_assertion env a in
	  let dnf = Dnf.make_and [be; bemin; bemax] in
	  env,dnf
      | JCAand al ->
	  List.fold_left (fun (env,dnf1) a ->
	    let env,dnf2 = extract_environment_and_dnf env a in
	    env,Dnf.make_and [dnf1;dnf2]
	  ) (env,Dnf.true_) al
      | JCAor al ->
	  List.fold_left (fun (env,dnf1) a ->
	    let env,dnf2 = extract_environment_and_dnf env a in
	    env,Dnf.make_or [dnf1;dnf2]
	  ) (env,Dnf.false_) al
      | JCAnot a ->
	  let nota = not_asrt a in
	  begin match nota.jc_assertion_node with
	    | JCAnot _ -> env, Dnf.true_
	    | _ -> extract_environment_and_dnf env nota
	  end
      | JCAapp (li, tl) ->
	  if debug then printf "[test_assertion] %a@." Jc_output.assertion a;
	  if li.jc_logic_info_name = "full_separated" then env,Dnf.true_ else
	    let _, term_or_assertion = 
	      try Hashtbl.find Jc_typing.logic_functions_table li.jc_logic_info_tag
	      with Not_found -> assert false 
	    in
	    begin
	      match term_or_assertion with
		| JCAssertion a ->
		    let a = List.fold_left2
		      (fun a vi t ->
			replace_vi_in_assertion vi t a)
		      a li.jc_logic_info_parameters tl
		    in
		    extract_environment_and_dnf env a
		| _ -> env, Dnf.true_
	    end
      | JCAimplies _ | JCAiff _
      | JCAquantifier _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
      | JCAif _ | JCAmutable _ | JCAtagequality _ -> env,Dnf.true_
  in
  let env, dnf = extract_environment_and_dnf env a in
  Abstract1.change_environment_with mgr pre env false;
  Dnf.test mgr pre dnf
    
let test_expr ~(neg:bool) mgr pre e =
  let a = asrt_of_expr e in
  let a = if neg then not_asrt a else a in
  test_assertion mgr pre a

(* Assigns expression [e] to abstract variable [va] in abstract value [pre]. *)
let assign_variable mgr pre va e =
  let env0 = Abstract1.env pre in
  let env = 
    if Environment.mem_var env0 va then env0 
    else Environment.add env0 [|va|] [||] 
  in
  match linstr_of_expr env e with
    | Some(env,str) ->
	
	if debug then printf "[assign_variable] str %s@." str;

	(* Assignment can be treated precisely. *)
	let lin = 
	  try Parser.linexpr1_of_string env str
	  with Parser.Error msg -> printf "%s@." msg; assert false
	in
	Abstract1.change_environment_with mgr pre env false;
	Abstract1.assign_linexpr_with mgr pre va lin None
    | None ->

	if debug then printf "[assign_variable] no str@.";

	(* Try over-approximate treatment of assignment. *)
	if Environment.mem_var env0 va then
	  Abstract1.forget_array_with mgr pre [|va|] false;
	match term_of_expr e with
	  | Some te ->
	      (* Assignment treated as an equality test. *)
	      let t = Vai.term va in
	      let a = raw_asrt(JCArelation(t,Beq_int,te)) in
	      test_assertion mgr pre a
	  | None ->
	      (* Assignment treated as a forget operation. *)
	      ()

let assign_offset_variable mgr pre va ok e =
  let env0 = Abstract1.env pre in
  let env = 
    if Environment.mem_var env0 va then env0 
    else Environment.add env0 [|va|] [||] 
  in
  let forget_vars = [] in
  let forget_vars = Array.of_list forget_vars in
  Abstract1.forget_array_with mgr pre forget_vars false;
  match offset_linstr_of_expr env ok e with
    | Some(env,str) ->
	(* Assignment can be treated precisely. *)
	let lin = 
	  try Parser.linexpr1_of_string env str
	  with Parser.Error msg -> printf "%s@." msg; assert false
	in
	Abstract1.change_environment_with mgr pre env false;
	Abstract1.assign_linexpr_with mgr pre va lin None
    | None ->
	(* Assignment treated as a forget operation. *)
	if Environment.mem_var env0 va then
	  Abstract1.forget_array_with mgr pre [|va|] false
	    
let assign_expr mgr pre t e =
  (* Choice: terms that depend on the term assigned to are removed from
     the abstract value -before- treating the assignment. *)
  let env = Abstract1.env pre in
  let integer_vars = Array.to_list (fst (Environment.vars env)) in
  let forget_vars = 
    List.filter (fun va' ->
      let t' = Vai.term va' in 
      (not (raw_term_equal t t')) && term_depends_on_term t' t
    ) integer_vars
  in
  let forget_vars = Array.of_list forget_vars in
  Abstract1.forget_array_with mgr pre forget_vars false;
  (* Propagate knowledge on abstract variables on the rhs of the assignment
     to equivalent abstract variables on the lhs. *)
  begin match term_of_expr e with
    | None -> ()
    | Some te ->
	let constr_vars = 
	  List.filter (fun va -> 
	    not (Abstract1.is_variable_unconstrained mgr pre va = Manager.True)
	  ) integer_vars
	in
	List.iter (fun va' ->
	  let t' = Vai.term va' in
	  if raw_strict_sub_term te t' then 
	    let lhst = 
	      replace_term_in_term ~source:te ~target:t.jc_term_node t' 
	    in
	    let a = raw_asrt(JCArelation(lhst,Beq_int,t')) in
	    test_assertion mgr pre a
	) constr_vars
  end;
  (* Assign abstract variables. *)
  if Vai.has_variable t then
    assign_variable mgr pre (Vai.variable t) e;
  if Vai.has_offset_min_variable t then
    begin
      let va = Vai.offset_min_variable t in
      assign_offset_variable mgr pre va Offset_min_kind e
    end;
  if Vai.has_offset_max_variable t then
    begin
      let va = Vai.offset_max_variable t in
      assign_offset_variable mgr pre va Offset_max_kind e
    end

let meet mgr val1 val2 =
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  Abstract1.change_environment_with mgr val1 env false;
  Abstract1.change_environment_with mgr val2 env false;
  Abstract1.meet_with mgr val1 val2

let join mgr val1 val2 =
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  Abstract1.change_environment_with mgr val1 env false;
  Abstract1.change_environment_with mgr val2 env false;
  Abstract1.join_with mgr val1 val2

let join_abstract_value mgr pair1 pair2 =
  join mgr pair1.jc_absval_regular pair2.jc_absval_regular;
  join mgr pair1.jc_absval_propagated pair2.jc_absval_propagated

let join_invariants mgr invs1 invs2 =
  if Jc_options.debug then
    printf "@[<v 2>[join]@\n%a@\nand@\n%a@]@." 
      print_abstract_invariants invs1 print_abstract_invariants invs2;
  let join_exclists postexcl1 postexcl2 =
    let join1 = List.fold_right (fun (ei,post1) acc ->
      try
	let post2 = List.assoc ei postexcl2 in
	join_abstract_value mgr post1 post2;
	(ei, post1) :: acc
      with Not_found -> (ei,post1) :: acc
    ) postexcl1 []
    in
    List.fold_right (fun (ei,post2) acc ->
      if List.mem_assoc ei join1 then acc 
      else (ei, post2) :: acc
    ) postexcl2 join1
  in
  assert (invs1.jc_absinv_return == invs2.jc_absinv_return);
  join_abstract_value mgr invs1.jc_absinv_normal invs2.jc_absinv_normal;
  invs1.jc_absinv_exceptional <-
    join_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional

(* Returns the widened value as there is no destructive version of [widening]
 * in [Abstract1]. *)
let widening mgr val1 val2 =
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  Abstract1.change_environment_with mgr val1 env false;
  Abstract1.change_environment_with mgr val2 env false;
  (* Join before widening so that arguments are in increasing order. *)
  Abstract1.join_with mgr val2 val1;
  (* Perform widening between values in increasing order. *)
  Abstract1.widening mgr val1 val2 

let widening_abstract_value mgr pair1 pair2 =
  pair1.jc_absval_regular <-
    widening mgr pair1.jc_absval_regular pair2.jc_absval_regular;
  pair1.jc_absval_propagated <-
    widening mgr pair1.jc_absval_propagated pair2.jc_absval_propagated

let widen_invariants mgr invs1 invs2 =
  if Jc_options.debug then
    printf "@[<v 2>[widening]@\n%a@\nand@\n%a@]@." 
      print_abstract_invariants invs1 print_abstract_invariants invs2;
  let widen_exclists postexcl1 postexcl2 =
    let widen1 = List.fold_right (fun (ei,post1) acc ->
      try
	let post2 = List.assoc ei postexcl2 in
	widening_abstract_value mgr post1 post2;
	(ei, post1) :: acc
      with Not_found -> (ei,post1) :: acc
    ) postexcl1 []
    in
    List.fold_right (fun (ei,post2) acc ->
      if List.mem_assoc ei widen1 then acc 
      else (ei, post2) :: acc
    ) postexcl2 widen1
  in
  assert (invs1.jc_absinv_return == invs2.jc_absinv_return);
  widening_abstract_value mgr invs1.jc_absinv_normal invs2.jc_absinv_normal;
  invs1.jc_absinv_exceptional <-
    widen_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional

let empty mgr val1 =
  let bot = Abstract1.bottom mgr (Abstract1.env val1) in
  Abstract1.meet_with mgr val1 bot

let empty_abstract_value mgr pair1 =
  empty mgr pair1.jc_absval_regular;
  empty mgr pair1.jc_absval_propagated

let is_eq mgr val1 val2 =
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  Abstract1.change_environment_with mgr val1 env false;
  Abstract1.change_environment_with mgr val2 env false;
  Abstract1.is_eq mgr val1 val2 = Manager.True

let eq_abstract_value mgr absval1 absval2 =
  is_eq mgr absval1.jc_absval_regular absval2.jc_absval_regular
  && is_eq mgr absval1.jc_absval_propagated absval2.jc_absval_propagated

let eq_invariants mgr invs1 invs2 =
  let eq_exclists postexcl1 postexcl2 =
    List.length postexcl1 = List.length postexcl2 &&
    List.fold_right (fun (ei,post1) acc ->
      acc &&
	try
	  let post2 = List.assoc ei postexcl2 in
	  eq_abstract_value mgr post1 post2
	with Not_found -> false
    ) postexcl1 true
  in
  assert (invs1.jc_absinv_return == invs2.jc_absinv_return);
  eq_abstract_value mgr invs1.jc_absinv_normal invs2.jc_absinv_normal
  && eq_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional

let copy_abstract_value mgr absval =
  {
    jc_absval_regular = Abstract1.copy mgr absval.jc_absval_regular;
    jc_absval_propagated = Abstract1.copy mgr absval.jc_absval_propagated;
  }

let copy_invariants mgr invs = { 
  jc_absinv_normal = copy_abstract_value mgr invs.jc_absinv_normal;
  jc_absinv_exceptional = 
    List.map (fun (ei,post) -> (ei,copy_abstract_value mgr post)) 
      invs.jc_absinv_exceptional;
  jc_absinv_return = invs.jc_absinv_return;
}

let forget mgr val1 vls =
  let vls = List.filter (Environment.mem_var (Abstract1.env val1)) vls in
  let varr = Array.of_list vls in
  Abstract1.forget_array_with mgr val1 varr false

let forget_abstract_value mgr absval vls =
  forget mgr absval.jc_absval_regular vls;
  forget mgr absval.jc_absval_propagated vls

let forget_invariants mgr invs vls =
  forget_abstract_value mgr invs.jc_absinv_normal vls;
  List.iter (fun (ei,post) -> forget_abstract_value mgr post vls)
    invs.jc_absinv_exceptional

let bottom_abstract_value mgr env =
  { 
    jc_absval_regular = Abstract1.bottom mgr env;
    jc_absval_propagated = Abstract1.bottom mgr env;
  }

let top_abstract_value mgr env =
  { 
    jc_absval_regular = Abstract1.top mgr env;
    jc_absval_propagated = Abstract1.top mgr env;
  }

let ai_inter_function_call mgr iai abs pre fi el =
  let formal_vars =
    List.fold_left2
      (fun (acc) vi e ->
	let t = term_var_no_loc vi in
	let acc = if Vai.has_variable t then 
	  (Vai.variable t)::acc else acc in
	let acc = if Vai.has_offset_min_variable t then
	  (Vai.offset_min_variable t)::acc else acc in
	let acc = if Vai.has_offset_max_variable t then
	  (Vai.offset_max_variable t)::acc else acc in
        assign_expr mgr pre t e; acc)
      [] fi.jc_fun_info_parameters el
  in
  let formal_vars = Array.of_list formal_vars in
  let env = try Environment.make formal_vars [||] with _ -> assert false in
  let pre = try 
    Abstract1.change_environment mgr pre env false 
  with _ -> assert false in
  let function_preconditions = iai.jc_interai_function_preconditions in
  let function_pre = try 
    Hashtbl.find function_preconditions fi.jc_fun_info_tag 
  with Not_found -> Abstract1.bottom mgr env in
  begin
    let old_pre = Abstract1.copy mgr function_pre in
    join mgr function_pre pre;
    if not (is_eq mgr old_pre function_pre) then
      state_changed := true;
    Hashtbl.replace function_preconditions fi.jc_fun_info_tag function_pre;
  end
    
let find_target_assertions targets s =
  List.fold_left 
    (fun acc target -> 
      if target.jc_target_statement == s then target::acc else acc
    ) [] targets
    
(* External function to call to perform abstract interpretation [abs] 
 * on statement [s], starting from invariants [curinvs]. 
 * It sets the initial value of invariants before treating a loop.
 *)
let rec ai_statement iaio abs curinvs s =
  let mgr = abs.jc_absint_manager in
  let loop_initial_invariants = abs.jc_absint_loop_initial_invariants in
  let loop_invariants = abs.jc_absint_loop_invariants in
  let loop_iterations = abs.jc_absint_loop_iterations in
  match s.jc_statement_node with
    | JCSloop (la, ls) ->
	(* Reinitialize the loop iteration count and the loop invariant.
	 * Comment those lines to gain in scaling, at the cost of less precision.
	 *)
	Hashtbl.replace loop_iterations la.jc_loop_tag 0;
	Hashtbl.remove loop_invariants la.jc_loop_tag;
	(* Set the initial value of invariants when entering the loop from 
	 * the outside. 
	 *)
	Hashtbl.replace 
	  loop_initial_invariants la.jc_loop_tag (copy_invariants mgr curinvs);
	intern_ai_statement iaio abs curinvs s 
    | _ -> intern_ai_statement iaio abs curinvs s 
	
(* Internal function called when computing a fixpoint for a loop. It does not
 * modify the initial value of invariants for the loop considered, so that 
 * narrowing is possible.
 *)
and intern_ai_statement iaio abs curinvs s =
  let mgr = abs.jc_absint_manager in
  (* Define common shortcuts. *)
  let normal = curinvs.jc_absinv_normal in
  let pre = normal.jc_absval_regular in
  let prop = normal.jc_absval_propagated in
  let postexcl = curinvs.jc_absinv_exceptional in
  let postret = curinvs.jc_absinv_return in
  (* Record invariant at assertion points. *)
  let targets = find_target_assertions abs.jc_absint_target_assertions s in
  List.iter
    (fun target ->
      target.jc_target_regular_invariant <- mkinvariant mgr pre;
      target.jc_target_propagated_invariant <- mkinvariant mgr prop
    ) targets;
  (* Apply appropriate transition function. *)
  begin match s.jc_statement_node with
    | JCSdecl (vi, None, s) ->
	ai_statement iaio abs curinvs s
    | JCSdecl (vi, Some e, s) ->
	assign_expr mgr pre (term_var_no_loc vi) e;
	ai_statement iaio abs curinvs s;
        (* To keep information on variable [vi], declaration should be turned
	 * into assignment before analysis.
	 *)
        forget_invariants mgr curinvs (Vai.all_variables (term_var_no_loc vi))
    | JCSassign_var (vi, e) ->
	assign_expr mgr pre (term_var_no_loc vi) e
    | JCSassign_heap(e1,fi,e2) ->
	begin match term_of_expr e1 with
	  | None -> () (* TODO *)
	  | Some t1 ->
	      let dereft = term_no_loc (JCTderef(t1,fi)) fi.jc_field_info_type in
	      assign_expr mgr pre dereft e2
	end
    | JCSassert a ->
	test_assertion mgr pre a
    | JCSblock sl ->
	List.iter (ai_statement iaio abs curinvs) sl
    | JCSif (e, ts, fs) ->
	let asrts = collect_expr_asserts e in 
	List.iter (test_assertion mgr prop) asrts;
	let copyinvs = copy_invariants mgr curinvs in
	(* Treat "then" branch. *)
	test_expr ~neg:false mgr pre e;
	ai_statement iaio abs curinvs ts;
	(* Treat "else" branch. *)
	let copy_pre = copyinvs.jc_absinv_normal.jc_absval_regular in
	test_expr ~neg:true mgr copy_pre e;
	ai_statement iaio abs copyinvs fs;
	(* Join both branches. *)
	join_invariants mgr curinvs copyinvs
    | JCSreturn_void ->
	join_abstract_value mgr !postret normal;
	empty_abstract_value mgr normal
    | JCSreturn (t, e) ->
	let asrts = collect_expr_asserts e in
	List.iter (test_assertion mgr prop) asrts;
	(* <return e;> is logically equivalent to <\result = e;> *)
	let vit = term_var_no_loc (Jc_pervasives.var ~unique:false t "\\result") in
	assign_expr mgr pre vit e;
	join_abstract_value mgr !postret normal;
	empty_abstract_value mgr normal;
    | JCSthrow(ei,eopt) ->
	begin match eopt with
	  | None -> ()
	  | Some e ->
	      let asrts = collect_expr_asserts e in
	      List.iter (test_assertion mgr prop) asrts
	end;
	(* TODO: add thrown value as abstract variable. *)
	begin 
	  try join_abstract_value mgr normal (List.assoc ei postexcl)
	  with Not_found -> () 
	end;
	let copy_normal = copy_abstract_value mgr normal in
	let postexcl = (ei, copy_normal) :: (List.remove_assoc ei postexcl) in
	curinvs.jc_absinv_exceptional <- postexcl; 
	empty_abstract_value mgr normal
    | JCSpack _ | JCSunpack _ ->
	()
    | JCStry(s,hl,fs) ->
	ai_statement iaio abs curinvs s;
	let postexcl = curinvs.jc_absinv_exceptional in
	(* Filter out exceptions present in [hl]. *)
	let curpostexcl =
	  List.filter (fun (ei,_) ->
	    not (List.exists (fun (ej,_,_) ->
	      ei.jc_exception_info_tag = ej.jc_exception_info_tag) hl)) postexcl
	in
	curinvs.jc_absinv_exceptional <- curpostexcl;
	(* Consider each handler in turn. *)
	List.iter 
	  (fun (ei,_,s) ->
	    try
	      let postexc = List.assoc ei postexcl in
	      let excinvs = {
		jc_absinv_normal = postexc;
		jc_absinv_exceptional = [];
		jc_absinv_return = postret;
	      } in
	      ai_statement iaio abs excinvs s;
	      join_invariants mgr curinvs excinvs
	    with Not_found -> ()
	  ) hl;
	(* BAD: ai_statement abs curinvs fs *)
	begin match fs.jc_statement_node with 
	  | JCSblock [] -> ()
	  | _ -> assert false (* TODO: apply finally stmt to all paths. *)
	end
    | JCSloop (la, ls) ->
	let loop_invariants = abs.jc_absint_loop_invariants in
	let loop_initial_invariants = abs.jc_absint_loop_initial_invariants in
	let loop_iterations = abs.jc_absint_loop_iterations in
	let num = 
	  try Hashtbl.find loop_iterations la.jc_loop_tag 
	  with Not_found -> 0
	in
	Hashtbl.replace loop_iterations la.jc_loop_tag (num + 1);
	if num < abs.jc_absint_widening_threshold then
	  let nextinvs = copy_invariants mgr curinvs in
	  (* Perform one step of propagation through the loop body. *)
	  ai_statement iaio abs nextinvs ls;
	  join_invariants mgr curinvs nextinvs;
	  (* Perform fixpoint computation on the loop. *)
	  intern_ai_statement iaio abs curinvs s
	else
	  begin try
	    let loopinvs = Hashtbl.find loop_invariants la.jc_loop_tag in
	    let wideninvs = copy_invariants mgr loopinvs in
	    widen_invariants mgr wideninvs curinvs;
	    if eq_invariants mgr loopinvs wideninvs then
	      begin 
		(* Fixpoint reached through widening. Perform narrowing now. *)
		let initinvs = 
		  Hashtbl.find loop_initial_invariants la.jc_loop_tag in
		wideninvs.jc_absinv_exceptional <- [];
		(* TODO: be more precise on return too. *)
		ai_statement iaio abs wideninvs ls;
		join_invariants mgr wideninvs initinvs;
		Hashtbl.replace 
		  loop_invariants la.jc_loop_tag (copy_invariants mgr wideninvs);
		wideninvs.jc_absinv_exceptional <- initinvs.jc_absinv_exceptional;
		(* TODO: be more precise on return too. *)
		ai_statement iaio abs wideninvs ls;
		(* This is an infinite loop, whose only exit is through return or
		   throwing exceptions. *)
		empty_abstract_value mgr normal;
		curinvs.jc_absinv_exceptional <- wideninvs.jc_absinv_exceptional;
	      end
	    else
	      begin
		Hashtbl.replace 
		  loop_invariants la.jc_loop_tag (copy_invariants mgr wideninvs);
		(* Perform one step of propagation through the loop body. *)
		ai_statement iaio abs wideninvs ls;
		(* Perform fixpoint computation on the loop. *)
		intern_ai_statement iaio abs wideninvs s;
		(* Propagate changes to [curinvs]. *)
		empty_abstract_value mgr normal;
		join_abstract_value mgr normal wideninvs.jc_absinv_normal;
		curinvs.jc_absinv_exceptional <- wideninvs.jc_absinv_exceptional
	      end
	  with Not_found ->
	    Hashtbl.replace 
	      loop_invariants la.jc_loop_tag (copy_invariants mgr curinvs);
	    (* Perform one step of propagation through the loop body. *)
	    ai_statement iaio abs curinvs ls;
	    (* Perform fixpoint computation on the loop. *)
	    intern_ai_statement iaio abs curinvs s
	  end
    | JCScall (vio, call, s) ->
	let fi = call.jc_call_fun in
	let el = call.jc_call_args in
	if Jc_options.interprocedural then
	  begin match iaio with
	    | None -> () (* last iteration: precondition for [fi] already inferred *)
	    | Some iai -> 
		let copy_pre = Abstract1.copy mgr pre in
		  ai_inter_function_call mgr iai abs copy_pre fi el;
	  end;
	(* add postcondition of [fi] to pre *)
	let _,_,fs,_ = 
          Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag 
        in
	let normal_behavior =
	  List.fold_left
	    (fun acc (_,_,b) ->
	       (* TODO : handle 'assumes' clauses correctly *)
	       if b.jc_behavior_throws = None && b.jc_behavior_assumes = None then
		 make_and [b.jc_behavior_ensures; acc] else acc)
	    true_assertion
	    fs.jc_fun_behavior
	in
	let normal_behavior = 
	  match vio with
	    | None -> normal_behavior
	    | Some vi ->
		let result_vi = 
                  Jc_pervasives.var ~unique:false vi.jc_var_info_type "\\result"
                in
		let normal_behavior =
		  switch_vis_in_assertion result_vi vi normal_behavior 
		in
		  (* add result type spec to [fi] postcondition *)
		let cstrs = Jc_typing.type_range_of_term vi.jc_var_info_type (term_var_no_loc vi) in
		  make_and [normal_behavior; cstrs];
	in
	let normal_behavior =
	  List.fold_left2 
	    (fun a e vi -> 
	       let t = term_of_expr e in
		 match t with
		   | None -> assert false
		   | Some t -> replace_vi_in_assertion vi t a)
	    normal_behavior el fi.jc_fun_info_parameters 
	in
	test_assertion mgr pre normal_behavior;
	(* TODO: handle exceptional behaviors as well *)
	ai_statement iaio abs curinvs s;
        (* To keep information on variable [vi], declaration should be turned
	 * into assignment before analysis.
	 *)
        match vio with None -> () | Some vi ->
          forget_invariants mgr curinvs (Vai.all_variables (term_var_no_loc vi))
  end;
  let normal = curinvs.jc_absinv_normal in
  let prop = normal.jc_absval_propagated in
  let asrts = collect_statement_asserts s in
    List.iter (test_assertion mgr prop) asrts

let rec record_ai_invariants abs s =
  let mgr = abs.jc_absint_manager in
  match s.jc_statement_node with
    | JCSdecl(_,_,s) -> 
	record_ai_invariants abs s
    | JCSblock sl ->
	List.iter (record_ai_invariants abs) sl
    | JCSif(_,ts,fs) ->
	record_ai_invariants abs ts;
	record_ai_invariants abs fs
    | JCStry(s,hl,fs) ->
	record_ai_invariants abs s;
	List.iter (fun (_,_,s) -> record_ai_invariants abs s) hl;
	record_ai_invariants abs fs
    | JCSloop(la,ls) ->
	let loop_invariants = abs.jc_absint_loop_invariants in
	begin try
	  let loopinvs = Hashtbl.find loop_invariants la.jc_loop_tag in
	  let loopinv = loopinvs.jc_absinv_normal.jc_absval_regular in
	  (* Abstract1.minimize mgr loopinv; NOT IMPLEMENTED IN APRON *)
	  if Abstract1.is_top mgr loopinv = Manager.True then ()
	  else if Abstract1.is_bottom mgr loopinv = Manager.True then
	    la.jc_loop_invariant <- raw_asrt JCAfalse
	  else
	    let a = mkinvariant mgr loopinv in
	    if Jc_options.verbose then
	      printf 
		"%a@[<v 2>Inferring loop invariant@\n%a@]@."
		Loc.report_position s.jc_statement_loc
		Jc_output.assertion a;
	    la.jc_loop_invariant <- make_and [la.jc_loop_invariant; a];
	    record_ai_invariants abs ls
	with Not_found -> () end
    | JCSassign_var _ | JCSassign_heap _ | JCSassert _ 
    | JCSreturn_void | JCSreturn _ | JCSthrow _ | JCSpack _ | JCSunpack _  
    | JCScall _ -> ()
	
let ai_function mgr iaio targets (fi, fs, sl) =
  try
    let env = Environment.make [||] [||] in
    
    (* Add global variables as abstract variables in [env]. *)
    let globvars =
      Hashtbl.fold (fun _ (vi, _) acc -> Vai.all_variables (term_var_no_loc vi) @ acc)
	Jc_norm.variables_table []
    in
    let env = Environment.add env (Array.of_list globvars) [||] in
    
    (* Add \result as abstract variable in [env] if any. *)
    let return_type = fi.jc_fun_info_return_type in
    let vi_result = Jc_pervasives.var ~unique:false return_type "\\result" in
    let env =
      if return_type <> JCTnull then
	let result = Vai.all_variables (term_var_no_loc vi_result) in
	Environment.add env (Array.of_list result) [||]
      else env in

    let extern_env = env in

    (* Add parameters as abstract variables in [env]. *)
    let params =
      List.fold_left
	(fun acc vi -> Vai.all_variables (term_var_no_loc vi) @ acc)
	[] fi.jc_fun_info_parameters
    in
    
    let env = Environment.add env (Array.of_list params) [||] in
    
    let abs = { 
      jc_absint_manager = mgr;
      jc_absint_function_environment = env;
      jc_absint_function_name = fi.jc_fun_info_name;
      jc_absint_widening_threshold = 1;
      jc_absint_loop_invariants = Hashtbl.create 0;
      jc_absint_loop_initial_invariants = Hashtbl.create 0;
      jc_absint_loop_iterations = Hashtbl.create 0;
      jc_absint_loop_entry_invs = Hashtbl.create 0;
      jc_absint_target_assertions = targets;
    } in
    
    (* Add parameters specs to the function precondition *)
    let cstrs =
      List.fold_left
 	(fun acc vi -> Jc_typing.type_range_of_term vi.jc_var_info_type (term_var_no_loc vi) :: acc) 
	[] fi.jc_fun_info_parameters
    in
    fs.jc_fun_requires <- make_and (fs.jc_fun_requires :: cstrs);
    (* Take the function precondition as init pre *)
    let initpre = top_abstract_value mgr env in
    test_assertion mgr initpre.jc_absval_regular fs.jc_fun_requires;

    (* Add the currently inferred pre for [fi] in pre *)
    (match iaio with
      | None -> ()
      | Some iai ->
	  let inferred_pre =
	    try Hashtbl.find iai.jc_interai_function_preconditions fi.jc_fun_info_tag 
	    with Not_found -> Abstract1.top mgr env (* for main function *) in
	  meet mgr initpre.jc_absval_regular inferred_pre);

    (* Annotation inference on the function body. *)
    let invs = {
      jc_absinv_normal = initpre;
      jc_absinv_exceptional = [];
      jc_absinv_return = ref (bottom_abstract_value mgr env);
    } in
    List.iter (ai_statement iaio abs invs) sl;
    (* [iaio] is equal to [None] in two cases:
       1) intraprocedural analysis
       2) last iteration of interprocedural analysis
       (i.e. inference of loop invariant once preconditions have been inferred) *)
    if iaio = None then
      List.iter (record_ai_invariants abs) sl;
    List.iter 
      (fun target -> 
	if Jc_options.verbose then
	  printf 
	    "%a@[<v 2>Inferring assert invariant@\n%a@]@."
	    Loc.report_position target.jc_target_location
	    Jc_output.assertion target.jc_target_regular_invariant 
      ) targets;

    (* Require isolation of parameters written through. *)
    let write_params = 
      fi.jc_fun_info_effects.jc_writes.jc_effect_through_params
    in
    let read_params = 
      fi.jc_fun_info_effects.jc_reads.jc_effect_through_params
    in
    let read_params = VarSet.diff read_params write_params in
    let write_params = VarSet.fold (fun v acc -> v::acc) write_params [] in
    let read_params = VarSet.fold (fun v acc -> v::acc) read_params [] in
(*     let rec write_sep_pred acc = function *)
(*       | v::r -> *)
(* 	  List.fold_left (fun acc v2 -> *)
(* 	    raw_asrt(JCAapp( *)
(* 	      full_separated,[term_var_no_loc v;term_var_no_loc v2])) *)
(* 	    :: acc *)
(* 	  ) acc (r @ read_params) *)
(*       | [] -> acc *)
(*     in *)
(*     let sep_preds = write_sep_pred [] write_params in *)
(*     fs.jc_fun_requires <- make_and(fs.jc_fun_requires :: sep_preds); *)
    
    (* record the inferred postcondition *)
    if iaio = None then
      let returnabs = !(invs.jc_absinv_return).jc_absval_regular in
      if Abstract1.is_top mgr returnabs = Manager.True 
	|| Abstract1.is_bottom mgr returnabs = Manager.True then
	  ()
      else
	let returnabs = Abstract1.change_environment mgr returnabs extern_env false in
	let returna = mkinvariant abs.jc_absint_manager returnabs in
	let post = make_and 
	  [returna; Jc_typing.type_range_of_term vi_result.jc_var_info_type (term_var_no_loc vi_result)] in
	let normal_behavior = { default_behavior with jc_behavior_ensures = post } in
	let excl, excabsl =
	  List.fold_left
	    (fun (acc1, acc2) (exc, va) -> (exc :: acc1, va.jc_absval_regular :: acc2))
	    ([], []) invs.jc_absinv_exceptional in
	let excabsl = List.map
	  (fun va -> Abstract1.change_environment mgr va extern_env false) excabsl in
	let excabsl = List.map
	  (fun va -> if Abstract1.is_bottom mgr va = Manager.True then
	    Abstract1.top mgr env else va) excabsl in
	let excal = List.map (mkinvariant abs.jc_absint_manager) excabsl in
	let exc_behaviors = 
	  List.map2 
	    (fun exc va ->
	      (Loc.dummy_position,"safety",
	      { default_behavior with 
		jc_behavior_throws = Some exc; 
		jc_behavior_ensures = va }))
	    excl excal in
	if Jc_options.verbose then
	  begin
	    printf
	      "@[<v 2>Inferring postcondition@\n%a@]@."
	      Jc_output.assertion post;
	    List.iter2
	      (fun exc exca -> printf
		"@[<v 2>Inferring postcondition for exception %s@\n%a@]@."
		exc.jc_exception_info_name
		Jc_output.assertion exca) excl excal;
	  end;
	begin
	  try
	    let (_,s,b) = List.find (fun (_,s,_) -> s = "safety") fs.jc_fun_behavior in
	    b.jc_behavior_ensures <- make_and [b.jc_behavior_ensures; post];
	  with Not_found -> 
	    if is_purely_exceptional_fun fs then () else
	    fs.jc_fun_behavior <- 
	      (Loc.dummy_position,"safety", normal_behavior) :: fs.jc_fun_behavior
	end;
	fs.jc_fun_behavior <- exc_behaviors @ fs.jc_fun_behavior
    else ()
      
  with Manager.Error exc ->
    Manager.print_exclog std_formatter exc;
    printf "@.";
    exit 1

      

(*****************************************************************************)
(* From terms and assertions to ATP formulas and the opposite way.           *)
(*****************************************************************************)

module Vwp : sig

  val variable : term -> string
  val offset_min_variable : term -> struct_info -> string
  val offset_max_variable : term -> struct_info -> string

  val term : string -> term

end = struct

  let variable_table = Hashtbl.create 0
  let offset_min_variable_table = Hashtbl.create 0
  let offset_max_variable_table = Hashtbl.create 0
  let term_table = Hashtbl.create 0

  let variable t = 
    let s = term_name t in
    begin try 
      let t2 = Hashtbl.find variable_table s in
      (*       printf "s = %s t = %a t2 = %a@." s Jc_output.term t Jc_output.term t2; *)
      assert (raw_term_compare t t2 = 0)
    with Not_found ->
      Hashtbl.add variable_table s t;
      Hashtbl.add term_table s t
    end;
    s

  let offset_min_variable t st = 
    let s = "__jc_offset_min_" ^ (term_name t) in
    begin try 
      let t2 = Hashtbl.find offset_min_variable_table s in
      assert (raw_term_compare t t2 = 0)
    with Not_found ->
      Hashtbl.add offset_min_variable_table s t;
      let tmin = term_no_loc (JCToffset(Offset_min,t,st)) integer_type in
      Hashtbl.add term_table s tmin
    end;
    s

  let offset_max_variable t st = 
    let s = "__jc_offset_max_" ^ (term_name t) in
    begin try 
      let t2 = Hashtbl.find offset_max_variable_table s in
      if debug then printf "%a,%a@." Jc_output.term t Jc_output.term t2;
      assert (raw_term_compare t t2 = 0)
    with Not_found ->
      Hashtbl.add offset_max_variable_table s t;
      let tmax = term_no_loc (JCToffset(Offset_max,t,st)) integer_type in
      Hashtbl.add term_table s tmax
    end;
    s

  let term s = Hashtbl.find term_table s

end

let is_neq_binop = function
  | Bneq_int | Bneq_real | Bneq_pointer -> true
  | _ -> false

let atp_relation_of_binop = function
  | Blt_int | Blt_real -> "<"
  | Bgt_int | Bgt_real -> ">"
  | Ble_int | Ble_real -> "<="
  | Bge_int | Bge_real -> ">="
  | Beq_int | Beq_real | Beq_pointer -> "="
  | Bneq_int | Bneq_real | Bneq_pointer -> 
      assert false (* Should be treated as "not (t1 eq t2)". *)
  | _ -> assert false

let atp_arithmetic_of_binop = function
  | Badd_int | Badd_real -> "+"
  | Bsub_int | Bsub_real -> "-"
  | Bmul_int | Bmul_real -> "*"
  | _ -> failwith "Atp alien"

let rec free_variables t =
  fold_term
    (fun acc t -> match t.jc_term_node with
      | JCTvar vi ->
	  VarSet.add vi acc
      | _ -> acc
    ) VarSet.empty t

let rec atp_of_term t = 
  if debug then printf "[atp_of_term] %a@." Jc_output.term t;
  let is_constant_term t = 
    match t.jc_term_node with JCTconst _ -> true | _ -> false
  in
  match t.jc_term_node with
    | JCTconst c ->
	begin match c with
	  | JCCinteger s -> 
	      Atp.Fn(s,[])
	  | JCCnull  -> 
	      Atp.Var (Vwp.variable t)
	  | JCCboolean _ | JCCvoid | JCCreal _ -> 
	      assert false
	end
    | JCTbinary(t1,(Badd_int | Bsub_int as bop),t2) ->
	Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
    | JCTbinary(t1,(Bmul_int as bop),t2) 
	when (is_constant_term t1 || is_constant_term t2) ->
	Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
    | JCTbinary(t1,(Bdiv_int as bop),t2) when (is_constant_term t2) ->
	Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
    | JCTbinary(t1,bop,t2) ->
	Atp.Var (Vwp.variable t)
    | JCTunary(uop,t1) ->
	Atp.Fn(Jc_output.unary_op uop, [atp_of_term t1])
    | JCToffset(Offset_min,t,st) ->
	Atp.Var (Vwp.offset_min_variable t st)
    | JCToffset(Offset_max,t,st) ->
	Atp.Var (Vwp.offset_max_variable t st)
    | JCTvar _ | JCTderef _ | JCTapp _ | JCTsub_pointer _ ->
	Atp.Var (Vwp.variable t)
    | JCTshift _ | JCTold _
    | JCTinstanceof _ | JCTcast _ | JCTif _ | JCTrange _ ->
        failwith "Atp alien"
(*	assert false*)

let rec term_of_atp tm =
  match tm with
    | Atp.Var s -> 
	Vwp.term s
    | Atp.Fn("+",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,Badd_int,term_of_atp tm2) in
	term_no_loc tnode integer_type
    | Atp.Fn("-",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,Bsub_int,term_of_atp tm2) in
	term_no_loc tnode integer_type
    | Atp.Fn("*",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,Bmul_int,term_of_atp tm2) in
	term_no_loc tnode integer_type
    | Atp.Fn("/",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,Bdiv_int,term_of_atp tm2) in
	term_no_loc tnode integer_type
    | Atp.Fn("-",[tm1]) ->
	let tnode = JCTunary(Uminus_int,term_of_atp tm1) in
	term_no_loc tnode integer_type
    | Atp.Fn(s,[]) ->
	let tnode = JCTconst (JCCinteger s) in
	term_no_loc tnode integer_type
    | tm -> 
	printf "Unexpected ATP term %a@." (fun fmt tm -> Atp.printert tm) tm;
	assert false

let rec atp_of_asrt a = 
  if debug then printf "[atp_of_asrt] %a@." Jc_output.assertion a;
  try begin match a.jc_assertion_node with
    | JCAtrue -> 
	Atp.True
    | JCAfalse -> 
	Atp.False
    | JCArelation(t1,bop,t2) ->
	if is_neq_binop bop then
	  Atp.Not(Atp.Atom(Atp.R("=",List.map atp_of_term [t1;t2])))
	else
	  Atp.Atom(Atp.R(atp_relation_of_binop bop,List.map atp_of_term [t1;t2]))
    | JCAand al -> 
	let rec mkand = function
	  | [] -> Atp.True
	  | [a] -> atp_of_asrt a
	  | a :: al -> Atp.And (atp_of_asrt a, mkand al)
	in
	mkand al
    | JCAor al -> 
	let rec mkor = function
	  | [] -> Atp.False
	  | [a] -> atp_of_asrt a
	  | a :: al -> Atp.Or (atp_of_asrt a, mkor al)
	in
	mkor al
    | JCAimplies(a1,a2) ->
	Atp.Imp(atp_of_asrt a1,atp_of_asrt a2)
    | JCAiff(a1,a2) ->
	Atp.And
	  (Atp.Imp(atp_of_asrt a1,atp_of_asrt a2),
	  Atp.Imp(atp_of_asrt a2,atp_of_asrt a1))
    | JCAnot a ->
	Atp.Not(atp_of_asrt a)
    | JCAquantifier(q,vi,a) ->
	let f = atp_of_asrt a in
	let fvars = Atp.fv f in
	let varsets = List.map (fun v -> free_variables (Vwp.term v)) fvars in
	let vars = List.fold_left2
	  (fun acc va vs -> 
	    if VarSet.mem vi vs then StringSet.add va acc else acc) 
	  (StringSet.singleton vi.jc_var_info_name) fvars varsets
	in
	let vars = StringSet.elements vars in
	let rec quant f = function
	  | [] -> f
	  | v::r -> 
	      match q with 
		| Forall -> quant (Atp.Forall(v,f)) r
		| Exists -> quant (Atp.Exists(v,f)) r
	in
	quant f vars
    | JCAapp _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAtagequality _ ->
	failwith "Atp alien"
  end with Failure "Atp alien" -> 
    (* If alien appears in negative position, say in left-hand side of
     * implication, then we must assume conservatively it may be true, so that
     * the consequence of the implication must hold. Conversely, if alien 
     * appears in positive form, assuming it to be true allows to keep the 
     * other part of a conjunction. It should not be part of a positive 
     * disjunction. TODO
     *)
    Atp.True

let rec asrt_of_atp fm =
  let anode = match fm with
    | Atp.False ->
	JCAfalse
    | Atp.True ->
	JCAtrue
    | Atp.Atom(Atp.R("=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Beq_int,term_of_atp tm2)
    | Atp.Atom(Atp.R("<",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Blt_int,term_of_atp tm2)
    | Atp.Atom(Atp.R(">",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Bgt_int,term_of_atp tm2)
    | Atp.Atom(Atp.R("<=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Ble_int,term_of_atp tm2)
    | Atp.Atom(Atp.R(">=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Bge_int,term_of_atp tm2)
    | Atp.Atom _ ->
	printf "Unexpected ATP atom %a@." (fun fmt fm -> Atp.printer fm) fm;
	assert false
    | Atp.Not fm ->
	JCAnot (asrt_of_atp fm)
    | Atp.And(fm1,fm2) ->
	JCAand [asrt_of_atp fm1;asrt_of_atp fm2]
    | Atp.Or(fm1,fm2) ->
	JCAor [asrt_of_atp fm1;asrt_of_atp fm2]
    | Atp.Imp(fm1,fm2) ->
	JCAimplies(asrt_of_atp fm1,asrt_of_atp fm2)
    | Atp.Iff(fm1,fm2) ->
	JCAiff(asrt_of_atp fm1,asrt_of_atp fm2)
    | Atp.Forall _ | Atp.Exists _ -> 
	JCAtrue
  in
  raw_asrt anode


(*****************************************************************************)
(* Computing weakest preconditions.                                          *)
(*****************************************************************************)

let is_function_level posts =
  List.length posts.jc_post_modified_vars = 1

let add_modified_var posts v =
  let vars = match posts.jc_post_modified_vars with
    | vs :: r -> VarSet.add v vs :: r
    | [] -> assert false
  in
  { posts with jc_post_modified_vars = vars; }

let add_modified_vars posts vs =
  let vars = match posts.jc_post_modified_vars with
    | vs2 :: r -> VarSet.union vs vs2 :: r
    | [] -> assert false
  in
  { posts with jc_post_modified_vars = vars; }

let add_inflexion_var posts v =
  posts.jc_post_inflexion_vars :=
    VarSet.add v !(posts.jc_post_inflexion_vars)

let remove_modified_var posts v =
  let vars = match posts.jc_post_modified_vars with
    | vs :: r -> VarSet.remove v vs :: r
    | [] -> assert false
  in
  { posts with jc_post_modified_vars = vars; }

let push_modified_vars posts = 
  let vars = posts.jc_post_modified_vars in
  { posts with jc_post_modified_vars = VarSet.empty :: vars; }

let pop_modified_vars posts = 
  let vs,vars = match posts.jc_post_modified_vars with
    | vs :: r -> vs,r
    | [] -> assert false
  in
  vs,{ posts with jc_post_modified_vars = vars; }

let tautology a =
  let qf = Atp.generalize (atp_of_asrt a) in
  if Jc_options.debug then
    printf "@[<v 2>Before quantifier elimination@\n%a@]@." 
      (fun fmt fm -> Atp.printer fm) qf; 
  let dnf = Atp.dnf qf in
  if Jc_options.debug then
    printf "@[<v 2>After dnf@\n%a@]@." 
      (fun fmt fm -> Atp.printer fm) dnf; 
  if debug then printf "[before integer_qelim]@.";
  let qe = Atp.fourier_qelim qf in
  if debug then printf "[after integer_qelim]@.";
  let qe = asrt_of_atp qe in
  match qe.jc_assertion_node with
    | JCAtrue -> true
    | _ -> false

let contradictory a b =
  let res = tautology(make_not(make_and [a;b])) in
  if debug then 
    printf "@[<v 2>contradictory@\n%a@\n%a?%b@]@." 
      Jc_output.assertion a Jc_output.assertion b res;
  res

let simplify =
  let mgr = Polka.manager_alloc_strict () in
  fun inita inva ->
    let simpla = if tautology inita then raw_asrt JCAtrue else
      let dnf = Atp.dnf (atp_of_asrt inita) in
      let vars = Atp.fv dnf in
      let vars = List.map Vwp.term vars in
      let vars = List.map Vai.variable_of_term vars in
      let env = Environment.make (Array.of_list vars) [||] in
      let disjuncts = Atp.disjuncts dnf in
      let disjuncts = List.map Atp.conjuncts disjuncts in
      let disjuncts = List.map (List.map asrt_of_atp) disjuncts in

      let disjuncts =
	List.filter (fun conjunct ->
	  not(contradictory (make_and conjunct) inva)
	) disjuncts
      in

      let abstract_disjuncts,other_disjuncts = 
	List.fold_right (fun conjunct (abstractl,otherl) ->
	  try 
	    if Jc_options.debug then
	      printf "asrt conjunct : %a@."
		(Pp.print_list (fun fmt () -> printf " /\\ ") 
		  Jc_output.assertion)
		conjunct;
	    let absval = Abstract1.top mgr env in
	    (* Overapproximate conjunct. *)
	    let cstrs = List.map (linstr_of_assertion env) conjunct in
	    let cstrs = List.map snd cstrs in
	    let dnf = Dnf.make_and cstrs in
	    (* 	  if Jc_options.debug then *)
	    (* 	    printf "linstr conjunct : %a@."  *)
	    (* 	      (Pp.print_list (fun fmt () -> printf " /\\ ")  *)
	    (* 		 (fun fmt s -> print_string s)) *)
	    (* 	      cstrs; *)
	    Dnf.test mgr absval dnf;
	    if Jc_options.debug then
	      printf "abstract conjunct : %a@." Abstract1.print absval;
	    if (Abstract1.is_top mgr absval = Manager.True) then
	      failwith "Incorrect overapproximation";
	    if Abstract1.is_bottom mgr absval = Manager.True then
	      abstractl, otherl
	    else
	      absval :: abstractl, otherl
	  with Parser.Error _ | Failure _ ->
	    abstractl, make_and (List.map presentify conjunct) :: otherl
	) disjuncts ([],[])
      in
      let abstract_disjuncts = 
	List.fold_right (fun absval acc ->
	  let acc = List.filter 
	    (fun av -> not (Abstract1.is_leq mgr av absval = Manager.True)) acc
	  in
	  if List.exists 
	    (fun av -> Abstract1.is_leq mgr absval av = Manager.True) acc then acc
	  else absval :: acc
	) abstract_disjuncts []
      in
      List.iter (Abstract1.minimize mgr) abstract_disjuncts;
      let abstract_disjuncts = List.map (mkinvariant mgr) abstract_disjuncts in
      let disjuncts = abstract_disjuncts @ other_disjuncts in
      make_or disjuncts
    in
    if debug then
      printf "@[<v 2>[simplify] initial:@\n%a@]@." Jc_output.assertion inita;
    if debug then
      printf "@[<v 2>[simplify] w.r.t. invariant:@\n%a@]@." 
	Jc_output.assertion inva;
    if debug then
      printf "@[<v 2>[simplify] final:@\n%a@]@." Jc_output.assertion simpla;
    simpla

let quantif_eliminate qf finv =
  if Jc_options.debug then
    printf "@[<v 2>Raw precondition@\n%a@]@." Jc_output.assertion qf; 
  let qf = atp_of_asrt qf in
  if Jc_options.debug then
    printf "@[<v 2>Before quantifier elimination@\n%a@]@." 
      (fun fmt fm -> Atp.printer fm) qf; 
  let qf = Atp.pnf qf in
  match qf with
    | Atp.Forall _ | Atp.Exists _ ->
	let qe = Atp.fourier_qelim qf in
	if Jc_options.debug then
	  printf "@[<v 2>After quantifier elimination@\n%a@]@." 
	    (fun fmt fm -> Atp.printer fm) qe; 
	begin match qe with
	  | Atp.Not nqe ->
	      let qe = (Atp.dnf nqe) in
	      if Jc_options.debug then
		printf "@[<v 2>After negative disjunctive normal form@\n%a@]@." 
		  (fun fmt fm -> Atp.printer fm) qe;
	      let res = simplify (asrt_of_atp qe) (raw_asrt JCAtrue) in
	      let finv = asrt_of_atp (Atp.dnf (atp_of_asrt finv)) in
	      simplify (make_not res) finv
	  | _ ->
	      let qe = (Atp.dnf qe) in
	      if Jc_options.debug then
		printf "@[<v 2>After disjunctive normal form@\n%a@]@." 
		  (fun fmt fm -> Atp.printer fm) qe;
	      let finv = asrt_of_atp (Atp.dnf (atp_of_asrt finv)) in
	      simplify (asrt_of_atp qe) finv
	end
    | q -> 
	let finv = asrt_of_atp (Atp.dnf (atp_of_asrt finv)) in
	simplify (asrt_of_atp q) finv

let initialize_target curposts target =
  let collect_free_vars = 
    fold_term_and_assertion 
      (fun acc t -> match t.jc_term_node with
	| JCTvar vi -> VarSet.add vi acc
	| _ -> acc) 
      (fun acc a -> match a.jc_assertion_node with
	| JCAquantifier(_,vi,a) -> VarSet.remove vi acc
	| _ -> acc)
      VarSet.empty
  in
  let collect_sub_terms = 
    fold_term_in_assertion (fun acc t -> match t.jc_term_node with
      | JCTvar _ | JCTbinary(_,(Badd_int | Bsub_int),_)
      | JCTunary((Uplus_int | Uminus_int),_) -> acc
      | _ -> TermSet.add t acc
    ) TermSet.empty 
  in
  let vs1 = collect_free_vars target.jc_target_regular_invariant in
  let vs2 = collect_free_vars target.jc_target_assertion in
  let vs = VarSet.union vs1 vs2 in
  let ts1 = collect_sub_terms target.jc_target_regular_invariant in
  let ts2 = collect_sub_terms target.jc_target_assertion in
  let ts = TermSet.union ts1 ts2 in
  VarSet.fold (fun vi a ->
    let vit = term_var_no_loc vi in
    let copyvi = copyvar vi in
    add_inflexion_var curposts copyvi;
    target.jc_target_regular_invariant <-
      replace_term_in_assertion vit (JCTvar copyvi)
      target.jc_target_regular_invariant;
    target.jc_target_assertion <-
      replace_term_in_assertion vit (JCTvar copyvi) target.jc_target_assertion;
    let t1 = term_var_no_loc copyvi in
    let bop = equality_operator_for_type vi.jc_var_info_type in
    let eq = raw_asrt (JCArelation(t1,bop,vit)) in
    let eqs = 
      TermSet.fold (fun t acc ->
	if raw_strict_sub_term vit t then
	  let t2 = replace_term_in_term ~source:vit ~target:(JCTvar copyvi) t in
	  if is_integral_type t.jc_term_type then
	    let bop = equality_operator_for_type t.jc_term_type in
	    let eq = raw_asrt(JCArelation(t2,bop,t)) in
	    eq::acc
	  else acc
	else acc
      ) ts [eq]
    in
    make_and(a::eqs)
  ) vs (raw_asrt JCAtrue) 

let finalize_target ~is_function_level curposts target inva =
  let annot_name = 
    if is_function_level then "precondition" else "loop invariant" 
  in
  let vs,curposts = pop_modified_vars curposts in
  let vs = VarSet.union vs !(curposts.jc_post_inflexion_vars) in
  if is_function_level then assert(curposts.jc_post_modified_vars = []);
  match curposts.jc_post_normal with None -> None | Some wpa -> 
    (* [wpa] is the formula obtained by weakest precondition from some 
     * formula at the assertion point.
     *)
    (* [patha] is the path formula. It characterizes the states from which 
     * it is possible to reach the assertion point.
     *)
    let patha = make_and[wpa;target.jc_target_regular_invariant] in
    (* [impla] is the implication formula, that guarantees the assertion holds
     * when the assertion point is reached.
    *)
    let impla = raw_asrt(JCAimplies(patha,target.jc_target_assertion)) in
    (* [quanta] is the quantified formula. It quantifies [impla] over the 
     * variables modified.
     *)
    let quanta = 
      VarSet.fold (fun vi a -> raw_asrt (JCAquantifier(Forall,vi,a))) vs impla
    in
    (* [elima] is the quantifier free version of [quanta].
    *)
    let elima = quantif_eliminate quanta inva in
    if contradictory elima patha then
      begin
	if Jc_options.verbose then
	  printf "%a@[<v 2>No inferred %s@."
	    Loc.report_position target.jc_target_location annot_name;
	None
      end
    else
      begin
	if Jc_options.verbose then
	  printf "%a@[<v 2>Inferring %s@\n%a@]@."
	    Loc.report_position target.jc_target_location
	    annot_name Jc_output.assertion elima;
	Some elima
      end
	  
let rec wp_statement weakpre = 
  let var_of_term = Hashtbl.create 0 in
  (* Terms should be raw only. *)
  let unique_var_for_term t ty =
    try Hashtbl.find var_of_term t
    with Not_found ->
      let vi = Jc_pervasives.var ty (term_name t) in
      Hashtbl.add var_of_term t vi;
      vi
  in
  fun target s curposts ->
    if debug then 
      printf "[wp_statement] %a@." Loc.report_position s.jc_statement_loc;
    let curposts = match s.jc_statement_node with
      | JCSdecl(vi,eo,s) ->
	  let curposts = wp_statement weakpre target s curposts in
	  let post = 
	    match curposts.jc_post_normal with None -> None | Some a -> 
	      let a = 
		match eo with None -> a | Some e ->
		  match term_of_expr e with None -> a | Some t2 ->
		    if vi.jc_var_info_type = boolean_type then
		      (* TODO: take boolean variables into account. *)
		      a
		    else
		      let t1 = term_var_no_loc vi in
		      let bop = 
			equality_operator_for_type vi.jc_var_info_type in
		      let eq = raw_asrt (JCArelation(t1,bop,t2)) in
(* 		      raw_asrt (JCAimplies(eq,a)) *)
		      make_and [eq;a]
	      in
(* 	      Some (raw_asrt (JCAquantifier(Forall,vi,a))) *)
	      Some a
	  in
	  let curposts = add_modified_var curposts vi in
	  { curposts with jc_post_normal = post; }
      | JCSassign_var(vi,e) ->
	  if debug then
	    printf "[assignment]%s@." vi.jc_var_info_name;
	  let vit = term_var_no_loc vi in
	  let copyvi = copyvar vi in
	  let post = match curposts.jc_post_normal with
	    | None -> None
	    | Some a -> 
		let a = replace_term_in_assertion vit (JCTvar copyvi) a in
		match term_of_expr e with
		  | None -> Some a
		  | Some t2 ->
		      if vi.jc_var_info_type = boolean_type then
			(* TODO: take boolean variables into account. *)
			Some a
		      else
			let t1 = term_var_no_loc copyvi in
			let bop = equality_operator_for_type vi.jc_var_info_type in
			let eq = raw_asrt (JCArelation(t1,bop,t2)) in
(* 			Some (raw_asrt (JCAimplies(eq,a))) *)
			Some(make_and [eq;a])
	  in
	  add_inflexion_var curposts copyvi;
	  let curposts = 
	    if is_function_level curposts then curposts
	    else
	      (* Also add regular variable, for other branches in loop. *)
	      add_modified_var curposts vi 
	  in
	  { curposts with jc_post_normal = post; }
      | JCSassign_heap(e1,fi,e2) ->
	  begin match term_of_expr e1 with
	    | None -> curposts (* TODO *)	| Some t1 ->
		let dereft = term_no_loc (JCTderef(t1,fi)) fi.jc_field_info_type in
		let vi = unique_var_for_term dereft fi.jc_field_info_type in
		let copyvi = copyvar vi in
		let post = match curposts.jc_post_normal with
		  | None -> None
		  | Some a -> 
		      let a = 
			replace_term_in_assertion dereft (JCTvar copyvi) a 
		      in
		      match term_of_expr e2 with
			| None -> Some a
			| Some t2 ->
			    let t1 = term_var_no_loc copyvi in
			    let bop = 
			      equality_operator_for_type fi.jc_field_info_type in
			    let eq = raw_asrt (JCArelation(t1,bop,t2)) in
(* 			    Some (raw_asrt (JCAimplies(eq,a))) *)
			    Some(make_and [eq;a])
		in
		add_inflexion_var curposts copyvi;
		let curposts = 
		  if is_function_level curposts then curposts
		  else
		    (* Also add regular variable, for other branches in loop. *)
		    add_modified_var curposts vi 
		in
		{ curposts with jc_post_normal = post; }
	  end
      | JCSassert a1 ->
	  let post = match curposts.jc_post_normal with
	    | None -> None
(* 	    | Some a -> Some (raw_asrt (JCAimplies(a1,a))) *)
	    | Some a -> Some (make_and [a1;a])
	  in
	  { curposts with jc_post_normal = post; }
      | JCSblock sl ->
	  List.fold_right (wp_statement weakpre target) sl curposts
      | JCSif(e,ts,fs) ->
	  let tposts = wp_statement weakpre target ts curposts in
	  if debug then
	    printf "[true branch]%a@." print_modified_vars tposts;
	  let tpost = match tposts.jc_post_normal with
	    | None -> None
	    | Some a -> 
		let ta = raw_asrt_of_expr e in
(* 		Some (raw_asrt (JCAimplies(ta,a))) *)
		Some(make_and [ta;a])
	  in
	  let fposts = wp_statement weakpre target fs curposts in
	  if debug then
	    printf "[false branch]%a@." print_modified_vars fposts;
	  let fpost = match fposts.jc_post_normal with
	    | None -> None
	    | Some a -> 
		let fa = raw_not_asrt (raw_asrt_of_expr e) in
(* 		Some (raw_asrt (JCAimplies(fa,a))) *)
		Some(make_and [fa;a])
	  in
	  let post = match tpost,fpost with
	    | None,opta | opta,None -> opta
(* 	    | Some ta,Some fa -> Some (make_and [ta;fa]) *)
	    | Some ta,Some fa -> Some (make_or [ta;fa])
	  in
	  let tvs,_ = pop_modified_vars tposts in
	  let fvs,_ = pop_modified_vars fposts in
	  let vs = VarSet.union tvs fvs in
	  let curposts = add_modified_vars curposts vs in
	  { curposts with jc_post_normal = post; }
      | JCSreturn_void | JCSreturn _ -> 
	  { curposts with jc_post_normal = None; }
      | JCSthrow(ei,_) -> (* TODO: link with value caught *)
	  let post = 
	    try Some (List.assoc ei curposts.jc_post_exceptional) 
	    with Not_found -> None 
	  in
	  { curposts with jc_post_normal = post; }
      | JCSpack _ | JCSunpack _ -> 
	  curposts
      | JCStry(s,hl,fs) ->
	  begin match fs.jc_statement_node with 
	    | JCSblock [] -> ()
	    | _ -> assert false (* TODO: apply finally stmt to all paths. *)
	  end;
	  let handlpostexcl,handlvs = 
	    List.fold_left 
	      (fun (curpostexcl,curvs) (ei,vio,s) ->
		let excposts = wp_statement weakpre target s curposts in
		let curpostexcl = match excposts.jc_post_normal with
		  | None -> curpostexcl
		  | Some a -> (ei,a) :: curpostexcl
		in
		let excvs,_ = pop_modified_vars excposts in
		let curvs = VarSet.union curvs excvs in
		(curpostexcl,curvs)
	      ) ([],VarSet.empty) hl
	  in
	  let curpostexcl = 
	    List.filter (fun (ei,_) ->
	      not (List.exists (fun (ej,_,_) ->
		ei.jc_exception_info_tag = ej.jc_exception_info_tag) hl)
	    ) curposts.jc_post_exceptional
	  in
	  let curpostexcl = handlpostexcl @ curpostexcl in
	  let tmpposts = { curposts with jc_post_exceptional = curpostexcl; } in
	  let bodyposts = wp_statement weakpre target s tmpposts in
	  let bodyvs,_ = pop_modified_vars bodyposts in
	  let vs = VarSet.union handlvs bodyvs in
	  let curposts = add_modified_vars curposts vs in
	  { curposts with jc_post_normal = bodyposts.jc_post_normal; }
      | JCSloop(la,ls) ->
	  let curposts = { curposts with jc_post_normal = None; } in
	  let loopposts = push_modified_vars curposts in
	  let loopposts = wp_statement weakpre target ls loopposts in
	  let post = 
	    match finalize_target 
	      ~is_function_level:false loopposts target la.jc_loop_invariant
	    with None -> None | Some infera ->
	      target.jc_target_regular_invariant <- la.jc_loop_invariant;
	      target.jc_target_assertion <- infera;
	      begin try
		let a = Hashtbl.find weakpre.jc_weakpre_loop_invariants
		  la.jc_loop_tag
		in
		Hashtbl.replace weakpre.jc_weakpre_loop_invariants
		  la.jc_loop_tag (make_and [a; infera])
	      with Not_found ->
		Hashtbl.add weakpre.jc_weakpre_loop_invariants
		  la.jc_loop_tag infera
	      end;
	      let inita = initialize_target loopposts target in
	      Some inita
	  in
	  { curposts with jc_post_normal = post; }
      | JCScall(Some vi,call,s) -> 
	  let f = call.jc_call_fun in
	  let args = call.jc_call_args in
	  let curposts = wp_statement weakpre target s curposts in
	  let vit = term_var_no_loc vi in
	  let copyvi = copyvar vi in
	  let post = match curposts.jc_post_normal with
	    | None -> None
	    | Some a -> Some(replace_term_in_assertion vit (JCTvar copyvi) a)
	  in
	  add_inflexion_var curposts copyvi;
	  let curposts = 
	    if is_function_level curposts then curposts
	    else
	      (* Also add regular variable, for other branches in loop. *)
	      add_modified_var curposts vi 
	  in
	  { curposts with jc_post_normal = post; }
      | JCScall(None,call,s) -> 
	  let f = call.jc_call_fun in
	  let args = call.jc_call_args in
	  let curposts = wp_statement weakpre target s curposts in
	  curposts
    in
    if s == target.jc_target_statement then
(*       let a = raw_asrt(JCAimplies(target.jc_target_regular_invariant, *)
(*       target.jc_target_assertion)) in *)
      let inita = initialize_target curposts target in
      assert (curposts.jc_post_normal = None);
      { curposts with jc_post_normal = Some inita; }
    else curposts

let rec record_wp_invariants weakpre s =
  match s.jc_statement_node with
    | JCSdecl(_,_,s) -> 
	record_wp_invariants weakpre s
    | JCSblock sl ->
	List.iter (record_wp_invariants weakpre) sl
    | JCSif(_,ts,fs) ->
	record_wp_invariants weakpre ts;
	record_wp_invariants weakpre fs
    | JCStry(s,hl,fs) ->
	record_wp_invariants weakpre s;
	List.iter (fun (_,_,s) -> record_wp_invariants weakpre s) hl;
	record_wp_invariants weakpre fs
    | JCSloop(la,ls) ->
	let loop_invariants = weakpre.jc_weakpre_loop_invariants in
	begin try
	  let loopinvs = Hashtbl.find loop_invariants la.jc_loop_tag in
	  la.jc_loop_invariant <- make_and [la.jc_loop_invariant; loopinvs]
	with Not_found -> () end
    | JCSassign_var _ | JCSassign_heap _ | JCSassert _ 
    | JCSreturn_void | JCSreturn _ | JCSthrow _ | JCSpack _ | JCSunpack _ 
    | JCScall _ ->
	()

let wp_function targets (fi,fs,sl) =
  if debug then printf "[wp_function]@.";
  let weakpre = {
    jc_weakpre_loop_invariants = Hashtbl.create 0;
  } in
  List.iter (fun target ->
    let initposts = {
      jc_post_normal = None;
      jc_post_exceptional = [];
      jc_post_modified_vars = [];
      jc_post_inflexion_vars = ref VarSet.empty;
    } in
    let initposts = push_modified_vars initposts in
    let posts = List.fold_right (wp_statement weakpre target) sl initposts in
    match 
      finalize_target ~is_function_level:true posts target fs.jc_fun_requires
    with None -> () | Some infera ->
      fs.jc_fun_requires <- make_and [fs.jc_fun_requires;infera]
  ) targets;
  List.iter (record_wp_invariants weakpre) sl
    

(*****************************************************************************)
(* Augmenting loop invariants.                                               *)
(*****************************************************************************)

let collect_immediate_targets targets s =
  (* Special version of [fold_statement] different from the one 
   * in [Jc_iterators] in that fpost is called after the body statement 
   * of the try block.
   *)
  let rec fold_statement fpre fpost acc s =
    let acc = fpre acc s in
    let acc = match s.jc_statement_node with
      | JCSdecl(_,_,s) | JCScall(_,_,s) -> 
	  fold_statement fpre fpost acc s
      | JCSblock sl ->
	  List.fold_left (fold_statement fpre fpost) acc sl
      | JCSif(_,ts,fs) ->
	  let acc = fold_statement fpre fpost acc ts in
	  fold_statement fpre fpost acc fs
      | JCStry(s,hl,fs) ->
	  let acc = fold_statement fpre fpost acc s in
          let acc = fpost acc s in
	  let acc = 
	    List.fold_left (fun acc (_,_,s) -> 
	      fold_statement fpre fpost acc s
	    ) acc hl
	  in
	  fold_statement fpre fpost acc fs
      | JCSloop(_,ls) ->
	  fold_statement fpre fpost acc ls
      | JCSreturn _ | JCSthrow _ | JCSassert _ | JCSassign_var _
      | JCSassign_heap _ | JCSpack _ | JCSunpack _ | JCSreturn_void ->
	  acc
    in
    fpost acc s
  in
  let in_select_zone = ref false in
  let select_pre acc s =
    match s.jc_statement_node with
      | JCSassert a -> 
	  if debug then printf "[select_pre] consider target@.";
	  if debug then printf "[select_pre] in zone ? %b@." !in_select_zone;
	  if !in_select_zone then 
	    let target = target_of_assertion s s.jc_statement_loc a in
	    if debug then printf "[select_pre] adding in_zone target@.";
	    target::acc 
	  else acc
      | JCSloop _ -> 
	  if debug then printf "[select_pre] in_zone true@.";
	  in_select_zone := true; acc
      | JCSdecl _ | JCSblock _ | JCSassign_var _
      | JCSassign_heap _ | JCSpack _ | JCSunpack _ | JCStry _ ->
          (* Allowed with [JCStry] thanks to patched [fold_statement]. *)
	  acc
      | JCScall _ | JCSif _ | JCSreturn _ | JCSthrow _
      | JCSreturn_void ->
	  if debug then printf "[select_pre] in_zone false@.";
	  in_select_zone := false; acc	
  in
  let select_post acc s =
    match s.jc_statement_node with
      | JCSloop _ -> 
	  if debug then printf "[select_post] in_zone false@.";
	  in_select_zone := false; acc
      | _ -> acc
  in
  fold_statement select_pre select_post targets s

let rec backprop_statement target s curpost =
  if debug then 
    printf "[backprop_statement] %a@." Loc.report_position s.jc_statement_loc;
  let curpost = match s.jc_statement_node with
    | JCSdecl(vi,eo,s) ->
	let curpost = backprop_statement target s curpost in
	begin match curpost with None -> None | Some a -> 
	  match eo with None -> Some a | Some e ->
	    match term_of_expr e with None -> Some a | Some t2 ->
	      let t1 = term_var_no_loc vi in
	      Some(replace_term_in_assertion t1 t2.jc_term_node a)
	end
    | JCSassign_var(vi,e) ->
	begin match curpost with None -> None | Some a -> 
	  match term_of_expr e with None -> Some a | Some t2 ->
	    let t1 = term_var_no_loc vi in
	    Some(replace_term_in_assertion t1 t2.jc_term_node a)
	end
    | JCSassign_heap _ | JCSassert _ | JCSpack _ | JCSunpack _ ->
	curpost
    | JCSblock sl ->
	List.fold_right (backprop_statement target) sl curpost
    | JCSreturn_void | JCSreturn _ | JCSthrow _ ->
	assert (curpost = None); curpost
    | JCStry(s,hl,fs) ->
	assert (curpost = None); 
	let curpost = backprop_statement target fs None in
	assert (curpost = None);
        List.iter (fun (_,_,s) ->
  	  let curpost = backprop_statement target s None in
	  assert (curpost = None);
	) hl;
	backprop_statement target s None
    | JCSloop(la,ls) ->
	let curpost = backprop_statement target ls curpost in
	begin
          match curpost with None -> () | Some propa ->
	    if not (contradictory propa la.jc_loop_invariant) then
              begin
                if Jc_options.verbose then
                  printf 
	            "%a@[<v 2>Back-propagating loop invariant@\n%a@]@."
                    Loc.report_position s.jc_statement_loc
                    Jc_output.assertion propa;
	        la.jc_loop_invariant <- make_and [propa;la.jc_loop_invariant]
              end
	end;
	None
    | JCScall(_,_,s) ->
	assert (curpost = None);
	let curpost = backprop_statement target s None in
	assert (curpost = None); curpost
    | JCSif(_,ts,fs) ->
	assert (curpost = None);
	let curpost = backprop_statement target ts None in
	assert (curpost = None);
	let curpost = backprop_statement target fs None in
	assert (curpost = None); None
  in
  if s == target.jc_target_statement then
    begin 
      assert (curpost = None);
      Some target.jc_target_assertion
    end
  else curpost

let backprop_function targets (fi,fs,sl) =
  if debug then printf "[backprop_function]@.";
  List.iter (fun target ->
    ignore(List.fold_right (backprop_statement target) sl None)
  ) targets


(*****************************************************************************)
(* Main function.                                                            *)
(*****************************************************************************)

let code_function = function
  | fi,fs,None -> ()
  | fi,fs,Some sl ->
      let wp_filter canda =
        (* Only propagate candidate assertions for targets if Atp can make 
	 * sense of them.
	 *)
	(* TODO : make sure ident on common logic formulas. *)
(*         raw_assertion_equal canda (asrt_of_atp(atp_of_asrt canda)) *)
	true
      in
      begin match Jc_options.ai_domain with
	| "box" -> 
	    let mgr = Box.manager_alloc () in
	    ai_function mgr None [] (fi,fs,sl)
	| "oct" -> 
	    let mgr = Oct.manager_alloc () in
	    ai_function mgr None [] (fi,fs,sl)
	| "pol" -> 
	    let mgr = Polka.manager_alloc_strict () in
	    ai_function mgr None [] (fi,fs,sl)
	| "wp" ->
	    let targets = List.fold_left (collect_targets wp_filter) [] sl in
	    wp_function targets (fi,fs,sl)
	| "boxwp" | "octwp" | "polwp" ->
	    let targets = List.fold_left collect_immediate_targets [] sl in
	    backprop_function targets (fi,fs,sl);
	    let targets = List.fold_left (collect_targets wp_filter) [] sl in
	    begin match Jc_options.ai_domain with
	      | "boxwp" -> 
		  let mgr = Box.manager_alloc () in
		  ai_function mgr None targets (fi,fs,sl)
	      | "octwp" -> 
		  let mgr = Oct.manager_alloc () in
		  ai_function mgr None targets (fi,fs,sl)
	      | "polwp" -> 
		  let mgr = Polka.manager_alloc_strict () in
		  ai_function mgr None targets (fi,fs,sl)
	      | _ -> assert false
	    end;
 	    let targets = 
	      List.fold_right (fun target acc ->
		target.jc_target_regular_invariant <- 
		  simplify target.jc_target_regular_invariant (raw_asrt JCAtrue);
		(* Build the most precise invariant known at the current 
		 * assertion point: it is the conjunction of the regular 
		 * invariant (from forward abstract interpretation) and 
		 * the propagated invariant (from propagated assertions).
		 *)
		let inv = 
		  make_and [target.jc_target_regular_invariant;
		  target.jc_target_propagated_invariant]
		in
		(* Check whether the target assertion is a consequence of 
		 * the most precise invariant. 
		 *)
		let impl = 
		  raw_asrt(JCAimplies(inv,target.jc_target_assertion)) 
		in
		if tautology impl then 
		  begin
		    if debug then
		      printf "%a[code_function] proof of %a discharged@." 
			Loc.report_position target.jc_target_location
			Jc_output.assertion target.jc_target_assertion;
		    acc 
		  end
		else 
		  begin
		    if debug then
		      printf "%a[code_function] precondition needed for %a@." 
			Loc.report_position target.jc_target_location
			Jc_output.assertion target.jc_target_assertion;
		    (* Adding target to the list. *)
		    target :: acc
		  end
	      ) targets []
	    in
	    wp_function targets (fi,fs,sl)
	| _ -> assert false
      end
	

(*****************************************************************************)
(* Interprocedural analysis.                                                 *)
(*****************************************************************************)

let rec ai_entrypoint mgr iaio (fi, fs, sl) =
  ai_function mgr iaio [] (fi, fs, sl);
  inspected_functions := fi.jc_fun_info_tag::!inspected_functions;
  List.iter
    (fun fi ->
      Hashtbl.iter
	(fun _ (fi',_,fs,slo) ->
	  match slo with
	    | None -> ()
	    | Some sl ->
		if fi'.jc_fun_info_name = fi.jc_fun_info_name && 
		  (not (List.mem fi.jc_fun_info_tag !inspected_functions)) then
		    ai_entrypoint mgr iaio (fi, fs, sl))
	Jc_norm.functions_table)
    fi.jc_fun_info_calls
    
let rec record_ai_inter_preconditions mgr iai fi fs =
  let pre = try 
    Hashtbl.find iai.jc_interai_function_preconditions fi.jc_fun_info_tag 
  with Not_found -> Abstract1.top mgr (Environment.make [||] [||])
  in
  let a = mkinvariant mgr pre in
  begin
    if Jc_options.verbose then
      printf 
	"@[<v 2>Inferring precondition for function %s@\n%a@]@."
	fi.jc_fun_info_name Jc_output.assertion a;
    fs.jc_fun_requires <- make_and [fs.jc_fun_requires; a];
    inspected_functions := fi.jc_fun_info_tag::!inspected_functions;
    List.iter 
      (fun fi ->
	Hashtbl.iter
	  (fun _ (fi',_,fs,_) ->
	    if fi'.jc_fun_info_name = fi.jc_fun_info_name && 
	      (not (List.mem fi.jc_fun_info_tag !inspected_functions)) then
		record_ai_inter_preconditions mgr iai fi' fs;)
	  Jc_norm.functions_table)
      fi.jc_fun_info_calls
  end
    
let rec ai_entrypoint_fix mgr iai (fi, fs, sl) =
  ai_entrypoint mgr (Some iai) (fi, fs, sl);
  if !state_changed then
    begin
      state_changed := false;
      inspected_functions := [];
      ai_entrypoint_fix mgr iai (fi, fs, sl);
    end
      
let ai_interprocedural mgr (fi, fs, sl) =
  let iai = {
    jc_interai_manager = mgr;
    jc_interai_function_preconditions = Hashtbl.create 0
  } in
  ai_entrypoint_fix mgr iai (fi, fs, sl);
  inspected_functions := [];
  record_ai_inter_preconditions mgr iai fi fs;
  inspected_functions := [];
  ai_entrypoint mgr None (fi, fs, sl)
    
    
let main_function = function
  | fi, fs, None -> ()
  | fi, fs, Some sl ->
      begin match Jc_options.ai_domain with
	| "box" -> 
	    let mgr = Box.manager_alloc () in
	    ai_interprocedural mgr (fi, fs, sl)
	| "oct" -> 
	    let mgr = Oct.manager_alloc () in
	    ai_interprocedural mgr (fi, fs, sl)
	| "pol" -> 
	    let mgr = Polka.manager_alloc_strict () in
	    ai_interprocedural mgr (fi, fs, sl)
	| _ -> assert false
      end

	
(*
  Local Variables: 
  compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
  End: 
*)
