(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
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

(* $Id: jc_annot_inference.ml,v 1.137 2008-10-10 15:08:18 moy Exp $ *)

open Jc_stdlib
open Jc_env
open Jc_envset
open Jc_region
open Jc_ast
open Jc_fenv

open Jc_options
open Jc_constructors
open Jc_pervasives
open Jc_separation
open Jc_iterators

open Pp
open Format

open Apron
open Coeff
open Interval
open Lincons1
open Num

module TermTable = 
  Hashtbl.Make(struct type t = term 
		      let equal = raw_term_equal
		      let hash = Hashtbl.hash end)

module TermSet = 
struct
  include Set.Make(struct type t = term 
			  let compare = raw_term_compare end)
  let of_list tls = List.fold_left (fun acc t -> add t acc) empty tls
end

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
let nb_conj_atoms_inferred = ref 0
let nb_nodes = ref 0
let nb_loop_inv = ref 0
let nb_fun_pre = ref 0
let nb_fun_post = ref 0
let nb_fun_excep_post = ref 0


(*****************************************************************************)
(* Replacing variables in terms and assertions.                              *)
(*****************************************************************************)

let rec mem_term_in_assertion t a =
  fold_term_in_assertion (fun acc t' -> acc || raw_term_equal t t') false a

let rec mem_any_term_in_assertion tset a =
  fold_term_in_assertion (fun acc t -> acc || TermSet.mem t tset) false a

let rec replace_term_in_term ~source ~target t = 
  map_term (fun t -> if raw_term_equal source t then target else t) t
    
let rec replace_term_in_assertion srct targett a = 
  let term = replace_term_in_term ~source:srct ~target:targett in
  let asrt = replace_term_in_assertion srct targett in
  let anode = match a#node with
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
    | JCAapp app ->
	JCAapp { app with jc_app_args = List.map term app.jc_app_args }
    | JCAquantifier(qt,vi,a) ->
	JCAquantifier(qt,vi,asrt a)
    | JCAold a ->
	JCAold(asrt a)      
    | JCAat(a,lab) ->
	JCAat(asrt a,lab)      
    | JCAinstanceof(t,lab,st) ->
	JCAinstanceof(term t,lab,st)
    | JCAbool_term t ->
	JCAbool_term(term t)
    | JCAif(t,a1,a2) ->
	JCAif(term t,asrt a1,asrt a2)
    | JCAmutable(t,st,tag) ->
	JCAmutable(term t,st,tag)
    | JCAtrue | JCAfalse | JCAeqtype _ | JCAsubtype _ as anode -> anode
    | JCAmatch _ -> assert false (* TODO *)
  in
  new assertion_with ~node:anode a


let rec replace_vi_in_assertion srcvi targett a = 
  let term = replace_term_in_term 
    ~source:(new term ~typ:srcvi.jc_var_info_type (JCTvar srcvi)) 
    ~target:targett in
  let asrt = replace_vi_in_assertion srcvi targett in
  let anode = match a#node with
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
    | JCAapp app ->
	JCAapp { app with jc_app_args = List.map term app.jc_app_args }
    | JCAquantifier (qt, vi, a) ->
	JCAquantifier (qt, vi, asrt a)
    | JCAold a ->
	JCAold (asrt a)      
    | JCAat(a,lab) ->
	JCAat (asrt a,lab)      
    | JCAinstanceof (t, lab, st) ->
	JCAinstanceof (term t, lab, st)
    | JCAbool_term t ->
	JCAbool_term (term t)
    | JCAif (t, a1, a2) ->
	JCAif (term t, asrt a1, asrt a2)
    | JCAmutable (t, st, tag) ->
	JCAmutable (term t, st, tag)
    | JCAtrue | JCAfalse | JCAeqtype _ | JCAsubtype _ as anode -> anode
    | JCAmatch _ -> assert false (* TODO *)
  in
  new assertion_with ~node:anode a

let unfolding_of_app app =
  let f = app.jc_app_fun in
  let _, term_or_assertion = 
    try Hashtbl.find Jc_typing.logic_functions_table f.jc_logic_info_tag
    with Not_found -> assert false 
  in
  match term_or_assertion with
    | JCAssertion a ->
	let a = 
	  List.fold_left2 (fun a vi t -> replace_vi_in_assertion vi t a)
	    a f.jc_logic_info_parameters app.jc_app_args
	in
	Some a
    | _ -> None


(* comparison by name (vs. comparison by tag in 'replace_term_in_term' ) *)
let rec switch_vis_in_term srcvi targetvi t =
  let term = switch_vis_in_term srcvi targetvi in
  let node = match t#node with
    | JCTconst c -> JCTconst c
    | JCTvar vi -> 
	if vi.jc_var_info_name = srcvi.jc_var_info_name then
	  JCTvar targetvi else JCTvar vi
    | JCTshift (t1, t2) -> JCTshift (term t1, term t2)
    | JCTderef (t, lab, fi) -> JCTderef (term t, lab, fi)
    | JCTbinary (t1, bop, t2) -> JCTbinary (term t1, bop, term t2)
    | JCTunary (op, t) -> JCTunary (op, term t)
    | JCTapp app -> let tl = app.jc_app_args in
      JCTapp { app with jc_app_args = List.map term tl; }
    | JCTold t -> JCTold (term t)
    | JCTat (t, lab) -> JCTat (term t, lab)
    | JCToffset (ok, t, si) -> JCToffset (ok, term t, si)
    | JCTaddress (b,t) -> JCTaddress (b,term t)
    | JCTinstanceof (t, lab, si) -> JCTinstanceof (term t, lab, si)
    | JCTcast (t, lab, si) -> JCTcast (term t, lab, si)
    | JCTbitwise_cast (t, lab, si) -> JCTbitwise_cast (term t, lab, si)
    | JCTrange_cast (t, si) -> JCTrange_cast (term t, si)
    | JCTreal_cast (t, si) -> JCTreal_cast (term t, si)
    | JCTif (t1, t2, t3) -> JCTif (term t1, term t2, term t3)
    | JCTrange (to1, to2) -> JCTrange (Option_misc.map term to1, Option_misc.map term to2)
    | JCTmatch _ -> assert false (* TODO *)
  in
  new term_with ~node t
    
let rec switch_vis_in_assertion srcvi targetvi a = 
  let term = switch_vis_in_term srcvi targetvi in
  let asrt = switch_vis_in_assertion srcvi targetvi in
  let anode = match a#node with
    | JCArelation (t1, bop, t2) -> JCArelation (term t1, bop, term t2)
    | JCAnot a -> JCAnot (asrt a)
    | JCAand al -> JCAand (List.map asrt al)
    | JCAor al -> JCAor (List.map asrt al)
    | JCAimplies (a1, a2) -> JCAimplies (asrt a1, asrt a2)
    | JCAiff (a1, a2) -> JCAiff (asrt a1, asrt a2)
    | JCAapp app -> JCAapp { app with jc_app_args = List.map term app.jc_app_args }
    | JCAquantifier (qt, vi, a) -> 
	assert (vi.jc_var_info_name <> srcvi.jc_var_info_name);
	assert (vi.jc_var_info_name <> targetvi.jc_var_info_name);
	JCAquantifier (qt, vi, asrt a)
    | JCAold a -> JCAold (asrt a)      
    | JCAat (a, lab) -> JCAat (asrt a, lab)      
    | JCAinstanceof (t, lab, st) -> JCAinstanceof (term t, lab, st)
    | JCAbool_term t -> JCAbool_term (term t)
    | JCAif (t, a1, a2) -> JCAif (term t, asrt a1, asrt a2)
    | JCAmutable (t, st, tag) -> JCAmutable (term t, st, tag)
    | JCAtrue | JCAfalse | JCAeqtype _ | JCAsubtype _ as anode -> anode
    | JCAmatch _ -> assert false (* TODO *)
  in
  new assertion_with ~node:anode a
    
let forget_var_in_assertion v a =
  let v' = Jc_pervasives.newvar v.jc_var_info_type in
  switch_vis_in_assertion v v' a

(* Utility functions *)

let normalize_expr e =
  let name_app (e : expr) = match e#node with
    | JCEapp _ -> 
	if e#typ = Jc_pervasives.unit_type then e else
	  let name = tmp_var_name () in
	  let vi = Jc_pervasives.var e#typ name in
	  Expr.mklet 
	    ~pos:e#pos
	    ~var:vi
	    ~init:e
	    ~body:(Expr.mkvar ~pos:e#pos ~var:vi ())
	    ()
    | _ -> e
  in
  map_expr 
    ~after:(fun e -> match e#node with
	      | JCElet(_vi,e1,e2) ->
		  let elist = 
		    Option_misc.fold (fun e1 l -> e1::l) e1 [name_app e2] 
		  in
		  replace_sub_expr e elist
	      | _ ->
		  let elist = IExpr.subs e in
		  let elist = List.map name_app elist in
		  replace_sub_expr e elist
	   ) e
    
(* return the struct_info of (assumed) pointer t *)
let struct_of_term t =
  match t#typ with
    | JCTpointer(st,_,_) -> 
	begin match st with 
	  | JCtag(st,_) -> st
	  | JCroot _ -> assert false (* TODO *)
 	end
    | _ -> 
	if debug then printf "[struct_of_term] %a@." Jc_output.term t;
	assert false

let rec nb_conj_atoms a = match a#node with
  | JCAand al -> List.fold_left (fun acc a -> nb_conj_atoms a + acc) 0 al
  | JCAtrue | JCAfalse | JCArelation _ | JCAapp _  
  | JCAimplies _ | JCAiff _ | JCAquantifier _ | JCAinstanceof _ 
  | JCAbool_term _ | JCAif _ | JCAmutable _ | JCAeqtype _ | JCAmatch _
  | JCAor _ | JCAnot _ | JCAold _ | JCAat _ | JCAsubtype _ -> 1
      
let rec conjuncts a = match a#node with
  | JCAand al -> List.flatten(List.map conjuncts al)
  | JCAapp app ->
      begin match unfolding_of_app app with
	| Some a -> conjuncts a
	| None -> [ a ]
      end
  | _ -> [ a ]

let rec disjuncts a = match a#node with
  | JCAor al -> List.flatten(List.map disjuncts al)
  | _ -> [a]

let rec without_disjunct a = 
  fold_assertion (fun acc a -> match a#node with
		    | JCAor _ -> false
		    | _ -> acc) true a

let normalize_term t =
  map_term (fun t -> 
	      let tnode = match t#node with
		| JCToffset(off,t',st) as tnode ->
		    begin match t'#node with
		      | JCTshift(t1,t2) ->
			  let offt1 = new term_with ~node:(JCToffset(off,t1,st)) t in
			  JCTbinary(offt1,(`Bsub,`Integer),t2)
		      | _ -> tnode
		    end
		| tnode -> tnode
	      in
	      new term_with ~node:tnode t) t

let normalize_assertion a =
  let a = map_term_in_assertion normalize_term a in
  map_assertion (fun a -> 
		   let anode = match a#node with
		     | JCAand al ->
			 JCAand(List.flatten (List.map conjuncts al))
		     | JCAor al ->
			 JCAor(List.flatten (List.map disjuncts al))
		     | anode -> anode
		   in
		   new assertion_with ~node:anode a) a

let is_integral_type = function
  | JCTnative ty ->
      begin match ty with
	| Tunit | Treal | Tboolean | Tstring -> false
	| Tinteger -> true
      end
  | JCTenum _ -> true
  | JCTpointer _ | JCTlogic _ | JCTnull | JCTany | JCTtype_var _ -> false

let equality_operator_for_type ty = 
  `Beq, operator_of_type ty

(*
  let make_and al = 
(* optimization *)
  let al = List.filter (fun a -> not (is_true a)) al in
  let anode = match al with
  | [] -> JCAtrue
  | [a] -> a#node
  | a::tl -> JCAand al
  in
  new assertion anode
*)

let make_or al = 
  let anode = match al with
    | [] -> JCAfalse
    | [a] -> a#node
    | al -> JCAor al
  in
  new assertion anode

let make_not a =
  new assertion(JCAnot a)

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
    match t#node with
      | JCTconst c ->
	  begin match c with
	    | JCCinteger s -> filter_alphanumeric s
	    | JCCboolean b -> if b then "true" else "false"
	    | JCCvoid -> "void"
	    | JCCnull -> "null" 
	    | JCCreal(s,_) -> filter_alphanumeric s
	    | JCCstring _ -> "string"
	  end
      | JCTvar vi -> filter_alphanumeric vi.jc_var_info_final_name
      | JCTbinary(t1,(bop,_),t2) ->
	  let bop_name = match bop with
	    | `Blt -> "inf"
	    | `Bgt -> "sup"
	    | `Ble -> "infeq"
	    | `Bge -> "supeq"
	    | `Beq -> "eq"
	    | `Bneq -> "neq"
	    | `Badd -> "plus"
	    | `Bsub -> "minus"
	    | `Bmul -> "times"
	    | `Bdiv -> "div"
	    | `Bmod -> "mod"
	    | `Bland -> "and"
	    | `Blor -> "or"
	    | `Bimplies -> "implies"
	    | `Biff -> "iff"
	    | `Bbw_and -> "bwand"
	    | `Bbw_or -> "bwor"
	    | `Bbw_xor -> "bwxor"
	    | `Bshift_left -> "shiftleft"		
	    | `Blogical_shift_right -> "logicalshiftright"
	    | `Barith_shift_right -> "arithshiftright"
	    | `Bconcat -> "concat"
	  in
	  term_name t1 ^ "_" ^ bop_name ^ "_" ^ (term_name t2)
      | JCTunary((uop,_),t1) ->
	  let uop_name = match uop with
	    | `Uminus -> "minus"
	    | `Unot -> "not"
	    | `Ubw_not -> "bwnot"
	  in
	  uop_name ^ "_" ^ (term_name t1)
      | JCTshift (t1, t2) ->
	  term_name t1 ^ "_shift_" ^ (term_name t2)
      | JCTderef (t1, lab, fi) ->
	  term_name t1 ^ "_field_" ^ fi.jc_field_info_final_name
      | JCTapp app ->
	  let li = app.jc_app_fun and tl = app.jc_app_args in
	  li.jc_logic_info_name ^ "_of_" ^ 
	    List.fold_right(fun t acc ->
			      if acc = "" then term_name t
			      else term_name t ^ "_and_" ^ acc
			   ) tl ""
      | JCTold t ->
	  "old_" ^ (term_name t)
      | JCTat(t,lab) ->
	  (term_name t) ^ "_at_"   
      | JCToffset(Offset_max,t,st) ->
	  "offset_max_" ^ (term_name t)
      | JCToffset(Offset_min,t,st) ->
	  "offset_min_" ^ (term_name t)
      | JCTaddress(_,t) ->
	  "address_" ^ (term_name t)
      | JCTinstanceof(t,_,st) ->
	  (term_name t) ^ "_instanceof_" ^ st.jc_struct_info_name
      | JCTcast(t,_,st) | JCTbitwise_cast(t,_,st) ->
	  (term_name t) ^ "_cast_" ^ st.jc_struct_info_name
      | JCTrange_cast(t,ei) ->
	  (term_name t) ^ "_cast_" ^ ei.jc_enum_info_name
      | JCTreal_cast(t,rc) ->
	  (term_name t) ^ "_cast_" ^ 
	    (match rc with 
	       | Integer_to_real -> "integer_to_real"
	       | Real_to_integer -> "real_to_integer")
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
      | JCTmatch _ -> assert false (* TODO *)

(* support of <new> (Nicolas) *)
let rec destruct_alloc t = 
  match t#node with
    | JCTconst (JCCinteger str) -> None, Some t 
    | JCTvar vi -> Some vi, None
    | JCTbinary (t1, (`Bsub,`Integer), t2) ->
	begin
	  match destruct_alloc t1 with
	    | None, None ->
		None, Some 
		  (new term ~typ:integer_type
		     (JCTunary ((`Uminus,`Integer), 
				new term ~typ:integer_type
				  (JCTconst (JCCinteger "-1"))))
		  )
	    | Some vi, None ->
		None, Some 
		  (new term ~typ:integer_type
		     (JCTbinary	(new term ~typ:integer_type (JCTvar vi),
				 (`Bsub,`Integer),
				 new term ~typ:integer_type (JCTconst (JCCinteger "-1"))))
		  )
	    | vio, Some offt ->
		let t3 = JCTbinary (offt, (`Bsub,`Integer), t2) in
		let offt = new term ~typ:integer_type t3 in
		vio, Some offt 
	end
    | _ -> assert false

(* Deconstruct a pointer term into a base pointer term and an integer offset.
*)
let rec destruct_pointer t = 
  match t#node with
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
	      let tnode = JCTbinary(offt,(`Badd,`Integer),t2) in
	      let offt = new term ~typ:integer_type tnode in
	      topt,Some offt
	end
    | JCTcast(t,_,_) | JCTbitwise_cast(t,_,_) | JCTrange_cast(t,_) | JCTreal_cast(t,_) -> 
        (* Pointer arithmetic in Jessie is not related to the size of 
	 * the underlying type, like in C. This makes it possible to commute
	 * cast and arithmetic.
         *)
        destruct_pointer t
    | JCTapp _ | JCTold _ | JCTat _ | JCTif _ | JCTrange _ | JCTmatch _ -> 
        (* Not supported yet. *)
        assert false
    | JCTconst _ | JCTbinary _ 
    | JCTunary _ | JCToffset _ | JCTinstanceof _ | JCTaddress _ -> 
        (* Not of a pointer type. *)
        assert false

let rec term_depends_on_term t1 t2 =
  raw_sub_term t2 t1 ||
    match t2#node with
      | JCTderef(t2', _, fi) ->
	  let t2' = select_option (fst(destruct_pointer t2')) t2' in
	  begin match t1#node with
	      (* TODO *)
	      (* 	    | JCTapp app ->  *)
	      (* 		let f = app.jc_app_fun and tls = app.jc_app_args in *)
	      (* 		List.fold_left2 (fun acc param arg -> acc || *)
	      (* 		  term_depends_on_term arg t2' *)
	      (* 		  &&  *)
	      (* 		  VarSet.mem param  *)
	      (* 		  f.jc_logic_info_effects.jc_effect_through_params *)
	      (* 		) false f.jc_logic_info_parameters tls *)
	    | JCTderef(t1', _, fj) ->
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
  jc_target_expr : expr;
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
  jc_absinv_exceptional : (exception_info * 'a abstract_value) list;
  jc_absinv_return : (expr ref,'a abstract_value) Hashtbl.t;
}

(* Parameters of an abstract interpretation. *)
type 'a abstract_interpreter = {
  jc_absint_manager : 'a Manager.t;
  jc_absint_function_environment : Environment.t;
  jc_absint_function : fun_info;
  jc_absint_widening_threshold : int;
  jc_absint_loops : (int,expr) Hashtbl.t;
  jc_absint_loop_invariants : (int,'a abstract_invariants) Hashtbl.t;
  jc_absint_loop_initial_invariants : (int,'a abstract_invariants) Hashtbl.t;
  jc_absint_loop_iterations : (int,int) Hashtbl.t;
  jc_absint_loop_entry_invs : (int, 'a abstract_invariants) Hashtbl.t;
  jc_absint_target_assertions : target_assertion list;
}

(* Parameters of an interprocedural abstract interpretation. *)
type 'a interprocedural_ai = {
  jc_interai_manager : 'a Manager.t;
  jc_interai_function_preconditions : (int, 'a Abstract1.t) Hashtbl.t;
  jc_interai_function_postconditions : (int, 'a Abstract1.t) Hashtbl.t;
  jc_interai_function_exceptional : (int, (exception_info * 'a Abstract1.t) list)  Hashtbl.t;
  jc_interai_function_nb_iterations : (int, int) Hashtbl.t;
  jc_interai_function_init_pre : (int, 'a Abstract1.t) Hashtbl.t;
  jc_interai_function_abs : (int, 'a abstract_interpreter) Hashtbl.t;
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
    (fun fmt returns -> 
       Hashtbl.iter (fun _ absval -> print_abstract_value fmt absval) returns)
    invs.jc_absinv_return

let print_modified_vars fmt posts =
  fprintf fmt "modified vars: %a" 
    (print_list comma (fun fmt vi -> fprintf fmt "%s" vi.jc_var_info_name))
    (VarSet.elements (List.hd posts.jc_post_modified_vars))


(*****************************************************************************)
(* Logging annotations inferred.                                             *)
(*****************************************************************************)

let reg_annot ?id ?kind ?name ~pos ~anchor a = 
  let (f,l,b,e) =
    try
      let (f,l,b,e,_,_) = Hashtbl.find Jc_options.pos_table anchor in
      (f,l,b,e)
    with Not_found -> Loc.extract pos
  in
  let pos = Lexing.dummy_pos in
  let pos = { pos with 
		Lexing.pos_fname = f; 
		Lexing.pos_lnum = l; 
		Lexing.pos_bol = 0; } 
  in
  let loc = 
    { pos with Lexing.pos_cnum = b; },
    { pos with Lexing.pos_cnum = e; } 
  in
  Format.fprintf Format.str_formatter "%a" Jc_output.assertion a;
  let formula = Format.flush_str_formatter () in
  let lab = Output.reg_pos "G" ?id ?kind ?name ~formula loc in
  new assertion_with ~mark:lab a


(*****************************************************************************)
(* From expressions to terms and assertions.                                 *)
(*****************************************************************************)

let rec p_term_of_expr e =
  let node = match e#node with
    | JCEconst c -> JCTconst c
    | JCEvar vi -> JCTvar vi
    | JCEbinary (e1, (op,opty), e2) -> 
	JCTbinary (p_term_of_expr e1, ((op :> bin_op),opty), p_term_of_expr e2) 
    | JCEunary (op, e) -> JCTunary (op, p_term_of_expr e)
    | JCEshift (e1, e2) -> JCTshift (p_term_of_expr e1, p_term_of_expr e2)
    | JCEderef (e, fi) -> JCTderef (p_term_of_expr e, LabelHere, fi)
    | JCEinstanceof (e, si) -> JCTinstanceof (p_term_of_expr e, LabelHere, si)
    | JCEcast (e, si) -> JCTcast (p_term_of_expr e, LabelHere, si)
    | JCEif (e1, e2, e3) -> JCTif (p_term_of_expr e1, p_term_of_expr e2, p_term_of_expr e3)
    | JCEoffset (ok, e, si) -> JCToffset (ok, p_term_of_expr e, si)
	(*    | JCEmatch (e, pel) ->
	      let ptl = List.map (fun (p, e) -> (p, p_term_of_expr e)) pel in
	      JCTmatch (p_term_of_expr e, ptl)*)
    | JCErange_cast (e, ri) -> JCTrange_cast (p_term_of_expr e, ri)
    | JCEreal_cast (e, rc) -> JCTreal_cast (p_term_of_expr e, rc)
    | JCEalloc _ -> assert false
    | JCEfree _ -> assert false
    | _ -> assert false
  in
  new term ~typ:e#typ ~region:e#region ~pos:e#pos node

let term_of_expr e =
  let rec term e = 
    let tnode, ty = match e#node with
      | JCEconst c -> JCTconst c, e#typ
      | JCEvar vi -> JCTvar vi, e#typ
      | JCEbinary (e1, (bop,opty), e2) -> 
	  JCTbinary (term e1, ((bop :> bin_op),opty), term e2), e#typ
      | JCEunary (uop, e1) -> JCTunary (uop, term e1), e#typ
      | JCEshift (e1, e2) -> JCTshift (term e1, term e2), e#typ
      | JCEderef (e1, fi) -> JCTderef (term e1, LabelHere, fi), e#typ
      | JCEinstanceof (e1, st) -> JCTinstanceof (term e1, LabelHere, st), e#typ
      | JCEcast (e1, st) -> JCTcast (term e1, LabelHere, st), e#typ
      | JCErange_cast(e1,_)
      | JCEreal_cast(e1,_) -> let t1 = term e1 in t1#node, t1#typ
      | JCEif (e1, e2, e3) -> JCTif (term e1, term e2, term e3), e#typ
      | JCEoffset (off, e1, st) -> JCToffset (off, term e1, st), e#typ
      | JCEalloc (e, _) -> (* Note: \offset_max(t) = length(t) - 1 *)
	  JCTbinary (term e, (`Bsub,`Integer), new term ~typ:integer_type (JCTconst (JCCinteger "1")) ), e#typ
      | JCEfree _ -> failwith "Not a term"
      | _ -> failwith "Not a term"
	  (*       | JCEmatch (e, pel) -> *)
	  (* 	  let ptl = List.map (fun (p, e) -> (p, term_of_expr e)) pel in *)
	  (* 	    JCTmatch (term_of_expr e, ptl) *)
    in
    new term ~typ:ty ~region:e#region tnode 
  in
  try Some (term e) with Failure _ -> None

let rec term_under_expr e =
  match e#node with
    | JCElet(_vi,_init,e) -> term_under_expr e
    | JCEblock [] -> None
    | JCEblock el -> term_under_expr (List.hd (List.rev el))
    | _ -> term_of_expr e

let term_of_expr = term_under_expr

let rec asrt_of_expr e =
  let anode = match e#node with
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
    | JCEbinary (e1,(#comparison_op,_ as bop), e2) ->
	begin match term_of_expr e1, term_of_expr e2 with
	  | Some t1, Some t2 -> JCArelation (t1, bop, t2)
	  | _ -> JCAtrue
	end
	  (*     | JCEbinary (e1,(#logical_op,_ as bop), e2) -> *)
	  (* 	begin match bop with *)
	  (* 	  | Bland -> JCAand [asrt_of_expr e1;asrt_of_expr e2] *)
	  (* 	  | Blor -> JCAor [asrt_of_expr e1;asrt_of_expr e2] *)
	  (* 	  | Bimplies -> JCAimplies(asrt_of_expr e1,asrt_of_expr e2) *)
	  (* 	  | Biff -> JCAiff(asrt_of_expr e1,asrt_of_expr e2) *)
	  (* 	  | _ -> assert false *)
	  (* 	end *)
    | JCEbinary _ ->
	assert false
	  (*     | JCEunary(uop,e1) -> *)
	  (* 	if is_logical_unary_op uop then *)
	  (* 	  match uop with *)
	  (* 	    | Unot -> JCAnot(asrt_of_expr e1) *)
	  (* 	    | _ -> assert false *)
	  (* 	else assert false *)
    | JCEinstanceof(e1,st) ->
	begin match term_of_expr e1 with
	  | Some t1 -> JCAinstanceof(t1,LabelHere,st)
	  | None -> JCAtrue 
	end
    | JCEif (e1, e2, e3) -> 
	begin match term_of_expr e1 with
	  | Some t1 -> JCAif (t1, asrt_of_expr e2, asrt_of_expr e3)
	  | None -> JCAtrue 
	end
    | JCEderef _ -> 
	begin match term_of_expr e with
	  | Some t -> JCAbool_term t
	  | None -> JCAtrue 
	end
    | JCEcast _ | JCErange_cast _ | JCEreal_cast _ | JCEshift _ 
    | JCEoffset _ | JCEalloc _ | JCEfree _ -> assert false
	(*     | JCEmatch (e, pel) -> assert false *)
	(*
	  let ptl = List.map (fun (p, e) -> (p, term_of_expr e)) pel in
	  JCAmatch (term_of_expr e, ptl)
	*)
    | _ -> 
	failwith "Not an assertion"
  in
  new assertion anode

let raw_asrt_of_expr = asrt_of_expr



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
      let tmin = new term ~typ:integer_type (JCToffset(Offset_min,t,st)) in
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
      let tmax = new term ~typ:integer_type (JCToffset(Offset_max,t,st)) in
      Hashtbl.add term_table s tmax
    end;
    s

  let term s = Hashtbl.find term_table s

end

let is_neq_binop = function
  | (`Bneq,`Integer) | (`Bneq,_) -> true
  | _ -> false

let atp_relation_of_binop = function
  | (`Blt,`Integer) | (`Blt,_) -> "<"
  | (`Bgt,`Integer) | (`Bgt,_) -> ">"
  | (`Ble,`Integer) | (`Ble,_) -> "<="
  | (`Bge,`Integer) | (`Bge,_) -> ">="
  | (`Beq,`Integer) | (`Beq,_) -> "="
  | (`Bneq,`Integer) | (`Bneq,_) -> 
      assert false (* Should be treated as "not (t1 eq t2)". *)
  | _ -> assert false

let atp_arithmetic_of_binop = function
  | (`Badd,`Integer) | (`Badd,_) -> "+"
  | (`Bsub,`Integer) | (`Bsub,_) -> "-"
  | (`Bmul,`Integer) | (`Bmul,_) -> "*"
  | _ -> failwith "Atp alien"

let rec free_variables t =
  fold_term
    (fun acc t -> match t#node with
       | JCTvar vi ->
	   VarSet.add vi acc
       | _ -> acc
    ) VarSet.empty t

let rec atp_of_term t = 
  (*   if debug then printf "[atp_of_term] %a@." Jc_output.term t; *)
  let is_constant_term t = 
    match t#node with JCTconst _ -> true | _ -> false
  in
  match t#node with
    | JCTconst c ->
	begin match c with
	  | JCCinteger s -> 
	      Atp.Fn(s,[])
	  | JCCnull  -> 
	      Atp.Var (Vwp.variable t)
	  | JCCboolean _ | JCCvoid | JCCreal _ | JCCstring _ -> 
	      assert false
	end
    | JCTbinary(t1,((`Badd,`Integer) | (`Bsub,`Integer) as bop),t2) ->
	Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
    | JCTbinary(t1,((`Bmul,`Integer) as bop),t2) 
	when (is_constant_term t1 || is_constant_term t2) ->
	Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
    | JCTbinary(t1,((`Bdiv,`Integer) as bop),t2) when (is_constant_term t2) ->
	Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
    | JCTbinary(t1,bop,t2) ->
	Atp.Var (Vwp.variable t)
    | JCTunary(uop,t1) ->
	Atp.Fn(Jc_output.unary_op uop, [atp_of_term t1])
    | JCToffset(Offset_min,t,st) ->
	Atp.Var (Vwp.offset_min_variable t st)
    | JCToffset(Offset_max,t,st) ->
	Atp.Var (Vwp.offset_max_variable t st)
    | JCTvar _ | JCTderef _ | JCTapp _ ->
	Atp.Var (Vwp.variable t)
    | JCTshift _ | JCTold _ | JCTat _ | JCTmatch _ 
    | JCTinstanceof _ | JCTcast _ | JCTrange_cast _ | JCTbitwise_cast _ | JCTreal_cast _ | JCTaddress _
    | JCTif _ | JCTrange _ ->
        failwith "Atp alien"
	  (*	assert false*)

let rec term_of_atp tm =
  match tm with
    | Atp.Var s -> 
	Vwp.term s
    | Atp.Fn("+",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,(`Badd,`Integer),term_of_atp tm2) in
	new term ~typ:integer_type tnode
    | Atp.Fn("-",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,(`Bsub,`Integer),term_of_atp tm2) in
	new term ~typ:integer_type tnode
    | Atp.Fn("*",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,(`Bmul,`Integer),term_of_atp tm2) in
	new term ~typ:integer_type tnode
    | Atp.Fn("/",[tm1;tm2]) ->
	let tnode = JCTbinary(term_of_atp tm1,(`Bdiv,`Integer),term_of_atp tm2) in
	new term ~typ:integer_type tnode
    | Atp.Fn("-",[tm1]) ->
	let tnode = JCTunary((`Uminus,`Integer),term_of_atp tm1) in
	new term ~typ:integer_type tnode
    | Atp.Fn(s,[]) ->
	let tnode = JCTconst (JCCinteger s) in
	new term ~typ:integer_type tnode
    | tm -> 
	printf "Unexpected ATP term %a@." (fun fmt tm -> Atp.printert tm) tm;
	assert false

let rec atp_of_asrt a = 
  (*   if debug then printf "[atp_of_asrt] %a@." Jc_output.assertion a; *)
  try begin match a#node with
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
    | JCAapp app ->
	begin match unfolding_of_app app with
	  | Some a -> atp_of_asrt a
	  | None -> failwith "Atp alien"
	end
    | JCAold _ | JCAat _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAeqtype _ | JCAmatch _ | JCAsubtype _ ->
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

let atp_of_asrt a =
  if Jc_options.debug then
    printf "@[<v 2>[atp_of_asrt]@\n%a@]@." Jc_output.assertion a;
  atp_of_asrt a

let rec asrt_of_atp fm =
  let anode = match fm with
    | Atp.False ->
	JCAfalse
    | Atp.True ->
	JCAtrue
    | Atp.Atom(Atp.R("=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,(`Beq,`Integer),term_of_atp tm2)
    | Atp.Atom(Atp.R("<",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,(`Blt,`Integer),term_of_atp tm2)
    | Atp.Atom(Atp.R(">",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,(`Bgt,`Integer),term_of_atp tm2)
    | Atp.Atom(Atp.R("<=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,(`Ble,`Integer),term_of_atp tm2)
    | Atp.Atom(Atp.R(">=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,(`Bge,`Integer),term_of_atp tm2)
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
  new assertion anode

let asrt_of_atp fm =
  if Jc_options.debug then
    printf "@[<v 2>[asrt_of_atp]@\n%a@]@." (fun fmt fm -> Atp.printer fm) fm;
  asrt_of_atp fm

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
    match t#typ with
      | JCTnative ty ->
	  begin match ty with
	    | Tunit | Treal | Tstring -> false
	    | Tboolean | Tinteger -> true
	  end
      | JCTenum _ -> true
      | JCTpointer _ | JCTlogic _ | JCTnull | JCTany | JCTtype_var _ -> false

  let has_offset_min_variable t =
    match t#typ with
      | JCTpointer _ -> true
      | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull | JCTany | JCTtype_var _ -> false

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
      let tmin = new term ~typ:integer_type (JCToffset(Offset_min,t,st)) in
      Hashtbl.add term_table va tmin;
      va
	
  let offset_max_variable t = 
    try
      TermTable.find offset_max_variable_table t
    with Not_found ->
      let va = Var.of_string ("__jc_offset_max_" ^ (term_name t)) in
      TermTable.add offset_max_variable_table t va;
      let st = struct_of_term t in
      let tmax = new term ~typ:integer_type (JCToffset(Offset_max,t,st)) in
      Hashtbl.add term_table va tmax;
      va

  let all_variables t =
    (if has_variable t then [variable t] else [])
    @ (if has_offset_min_variable t then [offset_min_variable t] else [])
    @ (if has_offset_max_variable t then [offset_max_variable t] else [])

  let term va = Hashtbl.find term_table va

  let variable_of_term t =
    match t#node with
      | JCToffset(Offset_min,t,_) ->
	  begin match t#node with
	    | JCTvar _ | JCTderef _ -> offset_min_variable t
	    | _ -> (*assert false*) offset_min_variable t
	  end
      | JCToffset(Offset_max,t,_) ->
	  begin match t#node with
	    | JCTvar _ | JCTderef _ -> offset_max_variable t
	    | _ -> (*assert false*) offset_max_variable t
	  end
      | _ -> variable t
	  
end      

let meet mgr val1 val2 =
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  let val1 = Abstract1.change_environment mgr val1 env false in
  let val2 = Abstract1.change_environment mgr val2 env false in
  Abstract1.meet mgr val1 val2

let join mgr val1 val2 =
  (*   let val1 = Abstract1.closure mgr val1 in *)
  (*   let val2 = Abstract1.closure mgr val2 in *)
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  let val1 = Abstract1.change_environment mgr val1 env false in
  let val2 = Abstract1.change_environment mgr val2 env false in
  Abstract1.join mgr val1 val2

let stronger mgr val1 val2 =
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  let val1 = Abstract1.change_environment mgr val1 env false in
  let val2 = Abstract1.change_environment mgr val2 env false in
  Abstract1.is_leq mgr val1 val2

let strictly_stronger mgr val1 val2 =
  stronger mgr val1 val2 && not (stronger mgr val2 val1)

let extend mgr env val1 =
  let env = Environment.lce env (Abstract1.env val1) in
  Abstract1.change_environment mgr val1 env false

let join_abstract_value mgr pair1 pair2 =
  {
    jc_absval_regular =
      join mgr pair1.jc_absval_regular pair2.jc_absval_regular;
    jc_absval_propagated =
      join mgr pair1.jc_absval_propagated pair2.jc_absval_propagated
  }

let join_invariants mgr invs1 invs2 =
  if Jc_options.debug then
    printf "@[<v 2>[join]@\n%a@\nand@\n%a@]@." 
      print_abstract_invariants invs1 print_abstract_invariants invs2;
  let join_exclists postexcl1 postexcl2 =
    let join1 = 
      List.fold_right 
	(fun (ei, post1) acc ->
	   try
	     let post2 = List.assoc ei postexcl2 in
	     let post1 = join_abstract_value mgr post1 post2 in
	     (ei, post1) :: acc
	   with Not_found -> (ei, post1) :: acc
	) postexcl1 []
    in
    List.fold_right 
      (fun (ei, post2) acc ->
	 if List.mem_assoc ei join1 then acc 
	 else (ei, post2) :: acc
      ) postexcl2 join1
  in
  assert (invs1.jc_absinv_return == invs2.jc_absinv_return);
  { 
    jc_absinv_normal =
      join_abstract_value mgr invs1.jc_absinv_normal invs2.jc_absinv_normal;
    jc_absinv_exceptional =
      join_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional;
    jc_absinv_return =
      invs1.jc_absinv_return
  }

(* Returns the widened value as there is no destructive version of [widening]
 * in [Abstract1]. *)
let widening mgr val1 val2 =
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  let val1 = Abstract1.change_environment mgr val1 env false in
  let val2 = Abstract1.change_environment mgr val2 env false in
  (* Join before widening so that arguments are in increasing order. *)
  let val2 = Abstract1.join mgr val2 val1 in
  (* Perform widening between values in increasing order. *)
  Abstract1.widening mgr val1 val2 

let widening_abstract_value mgr pair1 pair2 =
  {
    jc_absval_regular =
      widening mgr pair1.jc_absval_regular pair2.jc_absval_regular;
    jc_absval_propagated =
      widening mgr pair1.jc_absval_propagated pair2.jc_absval_propagated
  }

let widen_invariants mgr invs1 invs2 =
  if Jc_options.debug then
    printf "@[<v 2>[widening]@\n%a@\nand@\n%a@]@." 
      print_abstract_invariants invs1 print_abstract_invariants invs2;
  let widen_exclists postexcl1 postexcl2 =
    let widen1 = List.fold_right (fun (ei,post1) acc ->
				    try
				      let post2 = List.assoc ei postexcl2 in
				      let post1 = widening_abstract_value mgr post1 post2 in
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
  {
    jc_absinv_normal =
      widening_abstract_value mgr invs1.jc_absinv_normal invs2.jc_absinv_normal;
    jc_absinv_exceptional =
      widen_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional;
    jc_absinv_return =
      invs1.jc_absinv_return
  }    

let empty mgr val1 =
  Abstract1.bottom mgr (Abstract1.env val1)

let empty_abstract_value mgr pair1 =
  { 
    jc_absval_regular = 
      empty mgr pair1.jc_absval_regular;
    jc_absval_propagated =
      empty mgr pair1.jc_absval_propagated
  }

let is_eq mgr val1 val2 = (* TODO: compare env ? *)
  let env = Environment.lce (Abstract1.env val1) (Abstract1.env val2) in
  let val1 = Abstract1.change_environment mgr val1 env false in
  let val2 = Abstract1.change_environment mgr val2 env false in
  Abstract1.is_eq mgr val1 val2 

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
  Abstract1.forget_array mgr val1 varr false

let forget_abstract_value mgr absval vls =
  {
    jc_absval_regular =
      forget mgr absval.jc_absval_regular vls;
    jc_absval_propagated =
      forget mgr absval.jc_absval_propagated vls
  }

let forget_invariants mgr invs vls =
  {
    jc_absinv_normal =
      forget_abstract_value mgr invs.jc_absinv_normal vls;
    jc_absinv_exceptional =
      List.map (fun (ei,post) -> (ei,forget_abstract_value mgr post vls))
	invs.jc_absinv_exceptional;
    jc_absinv_return =
      invs.jc_absinv_return
  }

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

  let make_singleton conj = [conj]

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
    if is_false dnf then
      (* Make [pre] be the bottom abstract value. *)
      Abstract1.bottom mgr env
    else if is_true dnf then
      pre
    else
      let test_conj conj =
	let lincons =
	  try Parser.lincons1_of_lstring env conj
	  with Parser.Error msg -> printf "%s@." msg; assert false
	in
	let res = Abstract1.meet_lincons_array mgr pre lincons in
	if debug then printf "[Dnf.test_conj] %a@." print [conj];
	res
      in
      (* Test each disjunct separately and then join them. *)
      let copy_list = List.map test_conj dnf in
      match copy_list with
	| pre :: rest ->
	    List.fold_left (Abstract1.join mgr) pre rest
	| _ -> assert false
end

let assertion_of_dnf dnf = 
  let disjunct al = 
    let anode = match al with
      | [] -> JCAtrue
      | [a] -> a#node
      | _ -> JCAand al
    in
    new assertion anode    
  in
  let anode = match dnf with
    | [] -> JCAfalse
    | [[]] -> JCAtrue
    | [al] -> (disjunct al)#node
    | _ -> JCAor (List.map disjunct dnf)
  in
  new assertion anode


(*****************************************************************************)
(* Extracting linear expressions and constraints from AST expressions.       *)
(*****************************************************************************)
    
let rec not_asrt a =
  let anode = match a#node with
    | JCAtrue -> JCAfalse
    | JCAfalse -> JCAtrue
    | JCArelation (t1, (bop,opty), t2) ->
	begin match bop with
	  | `Blt -> JCArelation (t1, (`Bge,opty), t2)
	  | `Bgt -> JCArelation (t1, (`Ble,opty), t2)
	  | `Ble -> JCArelation (t1, (`Bgt,opty), t2)
	  | `Bge -> JCArelation (t1, (`Blt,opty), t2)
	  | `Beq -> JCArelation (t1, (`Bneq,opty), t2)
	  | `Bneq -> JCArelation (t1, (`Beq,opty), t2)
	end
    | JCAnot a -> 
	a#node
    | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _ | JCAapp _ 
    | JCAquantifier _ | JCAold _ | JCAat _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAeqtype _ | JCAsubtype _ | JCAmatch _ ->
	JCAnot a
  in
  new assertion_with ~node:anode a

let raw_not_asrt = not_asrt

let rec linearize t =
  match t#node with
    | JCTconst c ->
	begin match c with
	  | JCCinteger s -> (TermMap.empty, num_of_string s)
	  | JCCboolean _ | JCCvoid | JCCnull | JCCreal _ | JCCstring _ ->
	      failwith "linearize"
	end
    | JCTvar _ 
    | JCTderef _ ->
	(TermMap.add t (Int 1) TermMap.empty, Int 0)
    | JCTbinary(t1,(#arithmetic_op as bop,`Integer),t2) ->
	let coeffs1, cst1 = linearize t1 in
	let coeffs2, cst2 = linearize t2 in
        begin match bop with
	  | `Badd ->
	      let coeffs = TermMap.fold 
		(fun vt1 c1 acc ->
		   try 
		     let c2 = TermMap.find vt1 coeffs2 in
		     TermMap.add vt1 (c1 +/ c2) acc
		   with Not_found -> TermMap.add vt1 c1 acc
		) coeffs1 TermMap.empty
	      in
	      let coeffs = TermMap.fold 
		(fun vt2 c2 acc ->
		   if TermMap.mem vt2 coeffs then acc
		   else TermMap.add vt2 c2 acc
		) coeffs2 coeffs
	      in
	      (coeffs, cst1 +/ cst2)
	  | `Bsub ->
	      let coeffs = TermMap.fold 
		(fun vt1 c1 acc ->
		   try 
		     let c2 = TermMap.find vt1 coeffs2 in
		     TermMap.add vt1 (c1 -/ c2) acc
		   with Not_found -> TermMap.add vt1 c1 acc
		) coeffs1 TermMap.empty
	      in
	      let coeffs = TermMap.fold 
		(fun vt2 c2 acc ->
		   if TermMap.mem vt2 coeffs then acc
		   else TermMap.add vt2 (minus_num c2) acc
		) coeffs2 coeffs
	      in
	      (coeffs, cst1 -/ cst2)
	  | `Bmul when TermMap.is_empty coeffs1 || TermMap.is_empty coeffs2 ->
	      let coeffs =
		if TermMap.is_empty coeffs1 then
		  TermMap.map (fun c -> c */ cst1) coeffs2
		else
		  TermMap.map (fun c -> c */ cst2) coeffs1
	      in
	      (coeffs, cst1 */ cst2)
	  | `Bmul 
	  | `Bdiv
	  | `Bmod ->
	      (* Consider non-linear term as abstract variable. *)
	      (TermMap.add t (Int 1) TermMap.empty, Int 0)
	  | _ -> assert false
	end
    | JCTbinary(t1,(#bitwise_op as bop,`Integer),t2) ->
	let coeffs1, cst1 = linearize t1 in
	if coeffs1 = TermMap.empty && cst1 =/ Int 0 then
	  match bop with
	    | `Bbw_and 
	    | `Bshift_left 
	    | `Blogical_shift_right
	    | `Barith_shift_right -> TermMap.empty, Int 0 
	    | `Bbw_or
	    | `Bbw_xor -> linearize t2
	    | _ -> assert false
	else 
	  (* Consider non-linear term as abstract variable. *)
	  (TermMap.add t (Int 1) TermMap.empty, Int 0)
    | JCTbinary _ ->
	failwith "linearize"
    | JCTunary((uop,`Integer),t1) ->
	let coeffs1,cst1 = linearize t1 in
	begin match uop with
	  | `Uminus -> 
	      let coeffs = TermMap.map (fun c -> minus_num c) coeffs1 in
	      (coeffs, minus_num cst1)
	  | _ -> failwith "linearize"
	end
    | JCTunary _ ->
	failwith "linearize"
    | JCToffset _
    | JCTapp _ ->
	(TermMap.add t (Int 1) TermMap.empty, Int 0)
    | JCTshift _ | JCTinstanceof _
    | JCTmatch _ 
    | JCTold _ | JCTat _ | JCTcast _ | JCTbitwise_cast _  | JCTrange_cast _ | JCTreal_cast _ | JCTaddress _
    | JCTrange _ | JCTif _ -> 
	failwith "linearize"

let linstr_of_term env t =
  let mkmulstr = function
    | (va, Int 0) -> ""
    | (va, c) -> string_of_num c ^ " * " ^ va 
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
    let env = TermMap.fold 
      (fun t _ env  ->
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
	      new term ~typ:integer_type (JCToffset(Offset_min,ptrt,st))
	  | Offset_max_kind -> 
	      new term ~typ:integer_type (JCToffset(Offset_max,ptrt,st))
	in
	let t = match offt with None -> minmaxt | Some offt -> 
	  new term ~typ:integer_type (JCTbinary(minmaxt,(`Bsub,`Integer),offt))
	in
	linstr_of_term env t
	  
(* Returns a dnf. *)
let rec linstr_of_assertion env a =
  if debug then 
    Format.printf "[linstr_of_assertion] %a@." Jc_output.assertion a;
  match a#node with
    | JCAtrue -> env, Dnf.true_
    | JCAfalse -> env, Dnf.false_
    | JCArelation(t1,(bop,`Integer),t2) ->
	let subt = 
	  new term ~typ:integer_type (JCTbinary(t1,(`Bsub,`Integer),t2)) 
	in
	begin match linstr_of_term env subt with
	  | Some (env, str, cst) ->
	      let cstr = string_of_num (minus_num cst) in
	      (* Do not use < and > with APRON. Convert to equivalent non-strict. *)
	      let str = match bop with
		| `Blt -> [[str ^ " <= " ^ 
			      (string_of_num (pred_num (minus_num cst)))]]
		| `Bgt -> [[str ^ " >= " ^ 
			      (string_of_num (succ_num (minus_num cst)))]]
		| `Ble -> [[str ^ " <= " ^ cstr]]
		| `Bge -> [[str ^ " >= " ^ cstr]]
		| `Beq -> [[str ^ " = " ^ cstr]]
		| `Bneq -> 
		    [[str ^ " <= " ^ 
			(string_of_num (pred_num (minus_num cst)))];
		     [str ^ " >= " ^ 
			(string_of_num (succ_num (minus_num cst)))]]
	      in
	      env, str
	  | None -> env, Dnf.true_
	end
    | JCArelation _ -> env, Dnf.true_
    | JCAnot a ->
	let nota = not_asrt a in
	begin match nota#node with
	  | JCAnot _ -> env, Dnf.true_
	  | _ -> linstr_of_assertion env nota
	end
    | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _ | JCAapp _ 
    | JCAquantifier _ | JCAold _ | JCAat _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAeqtype _ | JCAsubtype _ | JCAmatch _ -> env, Dnf.true_
	
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
	  | Some (env, "", cst) -> Some (env, string_of_num cst)
	  | Some (env, str, cst) -> Some (env, str ^ " + " ^ (string_of_num cst))

let offset_linstr_of_expr env ok e = 
  match e#node with
    | JCEalloc _ -> 
	if ok = Offset_min_kind then Some (env, "0") else
	  (* Note: support of offset_max was skipped ? it seems to work well (Nicolas) *)
	  if ok = Offset_max_kind then
	    match term_of_expr e with
	      | None -> None
	      | Some t -> 
		  match linstr_of_term env t with
		    | None -> None
		    | Some (env,"",cst) -> Some (env,string_of_num cst)
		    | Some (env,str,cst) -> Some (env,str ^ " + " ^ (string_of_num cst))
	  else None
    | _ ->
	match term_of_expr e with
	  | None -> None
	  | Some t -> 
	      match offset_linstr_of_term env ok t with
		| None -> None
		| Some (env,"",cst) -> Some (env,string_of_num cst)
		| Some (env,str,cst) -> Some (env,str ^ " + " ^ (string_of_num cst))
		    
let is_null_term t = 
  match t#node with
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
		let tnode = JCTunary ((`Uminus,`Integer), Vai.term va) in
		let t = new term ~typ:integer_type tnode in
		Some t
	    | s -> 
		let ctnode = JCTconst (JCCinteger s) in
		let ct = new term ~typ:integer_type ctnode in
		let tnode = JCTbinary (ct, (`Bmul,`Integer), Vai.term va) in
		let t = new term ~typ:integer_type tnode in
		Some t
	  in
	  begin match t,vt with
	    | None,vt -> vt
	    | t,None -> t
	    | Some t,Some vt ->
		let tnode = JCTbinary (t, (`Badd,`Integer), vt) in
		let t = new term ~typ:integer_type tnode in
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
	      let ct = new term ~typ:integer_type ctnode in
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
    | EQ -> (`Beq,`Integer), JCCinteger "0"
    | SUPEQ -> (`Bge,`Integer), JCCinteger "0"
    | SUP -> (`Bgt,`Integer), JCCinteger "0"
    | DISEQ -> (`Bneq,`Integer), JCCinteger "0"
    | EQMOD scalar -> (* (`Bmod,`Integer), JCCinteger (Scalar.to_string scalar) *)
	assert false
  in
  let t2 = new term ~typ:integer_type (JCTconst c2) in
  new assertion (JCArelation(t1,op,t2)) 

let presentify a =
  let rec linterms_of_term t =
    let mkmulterm (t,c) =
      if c =/ Int 0 then None
      else if c =/ Int 1 then Some t
      else if c =/ Int (-1) then
	Some(new term ~typ:integer_type (JCTunary((`Uminus,`Integer),t)))
      else
	let c = new term ~typ:integer_type (JCTconst(JCCinteger(string_of_num c))) in
	Some(new term ~typ:integer_type (JCTbinary(c,(`Bmul,`Integer),t)))
    in
    let rec mkaddterm = function
      | [] -> None
      | [t,c] -> mkmulterm (t,c)
      | (t,c) :: r ->
	  match mkmulterm (t,c), mkaddterm r with
	    | None,None -> None
	    | Some t,None | None,Some t -> Some t
	    | Some t1,Some t2 -> Some(new term ~typ:integer_type (JCTbinary(t1,(`Badd,`Integer),t2)))
    in
    try
      let coeffs,cst = linearize t in
      let posl,negl =
	TermMap.fold (fun t c (pl,nl) ->
			if c >/ Int 0 then (t,c) :: pl, nl
			else if c </ Int 0 then pl, (t,minus_num c) :: nl
			else pl, nl
		     ) coeffs ([],[])
      in
      let cstt = new term ~typ:integer_type (JCTconst(JCCinteger(string_of_num(abs_num cst)))) in
      let post = match mkaddterm posl with
	| None -> 
	    if cst >/ Int 0 then cstt else new term ~typ:integer_type (JCTconst(JCCinteger "0"))
	| Some t -> 
	    if cst >/ Int 0 then new term ~typ:integer_type (JCTbinary(t,(`Badd,`Integer),cstt)) else t
      in
      let negt = match mkaddterm negl with
	| None ->
	    if cst </ Int 0 then cstt else new term ~typ:integer_type (JCTconst(JCCinteger "0"))
	| Some t ->
	    if cst </ Int 0 then new term ~typ:integer_type (JCTbinary(t,(`Badd,`Integer),cstt)) else t
      in
      Some (post,negt)
    with Failure _ -> None
  in
  let rec linasrt_of_assertion a =
    match a#node with
      | JCArelation(t1,bop,t2) ->
	  let subt = new term ~typ:integer_type (JCTbinary(t1,(`Bsub,`Integer),t2)) in
	  begin match linterms_of_term subt with
	    | None -> a
	    | Some (post,negt) -> new assertion(JCArelation(post,bop,negt))
	  end
      | JCAnot a ->
	  let nota = not_asrt a in
	  begin match nota#node with
	    | JCAnot _ -> a
	    | _ -> linasrt_of_assertion nota
	  end
      | JCAtrue | JCAfalse | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _
      | JCAapp _ | JCAquantifier _ | JCAold _ | JCAat _ | JCAinstanceof _ | JCAbool_term _
      | JCAif _ | JCAmutable _ | JCAeqtype _ | JCAsubtype _ | JCAmatch _ -> a
  in
  linasrt_of_assertion a

let mkinvariant mgr absval =
  if Abstract1.is_top mgr absval then
    true_assertion
  else if Abstract1.is_bottom mgr absval then
    false_assertion
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
(* Simplifying formulas.                                       *)
(*****************************************************************************)
    

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
  match qe#node with
    | JCAtrue -> true
    | _ -> false

(* For scaling: Dnf(make_and(a,b)) + emptiness test by Apron on each disjunct *)
let contradictory =
  let mgr = Polka.manager_alloc_strict () in
  fun a b ->
    (* tautology(make_not(make_and [a;b])) *)
    if Jc_options.debug then
      printf "@[<v 2>[contradictory]@\n%a@\n%a@]@."
	Jc_output.assertion a Jc_output.assertion b;
    let dnf = Atp.dnf(atp_of_asrt(make_and[a;b])) in
    let vars = Atp.fv dnf in
    let vars = List.map Vwp.term vars in
    let vars = List.map Vai.variable_of_term vars in
    let env = Environment.make (Array.of_list vars) [||] in
    let disjuncts = Atp.disjuncts dnf in
    let disjuncts = List.map Atp.conjuncts disjuncts in
    let disjuncts = List.map (List.map asrt_of_atp) disjuncts in
    assert(List.length disjuncts > 0);
    let res = List.fold_left 
      (fun acc conjunct -> acc &&
	 try
	   let cstrs = List.map (linstr_of_assertion env) conjunct in
	   let cstrs = List.map snd cstrs in
	   let dnf = Dnf.make_and cstrs in
	   let absval = Abstract1.top mgr env in
	   let absval = Dnf.test mgr absval dnf in
	   Abstract1.is_bottom mgr absval
	 with Parser.Error _ | Failure _ -> false
      ) true disjuncts
    in
    if debug then 
      printf "@[<v 2>[contradictory] %b@]@." res;
    res

let abstract_overapprox mgr env a =
  let conjuncts = conjuncts a in
  List.fold_left 
    (fun (absval,acc) conjunct ->
       try
	 let dnf = snd (linstr_of_assertion env conjunct) in
	 let absval' = Dnf.test mgr absval dnf in
	 if strictly_stronger mgr absval' absval then
	   absval', acc
	 else
	   absval, conjunct :: acc
       with Parser.Error _ | Failure _ -> 
	 absval, conjunct :: acc
    ) (Abstract1.top mgr env,[]) conjuncts

let simplify =
  let mgr = Polka.manager_alloc_strict () in
  fun ?inva inita ->
    if Jc_options.debug then
      printf "@[<v 2>[simplify]@\n%a@]@." Jc_output.assertion inita;
    let simpla = if tautology inita then true_assertion else
      let dnf = Atp.dnf (atp_of_asrt inita) in
      let vars = Atp.fv dnf in
      let vars = List.map Vwp.term vars in
      let vars = List.map Vai.variable_of_term vars in
      let env = Environment.make (Array.of_list vars) [||] in
      let disjuncts = Atp.disjuncts dnf in
      let disjuncts = List.map Atp.conjuncts disjuncts in
      let disjuncts = List.map (List.map asrt_of_atp) disjuncts in

      let invapprox = match inva with 
	| None -> Abstract1.top mgr env
	| Some inva -> fst (abstract_overapprox mgr env inva)
      in
      let disjuncts = match inva with
	| None -> disjuncts
	| Some inva -> 
	    List.filter (fun conjunct ->
			   not(contradictory (make_and conjunct) inva)
			) disjuncts
      in

      let abstract_disjuncts,other_disjuncts =
	List.fold_right 
	  (fun conjunct (abstractl,otherl) ->
	     try
	       if Jc_options.debug then
		 printf "asrt conjunct : %a@."
		   (Pp.print_list (fun fmt () -> printf " /\\ ")
		      Jc_output.assertion)
		   conjunct;
	       let absval,other_conjuncts = 
		 abstract_overapprox mgr env (make_and conjunct)
	       in
	       if Jc_options.debug then
		 printf "abstract conjunct : %a@." Abstract1.print absval;
	       if Abstract1.is_bottom mgr absval then
		 abstractl, otherl
	       else
		 (absval,other_conjuncts) :: abstractl, otherl
	     with Parser.Error _ | Failure _ ->
	       abstractl, make_and (List.map presentify conjunct) :: otherl
	  ) disjuncts ([],[])
      in
      let abstract_disjuncts =
	List.fold_right
	  (fun (absval,other_conjuncts) acc ->
	     (* Do not consider conjunct if less precise than [inva] *)
	     let skip = 
	       other_conjuncts = [] && stronger mgr invapprox absval 
	     in
	     if skip then acc else
	       (* Remove conjuncts that are weaker than current one *)
	       let acc = 
		 List.filter
		   (fun (av,oc) -> not (oc = [] && stronger mgr absval av)) acc
	       in
	       (* Do not add current conjunct if weaker than another one *)
	       if other_conjuncts = [] && 
		 List.exists (fun (av,_oc) -> stronger mgr av absval) acc 
	       then acc
	       else (absval,other_conjuncts) :: acc
	  ) abstract_disjuncts []
      in
      List.iter (Abstract1.minimize mgr $ fst) abstract_disjuncts;
      let abstract_disjuncts = 
	List.map (fun (absval,other_conjuncts) ->
		    make_and (mkinvariant mgr absval :: other_conjuncts)
		 ) abstract_disjuncts 
      in
      let disjuncts = abstract_disjuncts @ other_disjuncts in
      make_or disjuncts
    in
    if debug then
      printf "@[<v 2>[simplify] initial:@\n%a@]@." Jc_output.assertion inita;
    if debug then
      printf "@[<v 2>[simplify] w.r.t. invariant:@\n%a@]@."
	(print_option Jc_output.assertion) inva;
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
	      let res = simplify (asrt_of_atp qe) in
	      let finv = asrt_of_atp (Atp.dnf (atp_of_asrt finv)) in
	      simplify ~inva:finv (make_not res)
	  | _ ->
	      let qe = (Atp.dnf qe) in
	      if Jc_options.debug then
		printf "@[<v 2>After disjunctive normal form@\n%a@]@." 
		  (fun fmt fm -> Atp.printer fm) qe;
	      let finv = asrt_of_atp (Atp.dnf (atp_of_asrt finv)) in
	      simplify ~inva:finv (asrt_of_atp qe)
	end
    | q -> 
	let finv = asrt_of_atp (Atp.dnf (atp_of_asrt finv)) in
	simplify ~inva:finv (asrt_of_atp q)

let collect_free_vars = 
  fold_term_and_assertion 
    (fun acc t -> match t#node with
       | JCTvar vi -> VarSet.add vi acc
       | _ -> acc) 
    (fun acc a -> match a#node with
       | JCAquantifier(_,vi,a) -> VarSet.remove vi acc
       | _ -> acc)
    VarSet.empty


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


let initialize_target curposts target =
  let collect_sub_terms = 
    fold_term_in_assertion (fun acc t -> match t#node with
			      | JCTvar _ | JCTbinary(_,((`Badd,`Integer) | (`Bsub,`Integer)),_)
			      | JCTunary((`Uminus,`Integer),_) -> acc
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
		 let vit = new term_var vi in
		 let copyvi = copyvar vi in
		 add_inflexion_var curposts copyvi;
		 let t1 = new term_var copyvi in
		 target.jc_target_regular_invariant <-
		   replace_term_in_assertion vit t1 target.jc_target_regular_invariant;
		 target.jc_target_assertion <-
		   replace_term_in_assertion vit t1 target.jc_target_assertion;
		 let bop = equality_operator_for_type vi.jc_var_info_type in
		 let eq = new assertion (JCArelation(t1,bop,vit)) in
		 let eqs = 
		   TermSet.fold (fun t acc ->
				   if raw_strict_sub_term vit t then
				     let t2 = replace_term_in_term ~source:vit ~target:t1 t in
				     if is_integral_type t#typ then
				       let bop = equality_operator_for_type t#typ in
				       let eq = new assertion(JCArelation(t2,bop,t)) in
				       eq::acc
				     else acc
				   else acc
				) ts [eq]
		 in
		 make_and(a::eqs)
	      ) vs true_assertion

let finalize_target ~is_function_level ~pos ~anchor curposts target inva =
  if Jc_options.debug then
    printf "@[<v 2>[finalize_target]@\n%a@]@." Jc_output.assertion inva;
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
    let impla = new assertion(JCAimplies(patha,target.jc_target_assertion)) in
    (* [quanta] is the quantified formula. It quantifies [impla] over the 
     * variables modified.
     *)
    let quanta = 
      VarSet.fold (fun vi a -> new assertion (JCAquantifier(Forall,vi,a))) vs impla
    in
    (* [elima] is the quantifier free version of [quanta].
    *)
    if debug then 
      printf "@[<v 2>[finalize_target] quantified formula@\n%a@]@."
	Jc_output.assertion quanta;
    let elima = quantif_eliminate quanta inva in
    if debug then 
      printf "@[<v 2>[finalize_target] quantifier-free formula@\n%a@]@."
	Jc_output.assertion elima;
    if contradictory elima patha then
      begin
	if Jc_options.debug then
	  printf "%a@[<v 2>No inferred %s@."
	    Loc.report_position target.jc_target_location annot_name;
	None
      end
    else
      begin
	if Jc_options.debug then
	  printf "%a@[<v 2>Inferring %s@\n%a@]@."
	    Loc.report_position target.jc_target_location
	    annot_name Jc_output.assertion elima;
	let elima = reg_annot ~pos ~anchor elima in
	Some elima
      end
	
let rec wp_expr weakpre = 
  let var_of_term = Hashtbl.create 0 in
  (* Terms should be raw only. *)
  let unique_var_for_term t ty =
    try Hashtbl.find var_of_term t
    with Not_found ->
      let vi = Jc_pervasives.var ty (term_name t) in
      Hashtbl.add var_of_term t vi;
      vi
  in
  fun target e curposts ->
    let wp = wp_expr weakpre target in
    if debug then 
      printf "[wp_expr] %a@\n%a@\nfor stat %a@." Loc.report_position e#pos
	(print_option Jc_output.assertion) curposts.jc_post_normal
	Jc_output.expr target.jc_target_expr;
    if debug then 
      printf "[wp_expr] curposts is None? %b@." 
	(curposts.jc_post_normal = None);
    let curposts = match e#node with
      | JCElet(v,e1opt,e2) ->
	  let curposts = wp e2 curposts in
	  let post = 
	    match curposts.jc_post_normal, e1opt with
	      | None, _ -> None
	      | Some a, None -> Some a
	      | Some a, Some e1 ->
		  match term_of_expr e1 with None -> Some a | Some t1 ->
		    let tv = new term_var v in
		    if !Jc_options.annotation_sem = AnnotWeakPre
		      || (!Jc_options.annotation_sem = AnnotStrongPre
			  && mem_term_in_assertion tv a)
		    then
		      let bop = 
			equality_operator_for_type v.jc_var_info_type 
		      in
		      let eq = new assertion (JCArelation(tv,bop,t1)) in
		      Some (make_and [ eq; a ])
		    else Some a
	  in
	  let curposts = add_modified_var curposts v in
	  { curposts with jc_post_normal = post }
      | JCEassign_var(v,e1) ->
	  let tv = new term_var v in
	  let copyv = copyvar v in
	  let tv1 = new term_var copyv in
	  let post = 
	    match curposts.jc_post_normal with None -> None | Some a ->
	      if !Jc_options.annotation_sem = AnnotWeakPre
		|| (!Jc_options.annotation_sem = AnnotStrongPre
		    && mem_term_in_assertion tv a)
	      then
		let a = replace_term_in_assertion tv tv1 a in
		match term_of_expr e1 with None -> Some a | Some t1 ->
		  let bop = equality_operator_for_type v.jc_var_info_type in
		  let eq = new assertion (JCArelation(tv1,bop,t1)) in
		  Some (make_and [ eq; a ])
	      else Some a
	  in
	  add_inflexion_var curposts copyv;
	  let curposts = 
	    if is_function_level curposts then curposts
	    else
	      (* Also add regular variable, for other branches in loop. *)
	      add_modified_var curposts v
	  in
	  let curposts = { curposts with jc_post_normal = post } in
	  wp e1 curposts
      | JCEassign_heap(e1,fi,e2) ->
	  begin match term_of_expr e1 with
	    | None -> curposts (* TODO *)	
	    | Some t1 ->
		let dereft = 
		  new term ~typ:fi.jc_field_info_type 
		    (JCTderef(t1,LabelHere,fi)) 
		in
		let v = unique_var_for_term dereft fi.jc_field_info_type in
		let copyv = copyvar v in
		let tv1 = new term_var copyv in
		let post =
		  match curposts.jc_post_normal with None -> None | Some a ->
		    if !Jc_options.annotation_sem = AnnotWeakPre
		      || (!Jc_options.annotation_sem = AnnotStrongPre
			  && mem_term_in_assertion dereft a)
		    then
		      let a = replace_term_in_assertion dereft tv1 a in
		      match term_of_expr e2 with None -> Some a | Some t2 ->
			let bop = 
			  equality_operator_for_type fi.jc_field_info_type 
			in
			let eq = new assertion (JCArelation(t1,bop,t2)) in
			Some (make_and [ eq; a ])
		    else Some a
		in
		add_inflexion_var curposts copyv;
		let curposts = 
		  if is_function_level curposts then curposts
		  else
		    (* Also add regular variable, for other branches in loop. *)
		    add_modified_var curposts v 
		in
		{ curposts with jc_post_normal = post }
	  end
      | JCEassert(_behav,Ahint,a) -> 
	  (* Hints are not to be used in wp computation, only added to help. *)
	  curposts
      | JCEassert(_behav,_asrt,a1) ->
	  let f = atp_of_asrt a1 in
	  let fvars = Atp.fv f in
	  let varsets = List.map Vwp.term fvars in
	  let varsets = TermSet.of_list varsets in
	  let post = 
	    match curposts.jc_post_normal with None -> None | Some a ->
	      if !Jc_options.annotation_sem = AnnotWeakPre
		|| (!Jc_options.annotation_sem = AnnotStrongPre
		    && mem_any_term_in_assertion varsets a)
	      then
		Some (make_and [ a1; a ])
	      else Some a
	  in
	  { curposts with jc_post_normal = post }
      | JCEblock sl ->
	  List.fold_right wp sl curposts
      | JCEif(test,etrue,efalse) ->
	  let tposts = wp etrue curposts in
	  let ta = raw_asrt_of_expr test in
	  let f = atp_of_asrt ta in
	  let fvars = Atp.fv f in
	  let varsets = List.map Vwp.term fvars in
	  let varsets = TermSet.of_list varsets in
	  
	  let tpost = 
	    match tposts.jc_post_normal with None -> None | Some a -> 
	      if !Jc_options.annotation_sem = AnnotWeakPre
		|| (!Jc_options.annotation_sem = AnnotStrongPre
		    && mem_any_term_in_assertion varsets a)
	      then
		Some (make_and [ ta; a ])
	      else Some a
	  in
	  let fposts = wp efalse curposts in
	  let fpost = 
	    match fposts.jc_post_normal with None -> None | Some a -> 
	      let fa = raw_not_asrt (raw_asrt_of_expr test) in
	      if !Jc_options.annotation_sem = AnnotWeakPre
		|| (!Jc_options.annotation_sem = AnnotStrongPre
		    && mem_any_term_in_assertion varsets a)
	      then
		Some (make_and [ fa; a ])
	      else Some a
	  in
	  let post = match tpost,fpost with
	    | None,opta | opta,None -> opta
		(* TODO: add loc variable v with ta and not v with fa
		   to correctly implement wp *)
	    | Some ta,Some fa -> Some (make_or [ta;fa])
	  in
	  let tvs,_ = pop_modified_vars tposts in
	  let fvs,_ = pop_modified_vars fposts in
	  let vs = VarSet.union tvs fvs in
	  let curposts = add_modified_vars curposts vs in
	  let curposts = { curposts with jc_post_normal = post } in
	  wp test curposts
      | JCEreturn_void | JCEreturn _ -> 
	  { curposts with jc_post_normal = None; }
      | JCEthrow(ei,_) -> (* TODO: link with value caught *)
	  let post = 
	    try Some (List.assoc ei curposts.jc_post_exceptional) 
	    with Not_found -> None 
	  in
	  { curposts with jc_post_normal = post; }
      | JCEpack _ | JCEunpack _ -> 
	  curposts
      | JCEtry(s,hl,fs) ->
	  begin match fs#node with 
	    | JCEblock [] -> ()
	    | _ -> () (* assert false (\* TODO: apply finally stmt to all paths. *\) *)
	  end;
	  let handlpostexcl,handlvs = 
	    List.fold_left 
	      (fun (curpostexcl,curvs) (ei,vio,s) ->
		 let excposts = wp_expr weakpre target s curposts in
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
	  let bodyposts = wp_expr weakpre target s tmpposts in
	  let bodyvs,_ = pop_modified_vars bodyposts in
	  let vs = VarSet.union handlvs bodyvs in
	  let curposts = add_modified_vars curposts vs in
	  { curposts with jc_post_normal = bodyposts.jc_post_normal; }
      | JCEloop(la,ls) ->
	  let curposts = { curposts with jc_post_normal = None; } in
	  let loopposts = push_modified_vars curposts in
	  let loopposts = wp_expr weakpre target ls loopposts in
	  let post = 
	    match finalize_target 
	      ~is_function_level:false ~pos:e#pos ~anchor:e#mark
	      loopposts target (make_and (List.map snd la.jc_loop_invariant))
	    with None -> None | Some infera ->
	      target.jc_target_regular_invariant <- (make_and (List.map snd la.jc_loop_invariant));
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
	    (*       | JCEapp call ->  *)
	    (* 	  let curposts = wp_expr weakpre target s curposts in *)
	    (* 	  let vit = new term_var vi in *)
	    (* 	  let copyvi = copyvar vi in *)
	    (* 	  let t1 = new term_var copyvi in *)
	    (* 	  let post = match curposts.jc_post_normal with *)
	    (* 	    | None -> None *)
	    (* 	    | Some a -> Some(replace_term_in_assertion vit t1 a) *)
	    (* 	  in *)
	    (* 	  add_inflexion_var curposts copyvi; *)
	    (* 	  let curposts =  *)
	    (* 	    if is_function_level curposts then curposts *)
	    (* 	    else *)
	    (* 	      (\* Also add regular variable, for other branches in loop. *\) *)
	    (* 	      add_modified_var curposts vi  *)
	    (* 	  in *)
	    (* 	  { curposts with jc_post_normal = post; } *)
      | JCEapp call -> 
(* 	  let curposts = wp e curposts in *)
	  curposts
      | JCEvar _
      | JCEconst _ -> 
	  curposts
      | JCEderef(e1,_)
      | JCEunary(_,e1)
      | JCEalloc(e1,_)
      | JCEaddress(_,e1)
      | JCEoffset(_,e1,_)
      | JCEreal_cast(e1,_)
      | JCErange_cast(e1,_)
      | JCEbitwise_cast(e1,_)
      | JCEinstanceof(e1,_)
      | JCEcast(e1,_)
      | JCEfree e1 ->
	  wp e1 curposts
      | JCEshift(e1,e2)
      | JCEbinary(e1,_,e2) ->
	  wp e1 (wp e2 curposts)
      | JCEcontract _ -> assert false (* TODO *)
      | JCEmatch _ -> assert false (* TODO *)
    in
    if e == target.jc_target_expr then
      let inita = initialize_target curposts target in
      assert (curposts.jc_post_normal = None);
      if debug then 
	printf "[wp_expr] found target %a@\n%a@." Loc.report_position e#pos
	  Jc_output.assertion inita;
      { curposts with jc_post_normal = Some inita; }
    else curposts

(* let rec record_wp_invariants weakpre s = *)
(*   match s#node with *)
(*     | JCElet(_,_,s) ->  *)
(* 	record_wp_invariants weakpre s *)
(*     | JCEblock sl -> *)
(* 	List.iter (record_wp_invariants weakpre) sl *)
(*     | JCEmatch _ -> assert false (\* TODO *\) *)
(*     | JCEif(_,ts,fs) -> *)
(* 	record_wp_invariants weakpre ts; *)
(* 	record_wp_invariants weakpre fs *)
(*     | JCEtry(s,hl,fs) -> *)
(* 	record_wp_invariants weakpre s; *)
(* 	List.iter (fun (_,_,s) -> record_wp_invariants weakpre s) hl; *)
(* 	record_wp_invariants weakpre fs *)
(*     | JCEloop(la,ls) -> *)
(* 	let loop_invariants = weakpre.jc_weakpre_loop_invariants in *)
(* 	begin try *)
(* 	  let loopinvs = Hashtbl.find loop_invariants la.jc_loop_tag in *)
(* 	  la.jc_loop_invariant <- [[],make_and (loopinvs :: List.map snd la.jc_loop_invariant)] *)
(* 	with Not_found -> () end *)
(*     | JCEassign_var _ | JCEassign_heap _ | JCEassert _  *)
(*     | JCEreturn_void | JCEreturn _ | JCEthrow _ | JCEpack _ | JCEunpack _  *)
(*     | JCEapp _ -> *)
(* 	() *)
(*     | _ -> assert false (\* TODO *\) *)

let wp_function targets funpre (f,pos,spec,body) =
  if debug then printf "[wp_function] %s@." f.jc_fun_info_name;
  let weakpre = {
    jc_weakpre_loop_invariants = Hashtbl.create 0;
  } in
  let infer_req = ref [] in
  List.iter 
    (fun target ->
       if Jc_options.debug then
	 printf "%a@[<v 2>Infer precondition for assertion:@\n%a@]\
@\n@[<v 2>under invariant:@\n%a@]@." 
	   Loc.report_position target.jc_target_location 
	   Jc_output.assertion target.jc_target_assertion
	   Jc_output.assertion target.jc_target_regular_invariant;
       let initposts = {
	 jc_post_normal = None;
	 jc_post_exceptional = [];
	 jc_post_modified_vars = [];
	 jc_post_inflexion_vars = ref VarSet.empty;
       } in
       let initposts = push_modified_vars initposts in
       let posts = match !Jc_options.annotation_sem with
	 | AnnotNone | AnnotInvariants -> 
	     assert false (* [wp_function] should not be called *)
	 | AnnotElimPre ->
	     (* Directly eliminate modified variables *)
	     let vs1 = collect_free_vars target.jc_target_regular_invariant in
	     let vs2 = collect_free_vars target.jc_target_assertion in
	     let vs = VarSet.union vs1 vs2 in
	     let qvs = 
	       VarSet.filter
		 (fun v -> 
		    not v.jc_var_info_formal || v.jc_var_info_assigned
		 ) vs 
	     in
	     let curposts = add_modified_vars initposts qvs in
	     let inita = initialize_target curposts target in
	     { curposts with jc_post_normal = Some inita; }
	 | AnnotWeakPre | AnnotStrongPre ->
	     (* Compute weakest precondition of formula *)
	     wp_expr weakpre target body initposts 
       in
       match finalize_target ~is_function_level:true ~pos 
	 ~anchor:f.jc_fun_info_name posts target funpre
       with 
	 | None -> () (* precondition inconsistant or redundant *)
	 | Some infera -> (* valid precondition *)
	     infer_req := infera :: !infer_req
    ) targets;
  (* Remove redundancy in precondition inferred *)
  let inferred = simplify (make_and !infer_req) in
  spec.jc_fun_requires <- make_and [ spec.jc_fun_requires; inferred ];
  if Jc_options.verbose then
    printf "@[<v 2>Inferring precondition for function %s:@\n%a@]@." 
      f.jc_fun_info_name Jc_output.assertion inferred


(*****************************************************************************)
(* Augmenting loop invariants.                                               *)
(*****************************************************************************)

(* let collect_immediate_targets targets s = *)
(*   (\* Special version of [fold_expr] different from the one  *)
(*    * in [Jc_iterators] in that fpost is called after the body expr  *)
(*    * of the try block. *)
(*    *\) *)
(*   let rec fold_expr fpre fpost acc s = *)
(*     let ite = fold_expr fpre fpost in *)
(*     let acc = fpre acc s in *)
(*     let acc = match s#node with *)
(*       | JCEconst _  *)
(*       | JCEvar _  *)
(*       | JCEreturn_void -> *)
(* 	  acc *)
(*       | JCEthrow(_exc,e1_opt) -> *)
(* 	  Option_misc.fold_left ite acc e1_opt *)
(*       | JCEbinary(e1,_,e2)  *)
(*       | JCEshift(e1,e2) *)
(*       | JCEassign_heap(e1,_,e2) -> *)
(* 	  let acc = ite acc e1 in *)
(* 	  ite acc e2 *)
(*       | JCEunary(_,e1) *)
(*       | JCEderef(e1,_) *)
(*       | JCEoffset(_,e1,_) *)
(*       | JCEaddress(_,e1) *)
(*       | JCEcast(e1,_) *)
(*       | JCEbitwise_cast(e1,_)  *)
(*       | JCErange_cast(e1,_)  *)
(*       | JCEinstanceof(e1,_)  *)
(*       | JCEreal_cast(e1,_) *)
(*       | JCEunpack(_,e1,_) *)
(*       | JCEpack(_,e1,_) *)
(*       | JCEassign_var(_,e1)  *)
(*       | JCEalloc(e1,_)  *)
(*       | JCEfree e1  *)
(*       | JCEreturn(_,e1) -> *)
(* 	  ite acc e1 *)
(*       | JCElet(_,e1_opt,e2) -> *)
(* 	  let acc = Option_misc.fold_left ite acc e1_opt in *)
(* 	  ite acc e2 *)
(*       | JCEapp call -> *)
(* 	  List.fold_left ite acc call.jc_call_args *)
(*       | JCEif(e1,e2,e3) -> *)
(* 	  let acc = ite acc e1 in *)
(* 	  let acc = ite acc e2 in *)
(* 	  ite acc e3 *)
(*       | JCEmatch(e, ptl) -> *)
(* 	  let acc = ite acc e in *)
(* 	  List.fold_left (fun acc (_, e) -> ite acc e) acc ptl *)
(*       | JCEblock el -> *)
(* 	  List.fold_left ite acc el *)
(*       | JCEtry(e1,catches,finally) -> *)
(* 	  let acc = ite acc e1 in *)
(* 	  let acc =  *)
(* 	    List.fold_left (fun acc (_exc,_vi_opt,e) -> ite acc e) acc catches *)
(* 	  in *)
(* 	  ite acc finally *)
(*       | JCEassert(_behav,_asrt,a) -> *)
(* 	  ita acc a *)
(*       | JCEloop(la,e1) -> *)
(* 	  let acc = ite acc e1 in *)
(* 	  let acc =  *)
(* 	    List.fold_left  *)
(* 	      (fun acc (_behav,a) -> ita acc a) acc la.jc_loop_invariant *)
(* 	  in *)
(* 	  let acc = ita acc la.jc_free_loop_invariant in *)
(* 	  Option_misc.fold_left itt acc la.jc_loop_variant *)
(*       | JCEcontract(a_opt,t_opt,_v,behavs,e) -> *)
(* 	  let acc = Option_misc.fold_left ita acc a_opt in *)
(* 	  let acc = Option_misc.fold_left itt acc t_opt in *)
(* 	  let acc =  *)
(* 	    List.fold_left  *)
(* 	      (fun acc (_loc,_name,behav) -> *)
(* 		 fold_sub_behavior acc behav *)
(* 	      ) acc behavs *)
(* 	  in *)
(* 	  ite acc e *)

(*       | JCEif(_,ts,fs) -> *)
(*   	  let acc = fold_expr fpre fpost acc ts in *)
(*   	  fold_expr fpre fpost acc fs *)
(*       | JCEtry(s,hl,fs) -> *)
(*   	  let acc = fold_expr fpre fpost acc s in *)
(*           let acc = fpost acc s in *)
(*   	  let acc = *)
(*   	    List.fold_left (fun acc (_,_,s) -> *)
(*   			      fold_expr fpre fpost acc s *)
(*   			   ) acc hl *)
(*   	  in *)
(*   	  fold_expr fpre fpost acc fs *)
(*       | JCEloop(_,ls) -> *)
(*   	  fold_expr fpre fpost acc ls *)
(*       | JCEreturn _ | JCEthrow _ | JCEassert _ | JCEassign_var _ | JCEapp _ *)
(*       | JCEassign_heap _ | JCEpack _ | JCEunpack _ | JCEreturn_void -> *)
(*   	  acc *)
(*       | _ -> assert false (\* TODO *\) *)

(*     in *)
(*     fpost acc s *)
(*   in *)

(*   (\* First checks at start of function should be selected *\) *)
(*   let in_select_zone = ref true in *)

(*   let select_pre acc s = *)
(*     match s#node with *)
(*       | JCEassert a -> *)
(*   	  if debug then printf "[select_pre] consider target@."; *)
(*   	  if debug then printf "[select_pre] in zone ? %b@." !in_select_zone; *)
(*   	  if !in_select_zone then *)
(*   	    let target = target_of_assertion s s#pos a in *)
(*   	    if debug then printf "[select_pre] adding in_zone target@."; *)
(*   	    target::acc *)
(*   	  else acc *)
(*       | JCEloop _ -> *)
(*   	  if debug then printf "[select_pre] in_zone true@."; *)
(*   	  in_select_zone := true; acc *)
(*       | JCElet _ | JCEblock _ | JCEassign_var _ *)
(*       | JCEassign_heap _ | JCEpack _ | JCEunpack _ | JCEtry _ -> *)
(*           (\* Allowed with [JCEtry] thanks to patched [fold_expr]. *\) *)
(*   	  acc *)
(*       | JCEapp _ | JCEif _ | JCEreturn _ | JCEthrow _ *)
(*       | JCEreturn_void -> *)
(*   	  if debug then printf "[select_pre] in_zone false@."; *)
(*   	  in_select_zone := false; acc *)
(*       |  _ -> assert false (\* TODO *\) *)
(*   in *)

(*   let select_post acc s = *)
(*     match s#node with *)
(*       | JCEloop _ -> *)
(*   	  if debug then printf "[select_post] in_zone false@."; *)
(*   	  in_select_zone := false; acc *)
(*       | _ -> acc *)
(*   in *)
(*   fold_expr select_pre select_post targets s *)

let rec backprop_expr target s curpost =
  if debug then 
    printf "[backprop_expr] %a@." Loc.report_position s#pos;
  let curpost = match s#node with
    | JCElet(vi,eo,s) ->
	let curpost = backprop_expr target s curpost in
	begin match curpost with None -> None | Some a -> 
	  match eo with None -> Some a | Some e ->
	    match term_of_expr e with None -> Some a | Some t2 ->
	      let t1 = new term_var vi in
	      Some(replace_term_in_assertion t1 t2 a)
	end
    | JCEassign_var(vi,e) ->
	begin match curpost with None -> None | Some a -> 
	  match term_of_expr e with None -> Some a | Some t2 ->
	    let t1 = new term_var vi in
	    Some(replace_term_in_assertion t1 t2 a)
	end
    | JCEassign_heap _ | JCEassert _ | JCEpack _ | JCEunpack _ ->
	curpost
    | JCEblock sl ->
	List.fold_right (backprop_expr target) sl curpost
    | JCEreturn_void | JCEreturn _ | JCEthrow _ ->
	assert (curpost = None); curpost
    | JCEtry(s,hl,fs) ->
	assert (curpost = None); 
	let curpost = backprop_expr target fs None in
	assert (curpost = None);
        List.iter (fun (_,_,s) ->
  		     let curpost = backprop_expr target s None in
		     assert (curpost = None);
		  ) hl;
	backprop_expr target s None
    | JCEloop(la,ls) ->
	let curpost = backprop_expr target ls curpost in
	begin
          match curpost with None -> () | Some propa ->
	    if not (contradictory propa (make_and (List.map snd la.jc_loop_invariant))) then
              begin
                if Jc_options.debug then
                  printf 
	            "%a@[<v 2>Back-propagating loop invariant@\n%a@]@."
                    Loc.report_position s#pos
                    Jc_output.assertion propa;
	        la.jc_loop_invariant <- [[],make_and (propa :: List.map snd la.jc_loop_invariant)]
              end
	end;
	None
	  (*     | JCEcall(_,_,s) -> *)
	  (* 	assert (curpost = None); *)
	  (* 	let curpost = backprop_expr target s None in *)
	  (* 	assert (curpost = None); curpost *)
    | JCEif(_,ts,fs) ->
	assert (curpost = None);
	let curpost = backprop_expr target ts None in
	assert (curpost = None);
	let curpost = backprop_expr target fs None in
	assert (curpost = None); None
    | _ -> assert false (* TODO *)
  in
  if s == target.jc_target_expr then
    begin 
      assert (curpost = None);
      Some target.jc_target_assertion
    end
  else curpost

let backprop_function targets (fi,fs,sl) =
  if debug then printf "[backprop_function]@.";
  List.iter (fun target ->
	       ignore(backprop_expr target sl None)
	    ) targets


(*****************************************************************************)
(* Collecting assertions.                                                    *)
(*****************************************************************************)
      
let target_of_assertion s loc a = 
  { 
    jc_target_expr = s;
    jc_target_location = loc;
    jc_target_assertion = a;
    jc_target_regular_invariant = false_assertion;
    jc_target_propagated_invariant = false_assertion;
  }

(* Collect safety assertions from the evaluation of expression [e]. 
 * Currently, 3 kinds of assertions are collected, that check for:
 * - memory safety 
 * - no integer overflows
 * - no division by zero
 *)
let collect_expr_targets e =
  (* Collect memory safety assertions. *)
  let collect_memory_access e1 fi =
    match term_of_expr e1 with None -> [] | Some t1 ->
      match destruct_pointer t1 with None,_ -> [] | Some ptrt,offopt ->
	let offt = match offopt with
	  | None -> new term ~typ:integer_type (JCTconst(JCCinteger"0"))
	  | Some offt -> offt
	in
	let st = struct_of_term ptrt in
	let mint = new term ~typ:integer_type (JCToffset(Offset_min,ptrt,st)) in
	let maxt = new term ~typ:integer_type (JCToffset(Offset_max,ptrt,st)) in
	let mina = new assertion(JCArelation(mint,(`Ble,`Integer),offt)) in
	let maxa = new assertion(JCArelation(offt,(`Ble,`Integer),maxt)) in
	[mina;maxa]
  in
  (* Collect absence of integer overflow assertions. *)
  let collect_integer_overflow ei e1 =
    match term_of_expr e1 with None -> [] | Some t1 ->
      let mint = new term ~typ:integer_type
	(JCTconst (JCCinteger (Num.string_of_num ei.jc_enum_info_min)))
      in
      let maxt = new term ~typ:integer_type
	(JCTconst(JCCinteger (Num.string_of_num ei.jc_enum_info_max)))
      in
      let mina = new assertion (JCArelation (mint, (`Ble,`Integer), t1)) in
      let maxa = new assertion (JCArelation (t1, (`Ble,`Integer), maxt)) in
      [mina; maxa]
  in
  (* Collect absence of division by zero assertions. *)
  let collect_zero_division e =
    match term_of_expr e with None -> [] | Some t ->
      let zero = new term ~typ:integer_type (JCTconst(JCCinteger "0")) in
      [new assertion(JCArelation(t,(`Bneq,`Integer),zero))]
  in
  let collect e = 
    let asrts = match e#node with
      | JCEderef(e1,fi) -> collect_memory_access e1 fi
      | JCErange_cast(e1,ei) -> 
	  if !Jc_options.int_model = IMbounded then
	    collect_integer_overflow ei e1
	  else []
      | JCEbinary(_,(`Bdiv,`Integer),e2) -> collect_zero_division e2
      | JCEapp call ->
	  let fi = match call.jc_call_fun with JCfun f -> f | _ -> assert false in
	  let els = call.jc_call_args in
	  let _,_,fs,_ = 
            Hashtbl.find Jc_typing.functions_table fi.jc_fun_info_tag 
          in
          (* Collect preconditions of functions called. *)
          let reqa = fs.jc_fun_requires in
          let reqa = 
	    List.fold_left2 (fun a param arg ->
			       match term_of_expr arg with None -> true_assertion | Some targ ->
				 replace_term_in_assertion (new term_var param) targ a
			    ) reqa fi.jc_fun_info_parameters els
          in
	  let reqa = regionalize_assertion reqa call.jc_call_region_assoc in
          conjuncts reqa
      | JCEassert(_,Ahint, a) -> 
	  (* Hints are not to be proved by abstract interpretation, 
	     only added to help it. *)
	  []
      | JCEassert(_,_, a) -> 
	  (* Consider separately each conjunct in a conjunction. *)
	  conjuncts a
      | JCEassign_heap (e1, fi, _e2) ->
	  collect_memory_access e1 fi
      | JCElet(_,None,_) | JCEblock _ | JCEif _ | JCEtry _ | JCEloop _
      | JCEreturn_void | JCEreturn _ | JCEthrow _ 
      | JCElet _ | JCEassign_var _ 
      | JCEpack _ | JCEunpack _ | JCEshift _ | JCEmatch _ | JCEfree _ 
      | JCEalloc _ | JCEoffset _ | JCEreal_cast _ | JCEinstanceof _ 
      | JCEunary _ | JCEvar _ | JCEconst _ | JCEcast _ | JCEbinary _ 
      | JCEbitwise_cast _ | JCEaddress _ ->
	  []
      | JCEcontract _ -> assert false (* TODO *)
    in
    let asrts = List.map normalize_assertion asrts in
    List.map (target_of_assertion e e#pos) asrts
  in
  IExpr.fold_left (fun acc e -> collect e @ acc) [] e
    
let collect_expr_asserts e = 
  match term_of_expr e with None -> [] | Some _ ->
    let targets = collect_expr_targets e in
    List.map (fun target -> target.jc_target_assertion) targets
      
let rec collect_targets filter_asrt targets s =
  let candidates = List.rev (collect_expr_targets s) in
  List.filter (fun target -> filter_asrt target.jc_target_assertion) candidates


let pointer_terms_table = ref (Hashtbl.create 0)

let set_equivalent_terms t1 t2 = 
  let tl = 
    try 
      Hashtbl.find !pointer_terms_table t2#node
    with Not_found -> [] 
  in
  let tl = List.filter (fun t -> t <> t1) tl in
  Hashtbl.replace !pointer_terms_table t1#node (t2 :: tl)



(*****************************************************************************)
(* Performing abstract interpretation.                                       *)
(*****************************************************************************)

let apply_to_current_invariant ?(propagated=false) f curinvs =
  let normal = curinvs.jc_absinv_normal in
  let prop = normal.jc_absval_propagated in
  (* Always apply transformation to propagated invariant *)
  let curinvs = 
    { curinvs with jc_absinv_normal = 
	{ normal with jc_absval_propagated = f prop } }
  in
  (* Selectively apply transformation to regular invariant *)
  if propagated then curinvs else
    let normal = curinvs.jc_absinv_normal in
    let pre = normal.jc_absval_regular in
    { curinvs with jc_absinv_normal = 
	{ normal with jc_absval_regular = f pre } }
      
let simple_test_assertion mgr a pre =
  let env = Abstract1.env pre in
  let rec extract_environment_and_dnf env a =
    match a#node with
      | JCAtrue -> env,Dnf.true_
      | JCAfalse -> env,Dnf.false_
      | _ when is_constant_assertion a ->
	  (* 'constant' assertions (eg: 0 <= 1) do not have to be tested
	     (Nicolas) *)
	  env,Dnf.true_ 
      | JCArelation (t1, (`Bneq,`Integer), t2) ->
	  let infa = new assertion (JCArelation(t1, (`Blt,`Integer), t2)) in
	  let supa = new assertion (JCArelation(t1, (`Bgt,`Integer), t2)) in
	  let env, dnf1 = extract_environment_and_dnf env infa in
	  let env, dnf2 = extract_environment_and_dnf env supa in
	  env, Dnf.make_or [dnf1; dnf2]
      | JCArelation (t1, bop, t2) ->
	  if bop = (`Beq,`Pointer) then set_equivalent_terms t1 t2;
	  let env, be = linstr_of_assertion env a in
	  let env, bemin = offset_min_linstr_of_assertion env a in
	  let env, bemax = offset_max_linstr_of_assertion env a in
	  let dnf = Dnf.make_and [be; bemin; bemax] in
	  if debug then 
	    Format.printf "Dnf %a@." Dnf.print dnf;
	  env, dnf
      | JCAand al ->
	  List.fold_left 
	    (fun (env,dnf1) a ->
	       let env,dnf2 = extract_environment_and_dnf env a in
	       env,Dnf.make_and [dnf1;dnf2]
	    ) (env,Dnf.true_) al
      | JCAor al ->
	  List.fold_left 
	    (fun (env,dnf1) a ->
	       let env,dnf2 = extract_environment_and_dnf env a in
	       env,Dnf.make_or [dnf1;dnf2]
	    ) (env,Dnf.false_) al
      | JCAnot a ->
	  let nota = not_asrt a in
	  begin match nota#node with
	    | JCAnot _ -> env, Dnf.true_
	    | _ -> extract_environment_and_dnf env nota
	  end
      | JCAapp app ->
	  begin match unfolding_of_app app with
	    | Some a -> extract_environment_and_dnf env a
	    | None -> env, Dnf.true_
	  end
      | JCAimplies _ | JCAiff _
      | JCAquantifier _ | JCAold _ | JCAat _ | JCAinstanceof _ | JCAbool_term _
      | JCAif _ | JCAmutable _ | JCAeqtype _ | JCAsubtype _ | JCAmatch _ -> env,Dnf.true_
  in
  let env, dnf = extract_environment_and_dnf env a in
  let pre = Abstract1.change_environment mgr pre env false in
  Dnf.test mgr pre dnf

let test_expr ~(neg:bool) mgr e pre =
  try 
    let a = asrt_of_expr e in
    let a = if neg then not_asrt a else a in
    simple_test_assertion mgr a pre 
  with Failure "Not an assertion" -> pre

(* Assigns expression [e] to abstract variable [va] in abstract value [pre]. *)
let assign_variable mgr va e pre =
  let env0 = Abstract1.env pre in
  let env = 
    if Environment.mem_var env0 va then env0 
    else Environment.add env0 [|va|] [||] 
  in
  match linstr_of_expr env e with
    | Some (env, str) ->
	if debug then printf "[assign_variable] str %s@." str;
	(* Assignment can be treated precisely. *)
	let lin = 
	  try Parser.linexpr1_of_string env str
	  with Parser.Error msg -> printf "%s@." msg; assert false
	in
	let pre = Abstract1.change_environment mgr pre env false in
	Abstract1.assign_linexpr mgr pre va lin None
    | None ->
	if debug then printf "[assign_variable] no str@.";
	(* Try over-approximate treatment of assignment. *)
	let pre =
	  if Environment.mem_var env0 va then
	    Abstract1.forget_array mgr pre [|va|] false
	  else pre
	in
	match term_of_expr e with
	  | Some te ->
	      (* Assignment treated as an equality test. *)
	      let t = Vai.term va in
	      let a = new assertion(JCArelation(t,(`Beq,`Integer),te)) in
	      simple_test_assertion mgr a pre
	  | None ->
	      (* Assignment treated as a forget operation. *)
	      pre

let assign_offset_variable mgr va ok e pre =
  let env0 = Abstract1.env pre in
  let env = 
    if Environment.mem_var env0 va then env0 
    else Environment.add env0 [|va|] [||] 
  in
  let forget_vars = [] in
  let forget_vars = Array.of_list forget_vars in
  let pre = Abstract1.forget_array mgr pre forget_vars false in
  match offset_linstr_of_expr env ok e with
    | Some(env,str) ->
	(* Assignment can be treated precisely. *)
	let lin = 
	  try Parser.linexpr1_of_string env str
	  with Parser.Error msg -> printf "%s@." msg; assert false
	in
	let pre = Abstract1.change_environment mgr pre env false in
	Abstract1.assign_linexpr mgr pre va lin None
    | None ->
	(* Assignment treated as a forget operation. *)
	if Environment.mem_var env0 va then
	  Abstract1.forget_array mgr pre [|va|] false
	else pre

let assign_expr mgr t e pre =
  (* Choice: terms that depend on the term assigned to are removed from
     the abstract value -before- treating the assignment. *)
  let env = Abstract1.env pre in
  let integer_vars = Array.to_list (fst (Environment.vars env)) in
  let forget_vars = List.filter 
    (fun va' ->
       let t' = Vai.term va' in 
       (not (raw_term_equal t t')) && term_depends_on_term t' t
    ) integer_vars
  in
  let forget_vars = Array.of_list forget_vars in
  let pre = Abstract1.forget_array mgr pre forget_vars false in
  (* Propagate knowledge on abstract variables on the rhs of the assignment
     to equivalent abstract variables on the lhs. *)
  let pre = match term_of_expr e with
    | None -> pre
    | Some te ->
	let constr_vars = List.filter 
	  (fun va -> 
	     not (Abstract1.is_variable_unconstrained mgr pre va)
	  ) integer_vars
	in
	List.fold_left 
	  (fun pre va' ->
	     let t' = Vai.term va' in
	     if raw_strict_sub_term te t' then 
	       let lhst = 
		 replace_term_in_term ~source:te ~target:t t' 
	       in
	       let a = new assertion (JCArelation (lhst, (`Beq,`Integer), t')) in
	       simple_test_assertion mgr a pre
	     else pre
	  ) pre constr_vars
  in
  (* special case: t1 : pointer = t2 : pointer *)
  begin
    try 
      let t1 = t in
      let t2 = p_term_of_expr e in
      match t1#typ, t2#typ with
	| JCTpointer _, JCTpointer _ -> 
	    set_equivalent_terms t1 t2
	| _ -> ()
    with _ -> () 
  end;
  (* Assign abstract variables. *)
  let pre = 
    if Vai.has_variable t then
      assign_variable mgr (Vai.variable t) e pre 
    else pre
  in
  let pre = 
    if Vai.has_offset_min_variable t then
      begin
	let va = Vai.offset_min_variable t in
	assign_offset_variable mgr va Offset_min_kind e pre 
      end
    else pre
  in
  let pre = 
    if Vai.has_offset_max_variable t then
      begin
	let va = Vai.offset_max_variable t in
	assign_offset_variable mgr va Offset_max_kind e pre
      end
    else pre
  in pre

let assign_heap mgr r fi pre =
  if debug then 
    printf "[assign_heap]%a@." Region.print r;
  if !Jc_options.separation_sem = SepRegions then
    assert (not (is_dummy_region r));
  let env = Abstract1.env pre in
  let integer_vars = Array.to_list (fst (Environment.vars env)) in
  let forget_vars = List.filter 
    (fun va ->
       let t = Vai.term va in
       let is_deref_field t = match t#node with
	 | JCTderef(_,_,fi') -> FieldOrd.equal fi fi'
	 | _ -> false
       in
       let rec has_memory acc t =
	 if acc || 
	   (is_deref_field t &&
	      (not (!Jc_options.separation_sem = SepRegions)
	       || Region.equal t#region r)) then
	     (* cont = *)false,(* acc = *)true
	 else
	   match t#node with
	     | JCToffset(_,t',_) -> false,has_sub_memory acc t'
	     | _ -> true,acc
       and has_sub_memory acc t =
	 fold_sub_term fold_rec_term has_memory acc t
       in
       let res = fold_rec_term has_memory false t in
       if debug then 
	 printf "[assign_heap]%a:%b@." Var.print va res;
       res
    ) integer_vars
  in
  let forget_vars = Array.of_list forget_vars in
  Abstract1.forget_array mgr pre forget_vars false

let test_assertion ?propagated mgr a curinvs =
  apply_to_current_invariant ?propagated (simple_test_assertion mgr a) curinvs
    
let test_expr ~(neg:bool) mgr e curinvs =
  apply_to_current_invariant (test_expr ~neg mgr e) curinvs

let assign_variable mgr va e curinvs =
  apply_to_current_invariant (assign_variable mgr va e) curinvs

let assign_offset_variable mgr va ok e curinvs =
  apply_to_current_invariant (assign_offset_variable mgr va ok e) curinvs

let assign_expr mgr t e curinvs =
  apply_to_current_invariant (assign_expr mgr t e) curinvs
    
let assign_heap mgr r topt fi curinvs =
  apply_to_current_invariant (assign_heap mgr r fi) curinvs 

let keep_extern mgr fi post =
  let integer_vars = 
    Array.to_list (fst (Environment.vars (Abstract1.env post)))
  in
  let to_duplicate t =
    fold_term 
      (fun (acc1, acc2) t -> try 
	 let tl = Hashtbl.find !pointer_terms_table t#node in
	 t :: acc1, tl :: acc2
       with Not_found -> acc1, acc2) 
      ([], []) t
  in
  let integer_vars, strl =
    List.fold_left 
      (fun (acc1, acc2) va ->
	 try
	   let t = Vai.term va in
	   let tl1, tl2 = to_duplicate t in
	   let tl = List.fold_left2
	     (fun acc t1 tl ->
		if t1 == t then acc else
		  (List.map (fun t2 -> replace_term_in_term t1 t2 t) tl) @ acc)
	     [] tl1 tl2
	   in
	   let vars = List.map Vai.variable tl in
	   let vars = List.filter (fun va -> not (List.mem va acc1)) vars in
	   let vars = List.fold_left 
	     (fun acc va -> if (List.mem va acc) then acc else va :: acc) 
	     [] vars 
	   in
	   let strl = List.map 
	     (fun v -> (Var.to_string v) ^ "=" ^ (Var.to_string va)) 
	     vars 
	   in
	   vars @ acc1, strl @ acc2
	 with Not_found -> acc1, acc2)
      (integer_vars, []) integer_vars
  in
  let env = try Environment.make (Array.of_list integer_vars) [||] 
  with Failure msg -> printf "%s@." msg; assert false in
  let post = Abstract1.change_environment mgr post env false in
  let lincons = Parser.lincons1_of_lstring env strl in
  let post = meet mgr post (Abstract1.of_lincons_array mgr env lincons) in
  let term_has_local_var t =
    fold_term 
      (fun acc t -> match t#node with
	 | JCTvar vi -> 
	     acc || (not vi.jc_var_info_static  &&
		       not (vi == fi.jc_fun_info_result) &&
		       not (List.mem vi fi.jc_fun_info_parameters))
	 | _ -> acc
      ) false t
  in
  let extern_vars = 
    List.filter (fun va ->
		   let t = Vai.term va in not (term_has_local_var t)
		) integer_vars
  in
  let extern_vars = Array.of_list extern_vars in
  let extern_env = Environment.make extern_vars [||] in
  Abstract1.change_environment mgr post extern_env false

let find_target_assertions targets e =
  List.fold_left 
    (fun acc target -> 
       if target.jc_target_expr == e then target :: acc else acc
    ) [] targets

let return_abstract_value mgr postret e absval1 =
  let key = ref e in
  try 
    let absval2 = Hashtbl.find postret key in
    let absval = join_abstract_value mgr absval2 absval1 in
    Hashtbl.replace postret key absval
  with Not_found ->
    Hashtbl.replace postret key absval1

let rec ai_inter_function_call mgr iai abs pre fi loc fs sl el =
  assert false
    (*   let pre,formal_vars = *)
    (*     List.fold_left2 *)
    (*       (fun (pre,acc) vi e -> *)
    (* 	 let t = new term_var vi in *)
    (* 	 let pre,acc = if Vai.has_variable t then *)
    (* 	   let va = Vai.variable t in *)
    (* 	   assign_variable mgr va e pre, *)
    (* 	   va :: acc else pre,acc  *)
    (* 	 in *)
    (* 	 let pre,acc = if Vai.has_offset_min_variable t then *)
    (* 	   let va = Vai.offset_min_variable t in *)
    (* 	     assign_offset_variable mgr va Offset_min_kind e pre, *)
    (* 	     va :: acc else pre,acc  *)
    (* 	 in *)
    (* 	 let pre,acc = if Vai.has_offset_max_variable t then *)
    (* 	   let va = Vai.offset_max_variable t in *)
    (* 	     assign_offset_variable mgr va Offset_max_kind e pre, *)
    (* 	   va :: acc else pre,acc  *)
    (* 	 in *)
    (*          pre,acc) *)
    (*       (pre,[]) fi.jc_fun_info_parameters el *)
    (*   in *)
    (*   let formal_vars = List.filter (fun v -> not (Environment.mem_var (Abstract1.env pre) v)) formal_vars in *)
    (*   let formal_vars = Array.of_list formal_vars in *)
    (*   let env = try Environment.add (Abstract1.env pre) formal_vars [||] with _ -> assert false in *)
    (*   let pre = keep_extern mgr fi pre in *)
    (*   let pre = try Abstract1.change_environment mgr pre env false with _ -> assert false in *)
    (*   let function_pre =  *)
    (*     try Hashtbl.find iai.jc_interai_function_preconditions fi.jc_fun_info_tag  *)
    (*     with Not_found -> Abstract1.bottom mgr (Abstract1.env pre)  *)
    (*   in *)
    (*     begin *)
    (*       let old_pre = Abstract1.copy mgr function_pre in *)
    (*       let function_pre, fixpoint_reached =  *)
    (* 	if fi.jc_fun_info_is_recursive then *)
    (* 	  let num =  *)
    (* 	    try Hashtbl.find iai.jc_interai_function_nb_iterations fi.jc_fun_info_tag *)
    (* 	    with Not_found -> 0 *)
    (* 	  in *)
    (* 	    Hashtbl.replace iai.jc_interai_function_nb_iterations fi.jc_fun_info_tag  *)
    (* 	      (num + 1); *)
    (* 	    if num < abs.jc_absint_widening_threshold then *)
    (* 	      begin *)
    (* 		let function_pre = join mgr function_pre pre in *)
    (* 		if num = 0 then  *)
    (* 		  Hashtbl.replace iai.jc_interai_function_init_pre  *)
    (* 		    fi.jc_fun_info_tag function_pre; *)
    (* 		function_pre, false *)
    (* 	      end *)
    (* 	    else *)
    (* 	      begin *)
    (* 		let copy_pre = Abstract1.copy mgr pre in *)
    (* 		let function_pre = widening mgr function_pre copy_pre in *)
    (* 		  if is_eq mgr old_pre function_pre then *)
    (* 		    begin *)
    (* 		      let init_pre =  *)
    (* 			Hashtbl.find iai.jc_interai_function_init_pre fi.jc_fun_info_tag in *)
    (* 		      let function_pre = join mgr function_pre init_pre in *)
    (* 			(\* Hashtbl.replace iai.jc_interai_function_preconditions fi.jc_fun_info_tag function_pre;*\) *)
    (* 			function_pre, true *)
    (* 		    end *)
    (* 		  else *)
    (* 		      function_pre, false *)
    (* 	      end *)
    (* 	else *)
    (* 	  begin *)
    (* 	    let function_pre = join mgr function_pre pre in *)
    (* 	    function_pre, false; *)
    (* 	  end *)
    (*       in *)
    (*       let pre_has_changed = not (is_eq mgr old_pre function_pre) in *)
    (* 	if pre_has_changed then *)
    (* 	  Hashtbl.replace iai.jc_interai_function_preconditions fi.jc_fun_info_tag function_pre; *)
    (* 	let inspected = List.mem fi.jc_fun_info_tag !inspected_functions in *)
    (* 	  if not inspected || pre_has_changed then *)
    (* 	    ai_function mgr (Some iai) [] (fi, loc, fs, sl); *)
    (*     end *)
    
(* External function to call to perform abstract interpretation [abs] 
 * on expr [e], starting from invariants [curinvs]. 
 * It sets the initial value of invariants before treating a loop.
 *)
and ai_expr iaio abs curinvs e =
  if debug then 
    printf "[ai_expr] %a on %a@." print_abstract_invariants curinvs
      Jc_output.expr e;
  let loops = abs.jc_absint_loops in
  let loop_initial_invariants = abs.jc_absint_loop_initial_invariants in
  let loop_invariants = abs.jc_absint_loop_invariants in
  let loop_iterations = abs.jc_absint_loop_iterations in
  match e#node with
    | JCEloop(annot,body) ->
	(* Reinitialize the loop iteration count and the loop invariant.
	 * This is useful to get precise results for inner loops.
	 * Comment those lines to gain in scaling, at the cost of precision.
	 *)
	Hashtbl.replace loops annot.jc_loop_tag e;
	Hashtbl.replace loop_iterations annot.jc_loop_tag 0;
	Hashtbl.remove loop_invariants annot.jc_loop_tag;
	(* Set the initial value of invariants when entering the loop from 
	 * the outside. 
	 *)
	Hashtbl.replace loop_initial_invariants annot.jc_loop_tag curinvs;
	intern_ai_expr iaio abs curinvs e 
    | _ -> intern_ai_expr iaio abs curinvs e
	
(* Internal function called when computing a fixpoint for a loop. It does not
 * modify the initial value of invariants for the loop considered, so that 
 * narrowing is possible.
 *)
and intern_ai_expr iaio abs curinvs e =
  let mgr = abs.jc_absint_manager in
  let ai = ai_expr iaio abs in

  (* Define common shortcuts. *)
  let normal = curinvs.jc_absinv_normal in
  let pre = normal.jc_absval_regular in
  let prop = normal.jc_absval_propagated in
  let postexcl = curinvs.jc_absinv_exceptional in
  let postret = curinvs.jc_absinv_return in

  (* Record invariant at assertion points. *)
  let targets = find_target_assertions abs.jc_absint_target_assertions e in
  List.iter
    (fun target ->
       target.jc_target_regular_invariant <- mkinvariant mgr pre;
       target.jc_target_propagated_invariant <- mkinvariant mgr prop
    ) targets;

  (* Apply appropriate transition function. *)
  let curinvs = match e#node with
    | JCElet(v,None,e1) ->
	ai curinvs e1
    | JCElet(v,Some e1,e2) when Expr.is_app e1 ->
	let curinvs = ai_call iaio abs curinvs (Some v) e1 in
	ai curinvs e2
    | JCElet(v,Some e1,e2) ->
	let tv = new term_var v in
	let curinvs = match e1#node with
	  | JCEapp _call ->
	      ai_call iaio abs curinvs (Some v) e1
	  | _ ->
	      (* TODO: precise case of allocation *)
	      let curinvs = ai curinvs e1 in
	      assign_expr mgr tv e1 curinvs 
	in
	let curinvs = ai curinvs e2 in
        (* To keep information on variable [v], declaration should be
	   turned into assignment before analysis. *)
        forget_invariants mgr curinvs (Vai.all_variables tv)
    | JCEassign_var(v,e1) ->
	let tv = new term_var v in
	let curinvs = ai curinvs e1 in
	assign_expr mgr tv e1 curinvs
    | JCEassign_heap(e1,fi,e2) ->
	let curinvs = ai curinvs e1 in
	let curinvs = ai curinvs e2 in
	begin match term_of_expr e1 with
	  | None -> assign_heap mgr e1#region None fi curinvs
	  | Some t1 ->
	      let dereft = 
		new term ~typ:fi.jc_field_info_type (JCTderef(t1,LabelHere,fi)) 
	      in
	      let curinvs = 
		assign_heap mgr e1#region (Some dereft) fi curinvs 
	      in
	      assign_expr mgr dereft e2 curinvs 
	end
    | JCEassert(_behav,_asrt,a) ->
	test_assertion mgr a curinvs
    | JCEblock sl ->
	List.fold_left ai curinvs sl
    | JCEif(e1,etrue,efalse) ->
	let curinvs = ai curinvs e1 in
	(* Treat "then" branch. *)
	let trueinvs = test_expr ~neg:false mgr e1 curinvs in
	let trueinvs = ai trueinvs etrue in
	(* Treat "else" branch. *)
	let falseinvs = test_expr ~neg:true mgr e1 curinvs in
	let falseinvs = ai falseinvs efalse in
	(* Join both branches. *)
	join_invariants mgr trueinvs falseinvs
    | JCEreturn_void ->
	return_abstract_value mgr postret e normal;
	{ curinvs with jc_absinv_normal = empty_abstract_value mgr normal }
    | JCEreturn(_ty,e1) ->
	let curinvs = ai curinvs e1 in
	let result = abs.jc_absint_function.jc_fun_info_result in
	let resultt = new term_var result in
	let curinvs = assign_expr mgr resultt e1 curinvs in
	let normal = curinvs.jc_absinv_normal in
	return_abstract_value mgr postret e normal;
	{ curinvs with jc_absinv_normal = empty_abstract_value mgr normal }
    | JCEthrow(ei,e1opt) ->
	let curinvs = match e1opt with
	  | None -> curinvs
	  | Some e1 -> ai curinvs e1
	in
	(* TODO: add thrown value as abstract variable. *)
	let thrown =
	  try join_abstract_value mgr normal (List.assoc ei postexcl)
	  with Not_found -> normal
	in
	let postexcl = (ei,thrown) :: (List.remove_assoc ei postexcl) in
	let curinvs = { curinvs with jc_absinv_exceptional = postexcl } in
	{ curinvs with jc_absinv_normal = empty_abstract_value mgr normal }
    | JCEtry(body,handlers,finally) ->
	let curinvs = ai curinvs body in
	let postexcl = curinvs.jc_absinv_exceptional in
	(* Filter out exceptions present in [handlers]. *)
	let curpostexcl =
	  List.filter 
	    (fun (ei,_invs) ->
	       not (List.exists
		      (fun (ej,_vopt,_e) ->
			 ei.jc_exception_info_tag = ej.jc_exception_info_tag
		      ) handlers)
	    ) postexcl
	in
	let curinvs = { curinvs with jc_absinv_exceptional  = curpostexcl } in
	(* Consider each handler in turn. *)
	let curinvs = List.fold_left 
	  (fun curinvs (ei,_vopt,ehandler) ->
	     try
	       let postexc = List.assoc ei postexcl in
	       let excinvs = {
		 jc_absinv_normal = postexc;
		 jc_absinv_exceptional = [];
		 jc_absinv_return = postret;
	       } in
	       let excinvs = ai excinvs ehandler in
	       join_invariants mgr curinvs excinvs
	     with Not_found -> curinvs
	  ) curinvs handlers
	in
	begin match finally#node with 
	  | JCEblock []
	  | JCEconst JCCvoid -> curinvs
	  | JCEblock [e1] when e1#node = JCEblock [] -> curinvs
	  | JCEblock [e1] when e1#node = JCEconst JCCvoid -> curinvs
	  | _ -> assert false (* TODO: apply finally stmt to all paths. *)
	end
    | JCEloop(annot,body) ->
	let loop_invariants = abs.jc_absint_loop_invariants in
	let loop_initial_invariants = abs.jc_absint_loop_initial_invariants in
	let loop_iterations = abs.jc_absint_loop_iterations in
	let num = 
	  try Hashtbl.find loop_iterations annot.jc_loop_tag 
	  with Not_found -> 0
	in
	Hashtbl.replace loop_iterations annot.jc_loop_tag (num + 1);
	
	if num < abs.jc_absint_widening_threshold then
	  (* Perform one step of propagation through the loop body. *)
	  let nextinvs = ai curinvs body in
	  let curinvs = join_invariants mgr curinvs nextinvs in
	  (* Perform fixpoint computation on the loop. *)
	  intern_ai_expr iaio abs curinvs e
	else
	  begin try
	    let loopinvs = Hashtbl.find loop_invariants annot.jc_loop_tag in
	    let wideninvs = widen_invariants mgr loopinvs curinvs in
	    if eq_invariants mgr loopinvs wideninvs then
	      begin 
		(* Fixpoint reached through widening. Perform narrowing now. *)
		let initinvs = 
		  Hashtbl.find loop_initial_invariants annot.jc_loop_tag 
		in
		let wideninvs = 
		  { wideninvs with jc_absinv_exceptional = [] } 
		in
		(* TODO: be more precise on return too. *)
		let wideninvs = ai wideninvs body in
		let wideninvs = join_invariants mgr wideninvs initinvs in
		Hashtbl.replace loop_invariants annot.jc_loop_tag wideninvs;
		let wideninvs = 
		  { wideninvs with jc_absinv_exceptional = 
		      initinvs.jc_absinv_exceptional } 
		in
		let wideninvs = ai wideninvs body in
		(* This is an infinite loop, whose only exit is through 
		   return or throwing exceptions. *)
		let curinvs = 
		  { curinvs with jc_absinv_normal =
		      empty_abstract_value mgr normal }
		in
		{ curinvs with 
		    jc_absinv_exceptional = wideninvs.jc_absinv_exceptional }
	      end
	    else
	      begin
		Hashtbl.replace 
		  loop_invariants annot.jc_loop_tag wideninvs;
		(* Perform one step of propagation through the loop body. *)
		let wideninvs = ai wideninvs body in
		(* Perform fixpoint computation on the loop. *)
		let wideninvs = intern_ai_expr iaio abs wideninvs e in
		(* Propagate changes to [curinvs]. *)
		let curinvs = 
		  { curinvs with jc_absinv_normal =
		      empty_abstract_value mgr normal } 
		in
		let normal = 
		  join_abstract_value mgr normal wideninvs.jc_absinv_normal 
		in
		{ curinvs with 
		    jc_absinv_normal = normal;
		    jc_absinv_exceptional = wideninvs.jc_absinv_exceptional }
	      end
	  with Not_found ->
	    Hashtbl.replace 
	      loop_invariants annot.jc_loop_tag curinvs;
	    (* Perform one step of propagation through the loop body. *)
	    let curinvs = ai curinvs body in
	    (* Perform fixpoint computation on the loop. *)
	    intern_ai_expr iaio abs curinvs e
	  end
    | JCEapp _call ->
	ai_call iaio abs curinvs None e
    | JCEconst _
    | JCEvar _ -> 
	curinvs
    | JCEunary(_,e1)
    | JCEderef(e1,_)
    | JCEoffset(_,e1,_)
    | JCEaddress(_,e1)
    | JCEcast(e1,_)
    | JCEbitwise_cast(e1,_)
    | JCErange_cast(e1,_)
    | JCEinstanceof(e1,_)
    | JCEreal_cast(e1,_)
    | JCEunpack(_,e1,_)
    | JCEpack(_,e1,_)
    | JCEalloc(e1,_)
    | JCEfree e1 ->
	ai curinvs e1
    | JCEbinary(e1,_,e2)
    | JCEshift(e1,e2) ->
	ai (ai curinvs e1) e2
    | JCEcontract _ -> assert false (* TODO *)
    | JCEmatch _ -> assert false (* TODO *)
  in

  (* Propagate assertions. *)
  List.fold_left
    (fun curinvs target ->
       test_assertion ~propagated:true mgr target.jc_target_assertion curinvs
    ) curinvs targets


and ai_call iaio abs curinvs vio e =
  let mgr = abs.jc_absint_manager in

  let call = match e#node with JCEapp call -> call | _ -> assert false in
  let f = match call.jc_call_fun with JCfun f -> f | _ -> assert false in
  let args = call.jc_call_args in

  (* Compute abstract value at function call *)
  let curinvs = List.fold_left (ai_expr iaio abs) curinvs args in
  let _f, pos, spec, body = 
    Hashtbl.find Jc_typing.functions_table f.jc_fun_info_tag 
  in
(*   begin match body with None -> () | Some body -> *)
(*     if Jc_options.interprocedural then *)
(*       match iaio with *)
(* 	| None -> () (\* intraprocedural analysis only *\) *)
(* 	| Some iai ->  *)
(* 	    let copy_pre = Abstract1.copy mgr pre in *)
(* 	    ai_inter_function_call mgr iai abs copy_pre fi loc fs sl args; *)
(*   end; *)

  (* Add precondition as checks *)
  let curinvs = 
    test_assertion ~propagated:true mgr spec.jc_fun_requires curinvs
  in

  (* Compute normal postcondition *)
  let normal_post =
    List.fold_left
      (fun acc (_pos,_name,b) ->
	 (* TODO : handle 'assumes' clauses precisely *)
	 if b.jc_behavior_throws = None && b.jc_behavior_assumes = None then
	   make_and [b.jc_behavior_ensures; acc]
	 else acc
      ) true_assertion spec.jc_fun_behavior
  in

(*   let normal_behavior = *)
(*     match iaio with *)
(*       | None -> normal_behavior *)
(*       | Some iai ->  *)
(* 	  let inferred_post = *)
(* 	    try *)
(* 	      Hashtbl.find iai.jc_interai_function_postconditions f.jc_fun_info_tag *)
(* 	    with Not_found -> Abstract1.top mgr (Abstract1.env pre) *)
(* 	  in *)
(* 	  make_and [normal_behavior; (mkinvariant mgr inferred_post)] *)
(*   in *)

  (* Add typing constraints on result *)
  let normal_post =
    match vio with
      | None -> normal_post
      | Some v ->
  	  let result = f.jc_fun_info_result in
  	  let cstrs = 
	    Jc_typing.type_range_of_term result.jc_var_info_type 
	      (new term_var result)
  	  in
  	  make_and [ normal_post; cstrs ]
  in

  (* Replace formal by actual parameters and result by actual variable *)
  let normal_post =
    List.fold_left2 
      (fun a e v -> 
	 let t = term_of_expr e in
	 match t with
	   | None -> forget_var_in_assertion v a
	   | Some t -> replace_vi_in_assertion v t a
      ) normal_post args f.jc_fun_info_parameters 
  in
  let normal_post =
    match vio with
      | None -> forget_var_in_assertion f.jc_fun_info_result normal_post
      | Some v -> 
	  switch_vis_in_assertion f.jc_fun_info_result v normal_post
  in

(*   let exceptional_behaviors = *)
(*     List.fold_left *)
(*       (fun acc (_, _, b) -> *)
(* 	 (\* TODO : handle 'assumes' clauses correctly *\) *)
(* 	 match b.jc_behavior_throws with *)
(* 	   | None -> acc  *)
(* 	   | Some ei -> *)
(* 	       if b.jc_behavior_assumes = None then *)
(* 		 (ei, b.jc_behavior_ensures) :: acc else acc) *)
(*       [] fs.jc_fun_behavior *)
(*   in *)
(*   let exceptional_behaviors = *)
(*     List.map *)
(*       (fun (ei, a) ->  *)
(* 	 ei, List.fold_left2  *)
(* 	   (fun a e vi ->  *)
(* 	      let t = term_of_expr e in *)
(* 	      match t with *)
(* 		| None -> assert false *)
(* 		| Some t -> replace_vi_in_assertion vi t a) *)
(* 	   a args f.jc_fun_info_parameters) *)
(*       exceptional_behaviors *)
(*   in *)
(*   let postexcl =  *)
(*     List.map  *)
(*       (fun (ei, a) ->  *)
(* 	 let copy_normal = copy_abstract_value mgr normal in *)
(* 	 let copy_pre = copy_normal.jc_absval_regular in *)
(* 	 let copy_pre = simple_test_assertion mgr normal_behavior  copy_pre in *)
(* 	 let copy_normal = { copy_normal with jc_absval_regular = copy_pre } in *)
(* 	 ei, copy_normal) *)
(*       exceptional_behaviors *)
(*   in *)
(*   let curinvs = { curinvs with jc_absinv_exceptional = postexcl } in *)
(*   if (is_purely_exceptional_fun fs) then *)
(*     { curinvs with jc_absinv_normal = empty_abstract_value mgr normal } *)
(*   else *)
(*     begin *)

  let fi_writes = f.jc_fun_info_effects.jc_writes.jc_effect_globals in
  let vars_writes = 
    VarMap.fold
      (fun vi _labs acc -> Vai.all_variables (new term_var vi) @ acc)
      fi_writes [] 
  in
  let assigns absval = 
    Abstract1.forget_array mgr absval (Array.of_list vars_writes) false 
  in
  let curinvs = apply_to_current_invariant assigns curinvs in
  test_assertion mgr normal_post curinvs 

 and record_ai_loop_invariants abs =
    let mgr = abs.jc_absint_manager in
    let loop_invariants = abs.jc_absint_loop_invariants in
    Hashtbl.iter 
    (fun _tag e -> 
       let annot = match e#node with
	 | JCEloop(annot,_body) -> annot
	 | _ -> assert false
       in
       begin try
	 let loopinvs = Hashtbl.find loop_invariants annot.jc_loop_tag in
	 let loopinv = 
	   meet mgr
	     loopinvs.jc_absinv_normal.jc_absval_regular 
	     loopinvs.jc_absinv_normal.jc_absval_propagated 
	 in
	 (* TODO: when it is finally implemented in APRON, this would be
	    a good place to minimize the abstract value by calling
	    [Abstract1.minimize mgr loopinv] 
	 *)
	 if Abstract1.is_top mgr loopinv then () else
	   let a = mkinvariant mgr loopinv in
	   let a = simplify a in
(* 	   nb_conj_atoms_inferred := !nb_conj_atoms_inferred + nb_conj_atoms a; *)
(* 	   incr nb_loop_inv; *)
	   if Jc_options.verbose then
	     printf 
	       "%a@[<v 2>Inferring loop invariant@\n%a@]@."
	       Loc.report_position e#pos Jc_output.assertion a;
	   (* Register loop invariant as such *)
	   let a = reg_annot ~pos:e#pos ~anchor:e#mark a in
	   if Jc_options.trust_ai then 
	     annot.jc_free_loop_invariant <- a 
	   else
	     annot.jc_loop_invariant <-  ([], a) :: annot.jc_loop_invariant;
       with Not_found -> () end
    ) abs.jc_absint_loops

and ai_function mgr iaio targets funpre (f,pos,spec,body) =
  try
    let env = Environment.make [||] [||] in
    
    (* Add global variables as abstract variables in [env]. *)
    let globvars =
      Hashtbl.fold (fun _tag (vi,_e) acc -> 
		      Vai.all_variables (new term_var vi) @ acc
		   ) Jc_typing.variables_table []
    in
    let env = Environment.add env (Array.of_list globvars) [||] in
    
    (* Add \result as abstract variable in [env] if any. *)
    let result = f.jc_fun_info_result in
    let return_type = result.jc_var_info_type in
    let env =
      if return_type <> JCTnative Tunit then
	let result = Vai.all_variables (new term_var result) in
	Environment.add env (Array.of_list result) [||]
      else env 
    in

    (* Add parameters as abstract variables in [env]. *)
    let params =
      List.fold_left
	(fun acc v -> Vai.all_variables (new term_var v) @ acc)
	[] f.jc_fun_info_parameters
    in
    let env = Environment.add env (Array.of_list params) [||] in
    
    let abs = { 
      jc_absint_manager                 = mgr;
      jc_absint_function_environment    = env;
      jc_absint_function                = f;
      jc_absint_widening_threshold      = 1;
      jc_absint_loops                   = Hashtbl.create 0;
      jc_absint_loop_invariants         = Hashtbl.create 0;
      jc_absint_loop_initial_invariants = Hashtbl.create 0;
      jc_absint_loop_iterations         = Hashtbl.create 0;
      jc_absint_loop_entry_invs         = Hashtbl.create 0;
      jc_absint_target_assertions       = targets;
    } in
    
    (* Take the function precondition as initial constraints *)
    let initpre = top_abstract_value mgr env in
    let initpre = 
      { initpre with jc_absval_regular =
	  simple_test_assertion mgr funpre initpre.jc_absval_regular } 
    in

    (* Add the currently inferred pre for [f] in pre *)
(*     let initpre = match iaio with *)
(*       | None -> initpre *)
(*       | Some iai -> *)
(* 	  let inferred_pre = *)
(* 	    try Hashtbl.find iai.jc_interai_function_preconditions f.jc_fun_info_tag  *)
(* 	    with Not_found -> Abstract1.top mgr env (\* for main function *\) in *)
(* 	  { initpre with jc_absval_regular = *)
(* 	      meet mgr initpre.jc_absval_regular inferred_pre } *)
(*     in *)

    pointer_terms_table := Hashtbl.create 0;

    (* Annotation inference on the function body. *)
    let initinvs = {
      jc_absinv_normal = initpre;
      jc_absinv_exceptional = [];
      jc_absinv_return = Hashtbl.create 3;
    } in
    let finalinvs = ai_expr iaio abs initinvs body in
    begin match iaio with
      | None ->  record_ai_loop_invariants abs 
      | Some iai -> 
	  Hashtbl.replace iai.jc_interai_function_abs f.jc_fun_info_tag abs
    end;
    List.iter 
      (fun target -> 
	 if Jc_options.debug then
	   printf 
	     "%a@[<v 2>Inferring assert invariant@\n%a@]@."
	     Loc.report_position target.jc_target_location
	     Jc_output.assertion target.jc_target_regular_invariant 
      ) targets;
    
(*     let initpre = *)
(*       match iaio with *)
(* 	| None -> initpre *)
(* 	| Some iai -> (\* Interprocedural analysis *\)  *)
(* 	    inspected_functions := f.jc_fun_info_tag :: !inspected_functions; *)
(* 	    incr nb_nodes; *)
(* 	    (\* Take the currently inferred pre for [fi] if any *\) *)
(* 	    try *)
(* 	      let inferred_pre =  *)
(* 		Hashtbl.find iai.jc_interai_function_preconditions f.jc_fun_info_tag *)
(* 	      in *)
(* 	      { initpre with jc_absval_regular = *)
(* 		  Abstract1.copy mgr inferred_pre } *)
(* 	    with Not_found -> initpre *)
(*     in *)
(*     pointer_terms_table := Hashtbl.create 0; *)

    (* Update the return postcondition for procedure with no last return. *)
    if return_type = JCTnative Tunit then
      return_abstract_value mgr finalinvs.jc_absinv_return
	body finalinvs.jc_absinv_normal;

    (* record the inferred postcondition *)
(*     match iaio with  *)
(*       | None -> () *)
(*       | Some iai -> *)
(* 	  let old_post =  *)
(* 	    try *)
(* 	      Hashtbl.find iai.jc_interai_function_postconditions f.jc_fun_info_tag *)
(* 	    with Not_found -> Abstract1.top mgr env *)
(* 	  in *)
(* 	  let returnabs = keep_extern mgr fi !(invs.jc_absinv_return).jc_absval_regular in *)
(* 	  if not (is_eq mgr old_post returnabs) then *)
(* 	    Hashtbl.replace iai.jc_interai_function_postconditions f.jc_fun_info_tag returnabs; *)
(* 	  let old_excep =  *)
(* 	    try *)
(* 	      Hashtbl.find iai.jc_interai_function_exceptional f.jc_fun_info_tag *)
(* 	    with Not_found -> [] *)
(* 	  in *)
(* 	  let excabsl = *)
(* 	    List.fold_left *)
(* 	      (fun acc (exc, va) -> (exc, va.jc_absval_regular) :: acc) *)
(* 	      [] invs.jc_absinv_exceptional  *)
(* 	  in *)
(* 	  let excabsl = List.map (fun (exc, va) -> exc, keep_extern mgr fi va) excabsl in *)
(* 	  if (List.length old_excep = List.length excabsl) then *)
(* 	    let annot_inferred =  *)
(* 	      List.fold_left2 *)
(* 		(fun acc (ei1, va1) (ei2, va2) -> *)
(* 		   if ei1.jc_exception_info_tag <> ei2.jc_exception_info_tag || *)
(* 		     not (is_eq mgr va1 va2) then true else acc) false old_excep excabsl *)
(* 	    in *)
(* 	    if annot_inferred then *)
(* 	      Hashtbl.replace iai.jc_interai_function_exceptional f.jc_fun_info_tag excabsl; *)
	    
  with Manager.Error exc ->
    Manager.print_exclog std_formatter exc;
    printf "@.";
    exit 1

      
(*****************************************************************************)
(* Modular generation of annotations for a function.                         *)
(*****************************************************************************)

let prepare_target target =
  target.jc_target_regular_invariant <- 
    simplify target.jc_target_regular_invariant;
  (* Build the most precise invariant known at the current assertion point: 
   * it is the conjunction of the regular invariant (from forward abstract
   * interpretation) and the propagated invariant (from propagated assertions).
   *)
  let inv = 
    make_and [ target.jc_target_regular_invariant;
	       target.jc_target_propagated_invariant ]
  in
  (* Check whether the target assertion is a consequence of the most 
   * precise invariant. 
   *)
  let impl = new assertion (JCAimplies(inv,target.jc_target_assertion)) in
  if tautology impl then 
    (if debug then
       printf "%a[code_function] proof of %a discharged@." 
	 Loc.report_position target.jc_target_location
	 Jc_output.assertion target.jc_target_assertion;
     None) 
  else 
    (if debug then
       printf "%a[code_function] precondition needed for %a@." 
	 Loc.report_position target.jc_target_location
	 Jc_output.assertion target.jc_target_assertion;
     (* Adding target to the list. *)
     Some target)

let code_function (f,pos,spec,body) =
  match body with None -> () | Some body ->
    let wp_filter canda =
      (* Only propagate candidate assertions for targets if Atp can make 
       * sense of them.
       *)
      (* TODO : make sure ident on common logic formulas. *)
      (*         raw_assertion_equal canda (asrt_of_atp(atp_of_asrt canda)) *)
      true
    in

    (* Add parameters specs to the function precondition *)
    let cstrs =
      List.fold_left
 	(fun acc v -> 
	   let cstr = 
	     Jc_typing.type_range_of_term v.jc_var_info_type (new term_var v)
	   in 
	   cstr :: acc
	) [] f.jc_fun_info_parameters
    in
    let funpre = 
      make_and (spec.jc_fun_requires :: spec.jc_fun_free_requires :: cstrs)
    in

    begin match !Jc_options.annotation_sem with
      | AnnotNone -> ()
      | AnnotInvariants | AnnotElimPre | AnnotWeakPre | AnnotStrongPre ->
	  (* Collect checks that directly follow function beginning or 
	     loop beginning *)
(* 	  let targets = collect_immediate_targets [] sl in *)

	  (* Collect checks *)
	  let targets = collect_targets wp_filter [] body in

(* 	  backprop_function targets (fi,fs,sl); *)

	  (* Generate invariants by forward abstract interpretation *)
	  begin match !Jc_options.ai_domain with
	    | AbsNone ->
		()
	    | AbsBox -> 
		let mgr = Box.manager_alloc () in
		ai_function mgr None targets funpre (f,pos,spec,body)
	    | AbsOct -> 
		let mgr = Oct.manager_alloc () in
		ai_function mgr None targets funpre (f,pos,spec,body)
	    | AbsPol -> 
		let mgr = Polka.manager_alloc_strict () in
		ai_function mgr None targets funpre (f,pos,spec,body)
	  end;

	  (* Generate preconditions by quantifier elimination and
	     weakest preconditions *)
	  begin match !Jc_options.annotation_sem with 
	    | AnnotNone -> assert false
	    | AnnotInvariants	-> ()
	    | AnnotElimPre | AnnotWeakPre | AnnotStrongPre ->
 		let targets = 
		  List.fold_right 
		    (fun target acc ->
		       match prepare_target target with
			 | None -> acc
			 | Some a -> a :: acc
		    ) targets []
		in
		wp_function targets funpre (f,pos,spec,body)
	  end
    end
      

(*****************************************************************************)
(* Interprocedural analysis.                                                 *)
(*****************************************************************************)

let rec record_ai_inter_annotations mgr iai fi pos fs sl =
  let env = Environment.make [||] [||] in
  inspected_functions := fi.jc_fun_info_tag :: !inspected_functions;
  (* record inferred precondition for [fi] *)
  let pre = 
    try 
      Hashtbl.find iai.jc_interai_function_preconditions fi.jc_fun_info_tag 
    with Not_found -> Abstract1.top mgr env
  in
  let a = mkinvariant mgr pre in
  let a = reg_annot ~pos ~anchor:fi.jc_fun_info_name a in
  nb_conj_atoms_inferred := !nb_conj_atoms_inferred + nb_conj_atoms a;
  incr nb_fun_pre;
  if Jc_options.verbose then
    printf 
      "@[<v 2>Inferring precondition for function %s@\n%a@]@."
      fi.jc_fun_info_name Jc_output.assertion a;
  fs.jc_fun_free_requires <- make_and [fs.jc_fun_free_requires; a];
  (* record loop invariants for [fi] *)
  let abs = 
    try 
      Hashtbl.find iai.jc_interai_function_abs fi.jc_fun_info_tag
    with Not_found -> assert false 
  in
  record_ai_loop_invariants abs;
  (* record inferred postconditions for [fi] *)
  let post = 
    try 
      Hashtbl.find iai.jc_interai_function_postconditions fi.jc_fun_info_tag 
    with Not_found -> Abstract1.top mgr env
  in
  let returna = mkinvariant mgr post in
  let vi_result = fi.jc_fun_info_result in
  let post = make_and 
    [returna; Jc_typing.type_range_of_term vi_result.jc_var_info_type 
       (new term_var vi_result)] 
  in
  let normal_behavior = { default_behavior with jc_behavior_ensures = post } in
  let exceptional = 
    try 
      Hashtbl.find iai.jc_interai_function_exceptional fi.jc_fun_info_tag 
    with Not_found -> []
  in
  let excl, excabsl =
    List.fold_left
      (fun (acc1, acc2) (exc, va) -> (exc :: acc1, va :: acc2))
      ([], []) exceptional in
  let excabsl = List.map (fun va -> keep_extern mgr fi va) excabsl in
  let excabsl = List.map
    (fun va -> if Abstract1.is_bottom mgr va then
       Abstract1.top mgr env else va) excabsl in
  let excal = List.map (mkinvariant mgr) excabsl in
  
  let post = reg_annot ~pos ~anchor:fi.jc_fun_info_name post in
  nb_conj_atoms_inferred := !nb_conj_atoms_inferred + nb_conj_atoms post;
  incr nb_fun_post;
  let excal = List.map (reg_annot ~pos ~anchor:fi.jc_fun_info_name) excal in
  
  let exc_behaviors = 
    List.map2 
      (fun exc va ->
	 (Loc.dummy_position, "inferred",
	  { default_behavior with 
	      jc_behavior_throws = Some exc; 
	      jc_behavior_ensures = va }))
      excl excal 
  in
  if Jc_options.verbose then
    begin
      printf
	"@[<v 2>Inferring postcondition for function %s@\n%a@]@."
	fi.jc_fun_info_name
	Jc_output.assertion post;
      List.iter2
	(fun exc exca -> 
	   nb_conj_atoms_inferred := !nb_conj_atoms_inferred + nb_conj_atoms exca;
	   incr nb_fun_excep_post;
	   printf
	     "@[<v 2>Inferring exceptional postcondition (for exception %s) for function %s@\n%a@]@."
	     exc.jc_exception_info_name
	     fi.jc_fun_info_name
	     Jc_output.assertion exca) excl excal;
    end;
  begin
    if is_purely_exceptional_fun fs then () else
      fs.jc_fun_behavior <- 
	(Loc.dummy_position,"inferred", normal_behavior) :: fs.jc_fun_behavior
  end;
  fs.jc_fun_behavior <- exc_behaviors @ fs.jc_fun_behavior;
  (* iterate on the call graph *)
  List.iter 
    (fun fi ->
       let fi, _, fs, slo = 
	 try
	   Hashtbl.find Jc_typing.functions_table fi.jc_fun_info_tag
	 with Not_found -> assert false (* should never happen *)
       in
       match slo with
	 | None -> ()
	 | Some b ->
	     if not (List.mem fi.jc_fun_info_tag !inspected_functions) then
	       record_ai_inter_annotations mgr iai fi pos fs b)
    fi.jc_fun_info_calls
    
    
let ai_interprocedural mgr (fi, loc, fs, sl) =
  let iai = {
    jc_interai_manager = mgr;
    jc_interai_function_preconditions = Hashtbl.create 0;
    jc_interai_function_postconditions = Hashtbl.create 0;
    jc_interai_function_exceptional = Hashtbl.create 0;
    jc_interai_function_nb_iterations = Hashtbl.create 0;
    jc_interai_function_init_pre = Hashtbl.create 0;
    jc_interai_function_abs = Hashtbl.create 0;
  } in
  let time = Unix.gettimeofday () in
  ai_function mgr (Some iai) [] true_assertion (fi, loc, fs, sl);
  inspected_functions := [];
  record_ai_inter_annotations mgr iai fi loc fs sl;
  let time = Unix.gettimeofday () -. time in
  if Jc_options.verbose then 
    printf "Interprocedural analysis stats: \
@.    %d function preconditions inferred \
@.    %d function postconditions inferred \
@.    %d function exceptional postconditions inferred \
@.    %d loop invariants inferred \
@.    %d conjonction atoms inferred \
@.    %d nodes \
@.    %f seconds@." 
      !nb_fun_pre !nb_fun_post !nb_fun_excep_post !nb_loop_inv
      !nb_conj_atoms_inferred !nb_nodes time
      
      
let main_function = function
  | fi, loc, fs, None -> ()
  | fi, loc, fs, Some sl ->
      begin match !Jc_options.ai_domain with
	| AbsBox ->
	    let mgr = Box.manager_alloc () in
	    ai_interprocedural mgr (fi, loc, fs, sl)
	| AbsOct -> 
	    let mgr = Oct.manager_alloc () in
	    ai_interprocedural mgr (fi, loc, fs, sl)
	| AbsPol -> 
	    let mgr = Polka.manager_alloc_strict () in
	    ai_interprocedural mgr (fi, loc, fs, sl)
	| AbsNone -> assert false
      end

let rec is_recursive_rec fi fil =
  List.exists 
    (fun fi' -> 
       inspected_functions := fi'.jc_fun_info_tag :: !inspected_functions;
       fi.jc_fun_info_tag = fi'.jc_fun_info_tag || 
	   (not (List.mem fi'.jc_fun_info_tag !inspected_functions) &&
	      is_recursive_rec fi fi'.jc_fun_info_calls))
    fil

let is_recursive fi =
  inspected_functions := [];
  let r = is_recursive_rec fi fi.jc_fun_info_calls in
  inspected_functions := [];
  r

    
(*
  Local Variables: 
  compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
  End: 
*)
