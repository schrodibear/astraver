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

(* $Id: csymbol.ml,v 1.5 2006-11-03 14:41:38 moy Exp $ *)

(* TO DO:

   - implement [rewrite_pred_wrt_var]

*)

open Clogic
open Cabsint

(* local types describing terms and predicates, sufficient for expressing
   the predicates that result from the integer analysis.
   They depend on a parameter ['v] that describes the type of a variable.
*)

type 'v int_term =
  | ITconstant of constant
  | ITvar of 'v
  | ITunop of term_unop * 'v int_term
  | ITbinop of 'v int_term * term_binop * 'v int_term
    (* used to translate an expression that has no counterpart in the small
       term language presented here. When computing an abstraction for
       a surrounding term, we will translate [ITany] to top. *)
  | ITany
      
type 'v int_predicate =
  | IPfalse
  | IPtrue
  | IPrel of 'v int_term * relation * 'v int_term
  | IPand of 'v int_predicate * 'v int_predicate
  | IPor of 'v int_predicate * 'v int_predicate
  | IPimplies of 'v int_predicate * 'v int_predicate
  | IPiff of 'v int_predicate * 'v int_predicate
  | IPnot of 'v int_predicate
  | IPseparated of 'v int_term * 'v int_term
    (* specific predicates to express (non-)nullity of pointer and
       (non-)nullity of char pointer read. These should be translated in some
       more specific predicates depending on the domain. *)
  | IPnull_pointer of 'v int_term
  | IPnot_null_pointer of 'v int_term
  | IPnull_char_pointed of 'v int_term * 'v int_term
  | IPnot_null_char_pointed of 'v int_term * 'v int_term
    (* used to translate an predicate that has no counterpart in the small
       predicate language presented here. When computing an abstraction for
       a surrounding predicate, we will translate [IPany] to top. *)
  | IPany

module type TERM = sig
  type var
  include ELEMENT_OF_CONTAINER with type t = var int_term
  val collect_term_vars : t -> var list
end

module type PREDICATE = sig
  type var
  include ELEMENT_OF_CONTAINER with type t = var int_predicate
  val explicit_pred : t -> t
  val rewrite_pred_wrt_var : t -> var -> int -> t
  val collect_predicate_vars : t -> var list
  val make_conjunct : t list -> t
  val get_conjuncts : t -> t list
  val make_implication : t -> t -> t
  val get_implicants : t -> t * t
end

module TermOfVariable (V : ELEMENT_OF_CONTAINER) 
  : TERM with type var = V.t =
struct
  
  type var = V.t
  type t = var int_term

  let equal = ( = )
  let compare = Pervasives.compare
  let hash = Hashtbl.hash

  let rec pretty fmt = function
    | ITconstant (IntConstant c | RealConstant c) -> 
	Format.fprintf fmt "%s" c
    | ITvar v            -> Format.fprintf fmt "%a" V.pretty v
    | ITunop (op,t)      -> Format.fprintf fmt "%s %a" 
	(Cprint.term_unop op) pretty t
    | ITbinop (t1,op,t2) ->  Format.fprintf fmt "%a %s %a" 
	pretty t1 (Cprint.term_binop op) pretty t2
    | ITany              -> Format.fprintf fmt "_"

  (* takes as input a term
     returns a list of variables occurring in this term, in the order 
     they appear, with possible repetitions
  *)
  let rec collect_term_vars t = match t with
    | ITconstant _ -> []
    | ITvar v -> [v]
    | ITunop (_,t1) -> collect_term_vars t1
    | ITbinop (t1,_,t2) -> collect_term_vars t1 @ (collect_term_vars t2)
    | ITany -> []
end

module PredicateOfVariable (V : ELEMENT_OF_CONTAINER) 
  (T : TERM with type var = V.t)
  : PREDICATE with type var = V.t =
struct
  
  type var = V.t
  type t = var int_predicate

  let equal = ( = )
  let compare = Pervasives.compare
  let hash = Hashtbl.hash

  let rec pretty fmt = function
    | IPfalse -> Format.fprintf fmt "false"
    | IPtrue -> Format.fprintf fmt "true"
    | IPrel (t1,rel,t2) -> Format.fprintf fmt "%a %s %a"
	T.pretty t1 (Cprint.relation rel) T.pretty t2
    | IPand (p1,p2) -> Format.fprintf fmt "%a && %a"
	pretty p1 pretty p2
    | IPor (p1,p2) -> Format.fprintf fmt "%a || %a"
	pretty p1 pretty p2
    | IPimplies (p1,p2) -> Format.fprintf fmt "%a => %a"
	pretty p1 pretty p2
    | IPiff (p1,p2) -> Format.fprintf fmt "%a <=> %a"
	pretty p1 pretty p2
    | IPnot p -> Format.fprintf fmt "! %a" pretty p
    | IPseparated (t1,t2) -> Format.fprintf fmt "separated(%a,%a)"
	T.pretty t1 T.pretty t2
    | IPnull_pointer t1 -> Format.fprintf fmt "%a == 0"
	T.pretty t1
    | IPnot_null_pointer t1 -> Format.fprintf fmt "%a != 0"
	T.pretty t1
    | IPnull_char_pointed (t1,t2) -> Format.fprintf fmt "%a[%a] == 0"
	T.pretty t1 T.pretty t2
    | IPnot_null_char_pointed (t1,t2) -> Format.fprintf fmt "%a[%a] != 0"
	T.pretty t1 T.pretty t2
    | IPany -> Format.fprintf fmt "_"

  (* explicit the more complex predicates for an easier treatment from
     the integer analysis: 
     - implication and equivalence are translated in more basic
     conjunction and disjunction (using the next item on negation)
     - negation is pushed inside sub-predicates
  *)
  let rec explicit_pred p = match p with
    | IPfalse | IPtrue | IPrel _ | IPany | IPseparated _ | IPnull_pointer _ 
    | IPnot_null_pointer _ | IPnull_char_pointed _ | IPnot_null_char_pointed _
	-> p
    | IPand (p1,p2) -> 
	let ep1 = explicit_pred p1 in
	let ep2 = explicit_pred p2 in
	IPand (ep1,ep2)
    | IPor (p1,p2) -> 
	let ep1 = explicit_pred p1 in
	let ep2 = explicit_pred p2 in
	IPor (ep1,ep2)
    | IPimplies (p1,p2) ->
	explicit_pred (IPor(IPnot p1,p2))
    | IPiff (p1,p2) ->
	explicit_pred (IPand(IPimplies(p1,p2),IPimplies(p2,p1)))
    | IPnot p1 ->
	begin match explicit_pred p1 with
          | IPfalse -> IPtrue
          | IPtrue -> IPfalse
          | IPand (p3,p4) ->
	      let ep3 = explicit_pred (IPnot p3) in
	      let ep4 = explicit_pred (IPnot p4) in
	      IPor (ep3,ep4)
          | IPor (p3,p4) ->
	      let ep3 = explicit_pred (IPnot p3) in
	      let ep4 = explicit_pred (IPnot p4) in
	      IPand (ep3,ep4)
	  | IPnot p3 ->
	      p3
	  | IPrel (t3,op,t4) ->
	      let new_op = match op with
		| Lt -> Ge
		| Gt -> Le
		| Le -> Gt
		| Ge -> Lt
		| Eq -> Neq
		| Neq -> Eq
	      in
	      IPrel (t3,new_op,t4)
	  | IPimplies _ | IPiff _ -> 
	      (* those cases should not be returned by a call 
		 to [explicit_pred] *)
	      assert false
	  | IPany -> IPany
	  | IPseparated _ as psep -> psep
	  | IPnull_pointer t1 -> IPnot_null_pointer t1
	  | IPnot_null_pointer t1 -> IPnull_pointer t1
	  | IPnull_char_pointed (t1,t2) -> IPnot_null_char_pointed (t1,t2)
	  | IPnot_null_char_pointed (t1,t2) -> IPnull_char_pointed (t1,t2)
	end

  let rewrite_pred_wrt_var p v noccur = p	

  let rec collect_predicate_vars p = match p with
    | IPfalse | IPtrue | IPany -> 
	[]
    | IPnull_pointer t1 | IPnot_null_pointer t1 ->
	T.collect_term_vars t1
    | IPrel (t1,_,t2) | IPseparated (t1,t2) | IPnull_char_pointed (t1,t2)
    | IPnot_null_char_pointed (t1,t2) ->
	T.collect_term_vars t1 @ (T.collect_term_vars t2)
    | IPand (p1,p2) | IPor (p1,p2) | IPimplies (p1,p2) | IPiff (p1,p2) ->
	collect_predicate_vars p1 @ (collect_predicate_vars p2)
    | IPnot p1 -> 
	collect_predicate_vars p1

  let make_conjunct plist = 
    let rec make_sub p_acc plist = match p_acc,plist with
      | p_acc,[] -> p_acc
      | IPtrue,p :: plist | p,IPtrue :: plist -> make_sub p plist
      | p_acc,p :: plist -> make_sub (IPand (p_acc,p)) plist
    in
    make_sub IPtrue plist 

  let rec get_conjuncts p = match p with
    | IPand (p1,p2) -> get_conjuncts p1 @ (get_conjuncts p2)
    | _ -> [p]

  let make_implication lhs_p rhs_p = IPimplies (lhs_p,rhs_p)

  let get_implicants p = match p with
    | IPimplies (p1,p2) -> p1,p2
    | _ -> failwith "[get_implicants] expecting an implication"

end

(* predicate variable interface. Same as VARIABLE, plus [translate_predicate]
   whose aim is to translate generic predicates such as [IPnull_pointer] in
   more specific ones. *)

module type PVARIABLE = sig
  include VARIABLE

  (* containers based on [t] *)
  module S : Set.S with type elt = t
  module M : Map.S with type key = t
  module H : Hashtbl.S with type key = t

  (* modules for terms and predicates *)
  module T : TERM with type var = t
  module P : PREDICATE with type var = t

  (* containers based on terms *)
  module TS : Set.S with type elt = T.t
  module TM : Map.S with type key = T.t
  module TH : Hashtbl.S with type key = T.t

  (* containers based on predicates *)
  module PS : Set.S with type elt = P.t
  module PM : Map.S with type key = P.t
  module PH : Hashtbl.S with type key = P.t

  val translate_predicate : P.t -> P.t
end


module VarElimination (V : PVARIABLE) =
struct
  exception Not_Representable

  let rec destruct v p = match p with
    | ITconstant _ -> 0,p
    | ITvar v2 -> 
	if V.equal v v2 then 1,ITconstant (IntConstant "0")
	else 0,p
    | ITunop (Uminus,p1) ->
	let fact,term = destruct v p1 in -fact,ITunop (Uminus,term)
    | ITunop _ ->
	raise Not_Representable
    | ITbinop (p1,Badd,p2) ->
	let fact1,term1 = destruct v p1 in
	let fact2,term2 = destruct v p2 in
	fact1+fact2,ITbinop(term1,Badd,term2)
    | ITbinop (p1,Bsub,p2) ->
	destruct v (ITbinop (p1,Badd,ITunop(Uminus,p2)))
    | ITbinop _ -> 
	raise Not_Representable
    | ITany ->
	raise Not_Representable

  let rec min_max v p = match p with
    | IPand (p1,p2) ->
	let min_p1,max_p1 = min_max v p1 in
	let min_p2,max_p2 = min_max v p2 in
	V.TS.union min_p1 min_p2,V.TS.union max_p1 max_p2
    | IPrel (t1,Le,t2) ->
	begin try
	  let lhs_vfact,lhs_term = destruct v t1 in
	  let rhs_vfact,rhs_term = destruct v t2 in
	  match lhs_vfact - rhs_vfact with
	    | 1 -> 
		V.TS.empty,
		V.TS.add (ITbinop(rhs_term,Bsub,lhs_term)) V.TS.empty
	    | -1 -> 
		V.TS.add (ITbinop(lhs_term,Bsub,rhs_term)) V.TS.empty,
		V.TS.empty
	    | _ ->
		V.TS.empty,V.TS.empty
	with Not_Representable -> V.TS.empty,V.TS.empty end
    | IPrel (t1,Ge,t2) ->
	min_max v (IPrel (t2,Le,t1))
    | IPrel (t1,Lt,t2) ->
	(* since we are working with integer variables, t1 < t2 is equivalent
	   to t1 <= t2 - 1 *)
	min_max v 
	  (IPrel (t1,Le,ITbinop (t2,Bsub,ITconstant (IntConstant "1"))))
    | IPrel (t1,Gt,t2) ->
	(* since we are working with integer variables, t1 > t2 is equivalent
	   to t2 <= t1 - 1 *)
	min_max v 
	  (IPrel (t2,Le,ITbinop (t1,Bsub,ITconstant (IntConstant "1"))))
    | IPrel (t1,Eq,t2) ->
	min_max v (IPand (IPrel (t1,Le,t2), IPrel (t1,Ge,t2)))
    | IPrel (_,Neq,_) ->
	V.TS.empty,V.TS.empty
    | _ -> failwith "[min_max] expecting conjunct"

  let relate_individual_bounds min_t max_t =
    IPrel (min_t,Le,max_t)    

  let relate_bounds min_set max_set =
    V.TS.fold (fun min_t acc_l ->
		 V.TS.fold (fun max_t acc_l -> 
			      relate_individual_bounds min_t max_t :: acc_l
			   ) max_set acc_l
	      ) min_set []

  let transitivity v p = match p with
    | IPimplies (lhs_p,rhs_p) ->
	let min_lhs_tset,max_lhs_tset = min_max v lhs_p in
	let min_rhs_tset,max_rhs_tset = min_max v rhs_p in
	let trans1 =
	  V.TS.fold (fun min_t acc_p ->
		       V.TS.fold (fun max_t acc_p -> 
				    IPand (acc_p,IPrel (min_t,Le,max_t)))
			 max_lhs_tset acc_p 
		    ) min_rhs_tset IPtrue
	in
	let trans2 =
	  V.TS.fold (fun min_t acc_p ->
		       V.TS.fold (fun max_t acc_p -> 
				    IPand (acc_p,IPrel (min_t,Le,max_t)))
			 max_rhs_tset acc_p 
		    ) min_lhs_tset IPtrue
	in
	IPand (trans1,trans2)
    | _ -> failwith "[transitivity] expecting implication"

  let fourier_motzkin v p = match p with
    | IPimplies (lhs_p,rhs_p) ->
	let min_lhs_tset,max_lhs_tset = min_max v lhs_p in
	let min_rhs_tset,max_rhs_tset = min_max v rhs_p in
	let min_plist = relate_bounds min_rhs_tset min_lhs_tset in
	let max_plist = relate_bounds max_lhs_tset max_rhs_tset in
	V.P.make_conjunct (min_plist @ max_plist)
    | _ -> failwith "[fourier_motzkin] expecting implication"

end
