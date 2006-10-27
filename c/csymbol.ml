
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


(* predicate variable interface. Same as VARIABLE, plus [translate_predicate]
   whose aim is to translate generic predicates such as [IPnull_pointer] in
   more specific ones. *)

module type PVARIABLE = sig
  include VARIABLE
  (* local term and predicate, where the variable type is [t] *)
  type iterm = t int_term
  type ipredicate = t int_predicate
  val translate_predicate : ipredicate -> ipredicate
end

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

let rec collect_predicate_vars p = match p with
  | IPfalse | IPtrue | IPany -> 
      []
  | IPnull_pointer t1 | IPnot_null_pointer t1 ->
      collect_term_vars t1
  | IPrel (t1,_,t2) | IPseparated (t1,t2) | IPnull_char_pointed (t1,t2)
  | IPnot_null_char_pointed (t1,t2) ->
      collect_term_vars t1 @ (collect_term_vars t2)
  | IPand (p1,p2) | IPor (p1,p2) | IPimplies (p1,p2) | IPiff (p1,p2) ->
      collect_predicate_vars p1 @ (collect_predicate_vars p2)
  | IPnot p1 -> 
      collect_predicate_vars p1

module VarElimination (V : VARIABLE) =
struct

  module Term = 
  struct
    type t = V.t int_term
    let compare = Pervasives.compare
  end

  module TSet = Set.Make (Term)

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
	TSet.union min_p1 min_p2,TSet.union max_p1 max_p2
    | IPrel (t1,Le,t2) ->
	begin try
	  let lhs_vfact,lhs_term = destruct v t1 in
	  let rhs_vfact,rhs_term = destruct v t2 in
	  match lhs_vfact - rhs_vfact with
	    | 1 -> 
		TSet.empty,
		TSet.add (ITbinop(rhs_term,Bsub,lhs_term)) TSet.empty
	    | -1 -> 
		TSet.add (ITbinop(lhs_term,Bsub,rhs_term)) TSet.empty,
		TSet.empty
	    | _ ->
		TSet.empty,TSet.empty
	with Not_Representable -> TSet.empty,TSet.empty end
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
	TSet.empty,TSet.empty
    | _ -> failwith "[min_max] expecting conjunct"

  let transitivity v p = match p with
    | IPimplies (lhs_p,rhs_p) ->
	let min_lhs_pset,max_lhs_pset = min_max v lhs_p in
	let min_rhs_pset,max_rhs_pset = min_max v rhs_p in
	let trans1 =
	  TSet.fold (fun min_t acc_p ->
		       TSet.fold (fun max_t acc_p -> 
				    IPand (acc_p,IPrel (min_t,Le,max_t)))
			 max_lhs_pset acc_p 
		    ) min_rhs_pset IPtrue
	in
	let trans2 =
	  TSet.fold (fun min_t acc_p ->
		       TSet.fold (fun max_t acc_p -> 
				    IPand (acc_p,IPrel (min_t,Le,max_t)))
			 max_rhs_pset acc_p 
		    ) min_lhs_pset IPtrue
	in
	IPand (trans1,trans2)
    | _ -> failwith "[transitivity] expecting implication"

end
