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

(*i $Id: hypotheses_filtering.ml,v 1.21 2007-08-24 13:26:58 couchot Exp $ i*)

(**
   This module provides a quick way to filter hypotheses of 
   a goal. It is activated by the option 
   --prune-hyp vb pb 
   where vb an pb are integers that are positive or null. 
   vb is the bound of the max depth of the variable graph search 
   pb is the bound of the max depth of the predicate graph search 
   The number of selected hypotheses increases w.r.t. vb and pb. 
   
   The internal flow is:
   1) Hypotheses are expanded thanks to the intros tactic. 
   A short goal is then produced.
   2) Variables of hypothesis are stored into a graph where 
   - a variable is represented by a vertex
   - a predicate linking some variables is represented by 
   the complete graph with all the vertices 
   corresponding to the variables 
   3) A breadth-first search algorithm, bounded by the constant pb
   computes the set of relevant predicates P
   4) A breadth-first search algorithm, bounded by the constant k
   computes the set of relevant variables V
   5) An hypothesis is selected  by comparing its set of variables 
   with R and its set of predicates with P 
**)

open Ident
open Options
open Misc
open Error
open Logic
open Logic_decl
open Env
open Cc
open Format
open Pp
open Hashtbl
open Set
open Util
open Graph.Graphviz 


let pb = ref Options.pruning_hyp_p   
let vb = ref Options.pruning_hyp_v   
let v_count = ref 0
let hyp_count = ref 0

let set_pb  n = 
  pb := n 

let set_vb  n = 
  vb := n 

(** 
    ***********************
    VarStringSet module and miscenalous tools
    ***********************
**)


type var_string =
  | PureVar of string (*already present*)
  | FreshVar of string (*introduced by a flatening step*) 

module VarStringSet = Set.Make(struct type t = var_string let compare = compare end)

let member_of str st = 
  VarStringSet.mem (PureVar str) st || VarStringSet.mem (FreshVar str) st

let distinct_vars v1 v2 = 
  match (v1,v2) with 
      (PureVar (id1), PureVar (id2)) ->
	id1 <> id2 
    | _ -> assert false 
	      
let string_of_var v = 
  match v with 
      PureVar(id)  -> id 
    | FreshVar(id) -> id

let display_var_set set =
  VarStringSet.iter 
    (fun s -> 
       Format.printf "%s " (string_of_var s)) set ;
  Format.printf "@\n@." 

(** returns the free variable of a term that are not outer quantified **)
let free_vars_of qvars t  = 
  let vars = ref VarStringSet.empty in
  let rec collect formula  = 
    match formula with 
      | Tapp (id, tl , _)  -> 
	  List.iter collect tl 
      | Tvar (id) ->
	  if not (VarStringSet.mem (PureVar (Ident.string id)) qvars) 
	  then
	    vars := VarStringSet.add (PureVar (Ident.string id)) !vars 
      |  _ -> () in
  collect t ; 
  !vars

(** returns the free variable of a term that are not outer quantified **)
let free_vars_of  p  =
  let vars = ref VarStringSet.empty in
  let rec collect qvars formula  = 
    match formula with 
      | Papp (_,tl,_)  ->
	  List.iter 
	    (fun t -> 
	       let v' = free_vars_of qvars t in 
	       vars := VarStringSet.union v' !vars) tl
      | Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	    Pimplies (_, a, b) ->
	  collect qvars a;
	      collect qvars b
      | Pif (a, b, c) ->
	  let v' = free_vars_of  qvars a in 
	  vars := VarStringSet.union v' !vars ;
	  collect qvars b;
	  collect qvars c
      | Pnot a ->  collect qvars a;
      | Forall (_,id,_,_,_,p) | Exists (id,_,_,p) ->    
	  collect (VarStringSet.add (PureVar (Ident.string id)) qvars) p
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) ->  collect qvars p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect VarStringSet.empty p ; 
  !vars
    
(** returns the nnf of a formula **)
let rec nnf fm =
  let boolTrue =  Tconst (ConstBool true) in
  match fm with
    | Pand (p1,p2,p,q) -> Pand(p1,p2,nnf p,nnf q)
    | Forallb (p1,p,q) -> Pand(p1,false,nnf p,nnf q)
    | Por (p,q) -> Por(nnf p,nnf q) 
    | Pimplies (_,p,q) 
      -> Por (nnf (Pnot p) ,nnf q)
    | Piff (p,q) -> 
	Pand(false,false, Por(nnf (Pnot p), nnf q),Por(nnf p , nnf(Pnot q)))
    | Pif (a, b, c) ->
	Pand (false,false,
	      Por (Papp (t_neq_bool, [boolTrue; a], []) ,
		   nnf b),
	      Por (Papp (t_eq_bool, [boolTrue; a], []) ,nnf c))
    | Forall (t1,t2,p3,p4,p5,p) -> 
	Forall(t1,t2,p3,p4,p5,nnf p)
    | Exists (t1,t2,pt,p) ->
	Exists (t1,t2,pt, nnf p) 
    | Pnot (Pnot p) -> nnf p
    | Pnot (Pand (_,_,p,q)) -> Por(nnf (Pnot p), nnf(Pnot q))
    | Pnot (Por (p,q)) -> Pand(false,false, nnf (Pnot p), nnf (Pnot q))
    | Pnot (Pimplies (pwp,p,q)) -> Pand(pwp,false , nnf p, nnf (Pnot q))
    | Pnot (Piff (p,q)) -> Por( Pand(false,false, nnf p, nnf(Pnot q)), 
				Pand(false,false, nnf (Pnot p), nnf q))
    | Pnot(Forall(_,t1,t2,ty,_,p)) -> 
	Exists(t1,t2,ty,(nnf (Pnot p)))
    | Pnot(Forallb (_,p,q)) -> Por(nnf (Pnot p), nnf(Pnot q))
    | Pnot(Exists (t1,t2,pt,p)) ->
	Forall(false,t1,t2,pt,[],(nnf (Pnot p)))
    | Pnot(Pif (a, b, c)) ->
	Por (
	  Pand (false,false,Papp (t_eq_bool, [boolTrue; a], []) ,
		nnf (Pnot b)),
	  Pand (false,false,Papp (t_neq_bool, [boolTrue; a], []) ,
		nnf (Pnot c)))
    | _ -> fm


(** reduces as possible the scope of quantifier 
    @param pr is the concerned predicate **)	
let miniscoping pr = 
  let rec mq q fm = 
    match q with 
      | Forall (t1,t2,p3,p4,p5,_) ->
	  begin
	    if not (member_of  
		      (Ident.string t2) 
		      (free_vars_of fm)) then 
	      fm 
	    else 		
	      match fm with 
		| Pand (p1,p2,p,q) -> 
		    if not (member_of  
			      (Ident.string t2) 
			      (free_vars_of p)) then 
		      let q' = mq (Forall(t1,t2,p3,p4,p5,q)) q in
		      Pand (p1,p2,p,q')
		    else
		      if not (member_of  
				(Ident.string t2) 
				(free_vars_of q)) then 
			let p' =  mq (Forall(t1,t2,p3,p4,p5,p)) p in
			Pand (p1,p2,p',q)
		      else
			Pand (p1,p2, 
			      mq (Forall (t1,t2,p3,p4,p5,p)) p,
			      mq (Forall (t1,t2,p3,p4,p5,q)) q)
		| Por (p,q) -> 
		    if not (member_of  
			      (Ident.string t2) 
			      (free_vars_of p)) then 
		      let q' = mq (Forall(t1,t2,p3,p4,p5,q)) q in
		      Por (p,q')
		    else
		      if not (member_of  
				(Ident.string t2) 
				(free_vars_of q)) then 
			let p' = mq (Forall (t1,t2,p3,p4,p5,p)) p in
			Por (p',q)
		      else
			Forall (t1,t2,p3,p4,p5, fm)
		| _ -> Forall (t1,t2,p3,p4,p5, fm)
	  end
      | Exists (t1,t2,pt,p) -> 
	  begin
	    if not (member_of  
		      (Ident.string t1) 
		      (free_vars_of fm)) then 
	      fm 
	    else
	      match fm with 
		  | Pand (p1,p2,p,q) -> 
		      if not (member_of 
				(Ident.string t1)
				(free_vars_of p)) then 
			let q' = mq (Exists(t1,t2,pt,q)) q in
			Pand (p1,p2,p,q')
		      else
			if not (member_of 
				  (Ident.string t1) 
				  (free_vars_of q)) then 
			  let p' = mq (Exists(t1,t2,pt,p)) p in
			  Pand (p1,p2,p',q)
			else
			  Exists(t1,t2,pt,fm)
		  | Por (p,q) -> 
		      if not (member_of  
				(Ident.string t1) 
				(free_vars_of p)) then 
			let q' = mq (Exists(t1,t2,pt,q)) q in
			Por (p,q')
		      else
			if not (member_of
				  (Ident.string t1) 
				  (free_vars_of q)) then 
			  let p' = mq (Exists (t1,t2,pt,p)) p in
			  Por (p',q)
			else
			  Por(
			    mq (Exists (t1,t2,pt,p)) p,
			    mq (Exists (t1,t2,pt,q)) q)
		  |_ ->  Exists(t1,t2,pt,fm)
	  end
      |_ -> assert false 
  in
  let rec minib fm = 
    match fm with 
      | Pand (p1,p2,p,q) -> Pand(p1,p2, minib p, minib q)
      | Forallb (p1,p,q) -> Pand(p1,false,minib p, minib q)
      | Por (p,q) -> Por(minib p,minib q) 
      | Forall (t1,t2,p3,p4,p5,p) as pi -> mq pi (minib p)  
      | Exists (t1,t2,pt,p) as pi -> mq pi (minib p)  
      | _ -> fm
  in 
  minib (nnf pr)
    
	    
(** compute the cnf of a predicate **)
let cnf  fm =
  let rec cnfp p = match p with 
    | Pand (p1,p2,p,q) -> Pand(p1,p2,cnfp p,cnfp q)
    | Por  (p1, p2) -> distr (cnfp p1, cnfp p2)
    | Forall (t1,t2,p3,p4,p5,p) -> Forall (t1,t2,p3,p4,p5,cnfp p) 
    | Exists (t1,t2,pt,p)  -> Exists (t1,t2,pt,cnfp p)
    | _ -> p
  and distr = function
    | (Exists (t1,t2,pt,p), y) -> Exists (t1,t2,pt,distr (p,y))
    | (y,Exists (t1,t2,pt,p)) ->  Exists (t1,t2,pt,distr (y,p))
    | (Forall (t1,t2,p3,p4,p5,p),y) -> Forall (t1,t2,p3,p4,p5,distr(p,y)) 
    | (y,Forall (t1,t2,p3,p4,p5,p)) -> Forall (t1,t2,p3,p4,p5,distr(y,p)) 
    | (Pand (p1,p2, x2, x3), y) -> Pand (p1,p2, distr (x2, y), distr (x3, y))
    | (x, Pand (p1,p2, y2, y3)) -> Pand (p1,p2, distr (x, y2), distr (x, y3))
    | (x, y) -> Por(x, y) 
  in
  cnfp (miniscoping  fm)


(** avoided vars **)
let avoided_vars = VarStringSet.singleton (PureVar "alloc") 


(** a variable name will be associated to each hypothesis **)
let hash_hyp_vars : (predicate,'a) Hashtbl.t = Hashtbl.create 20

let display_str str set  = 
  Format.printf "%s : " str ;
  display_var_set set; 
  Format.printf "@\n@." 

module SS_set = Set.Make(struct type t=VarStringSet.t let compare= compare end)

let bound_variable id = 
  v_count := !v_count+1 ;
  Ident.create ((Ident.string id)^"_"^ (string_of_int !v_count))

let my_fresh_hyp ()=
  hyp_count := !hyp_count+1 ;
  Ident.create (string_of_int !hyp_count)


(**
   @return vars which is a set of set of  variables 
   (either pure or fresh) contained in tl 
   @param qvars is a set of quantified variables 
   @tl is the list of term
**)
let vars_of_list qvars tl  = 
  let vars = ref SS_set.empty in
  let rec collect l ac_fv_set = 
    let inner_vars = ref VarStringSet.empty in 
    let f t =
      match t with 
	| Tapp (id, tl, _) ->
	    let id' = (bound_variable id) in 
	    let bv = (FreshVar (Ident.string id')) in
	    inner_vars := VarStringSet.add bv !inner_vars;
	    let l' = Tvar(id')::tl in 
	    collect l' (VarStringSet.add bv ac_fv_set)
	| Tvar (id) ->
	    if not (member_of (Ident.string id) qvars) then
	      if not (member_of (Ident.string id) ac_fv_set)
	      then
		inner_vars := VarStringSet.add (PureVar (Ident.string id)) !inner_vars 
	      else
		inner_vars := VarStringSet.add (FreshVar (Ident.string id)) !inner_vars
	| _ -> ()
    in
    List.iter f l ;
    vars := SS_set.add (VarStringSet.diff !inner_vars avoided_vars) !vars 
  in
  collect tl VarStringSet.empty ; 
  !vars



(**
   @return vars which is a set of sets of variables
   @param f the formula to be analyzed
**)
let sets_of_vars f  =
  let vars = ref SS_set.empty  in
  let rec collect qvars formula  = 
    match formula with 
      | Papp (id, [el1;el2], _) when is_eq id ->
	  begin
	    match (el1,el2) with 
	      |	(Tvar (v1), Tvar(v2)) ->
		  vars :=  SS_set.add
		    (VarStringSet.add (PureVar (Ident.string v1)) 
		       (VarStringSet.singleton (PureVar (Ident.string v2))) )
		    !vars
	      | (Tvar (v1), Tapp (_, tl, _)) ->
		  let l' = Tvar(v1)::tl in 
		  let v = vars_of_list qvars l' in
		  vars := SS_set.union v !vars
	      | (Tapp (_, tl,_), Tvar(v1)) ->
		  let l' = Tvar(v1)::tl in 
		  let v = vars_of_list qvars l' in
		  vars := SS_set.union v !vars
	      | (Tapp (id, tl, _), Tapp (_, tl', _)) ->
		  let id' = bound_variable id in
		  let tl = Tvar(id')::tl in 
		  let tl' = Tvar(id')::tl' in
		  let v = vars_of_list qvars tl in
		  let v' = vars_of_list qvars tl' in
		  vars := SS_set.union v !vars ; 
		  vars := SS_set.union v' !vars ; 
	      | _ -> ()
	  end  
      | Papp (_,tl,_) ->
	  let v = vars_of_list qvars tl in 
	  vars := SS_set.union v !vars 
      | Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	    Pimplies (_, a, b) ->
	  collect qvars a;
	      collect qvars b
      | Pif (a, b, c) ->
	  let l = a::[] in 
	  let v' = vars_of_list qvars l in 
	  vars := SS_set.union v' !vars ;
	  collect qvars b;
	  collect qvars c
      | Pnot a ->
	  collect qvars a;
      | Forall (_,id,_,_,_,p) | Exists (id,_,_,p) ->    
	  collect (VarStringSet.add (PureVar (Ident.string id)) qvars) p
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) -> 
	  collect qvars p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect VarStringSet.empty f ; 
  !vars

(** end of  VarStringSet module  **)


(** 
    ***********************
    basic strategy type 
    ***********************
**)
type var_strat =
    All
  | One 
      




(** An abstract clause only stores atomes number, the set of positive predicates symbols 
    and the set of negative symbols.
    Each predicate is represented as a string an the set of positive predicates 
    is stored as a StringSet.t
**)
module StringSet = Set.Make(struct type t=string let compare= compare end)
type abstractClause = { num:int; pos : StringSet.t ; neg : StringSet.t}  
module AbstractClauseSet = Set.Make(struct type t= abstractClause let compare= compare end)

let display_cl cl =
  let display_set_pr = 
    StringSet.fold
      (fun x1 a -> x1^" "^a) ;
  in
  Format.printf "[num: %d, pos: {%s}, neg :{%s}]" 
    cl.num
    (display_set_pr cl.pos "")
    (display_set_pr cl.neg "")

let display_cl_set set  = 
  Format.printf "{ ";
  AbstractClauseSet.iter 
    (fun c -> 
       display_cl c) set ;
  Format.printf "}\n"








(**
   ********************************
   Graph of variables 
   ******************************** 
**)
module Var_node =
struct
  type t = var_string
  let hash = Hashtbl.hash
  let compare n1 n2 = Pervasives.compare n1 n2
  let equal = (=)
end

module Var_graph =  Graph.Imperative.Graph.Concrete(Var_node)
let vg = ref (Var_graph.create())



module DisplayVarGraph = struct
  let vertex_name v = string_of_var v 
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let edge_attributes _ = []
  include Var_graph
end
  
module DotVG = Graph.Graphviz.Dot(DisplayVarGraph)


(** 
    updates the graph_of_variables
**)
let update_v_g vars = 
  (** computes the vertex **)
  VarStringSet.iter (fun n -> Var_graph.add_vertex !vg n) vars  ; 
  let rec updateb n v = 
    (** adds the edges n<->n2 for all n2 in v **)
    VarStringSet.iter (
      fun n2 -> Var_graph.add_edge !vg n n2) v ;
    (** choose another variable and computes the other edges **) 
    if not (VarStringSet.is_empty v) then 
      let n' = VarStringSet.choose v in
      updateb n' (VarStringSet.remove n' v)
  in
  if not (VarStringSet.is_empty vars) then 
    let n' = (VarStringSet.choose vars) in
    updateb 
      n'
      (VarStringSet.remove n' vars)
      
(**
   @param l list of variable declaration or predicates (hypotheses)
   @param c is the conclusion 
   Update the hashtables 
   - symbs which associates to each hypothesis its symbols (as a triple)
   and class_of_hyp 
   - class_of_hyp which associates to each hypothesis its representative 
   variable 
**)
let build_var_graph (l,c)=
  
  (** retrieves the variables of the conclusion **)
  let v = (sets_of_vars c) in 

  let v = SS_set.fold (fun s  t ->
			 (** update the graph of variables **)
			 update_v_g s ; 
			 VarStringSet.union s t) v VarStringSet.empty in
  let rec mem   = function  
    | [] ->  ()
    | Svar (id, v) :: q ->  mem  q 
    | Spred (_,p) :: q -> 
	let v = sets_of_vars p in 	
	(** for each set of variables, build the SCC
	   of the set and computes the union of all the variables **)
	let v' = 
	  SS_set.fold (fun s  t -> 
			 update_v_g s ; 
			 VarStringSet.union s t) v VarStringSet.empty in    
	(** v' is the union of all the variables **)
	let v' = VarStringSet.diff v' avoided_vars in
	(** associates v' to the hypothesis **) 
	Hashtbl.add hash_hyp_vars  p v';
	mem  q   
  in
  mem l 
    

(** **)
let removes_fresh_vars vs = 
  VarStringSet.fold 
    (fun el s -> 
       match el with 
	   PureVar _ as x -> VarStringSet.add x s 
	 | FreshVar _ -> s) 
    vs
    VarStringSet.empty


(** returns the set of  all the successors of a node **)
let succs_of vs  = 
  VarStringSet.fold 
    (fun el l -> 
       let succ_set = 
	 try 
	   let succ_list = Var_graph.succ !vg el in
           List.fold_right
	     (fun el s ->
		VarStringSet.add el s) succ_list VarStringSet.empty 
	 with _-> VarStringSet.empty in
       VarStringSet.union l succ_set  
    ) 
    vs
    VarStringSet.empty
    



(**
   @param v the initial set of variables 
   @param n the depth of the tree of variables
   @param acc acumumulates the variables that have already been visited 
   @return the ist of variables reachable in n steps
   
**)
let get_reachable_vars v n = 
  let rec get_vars_in_tree_b v n acc =
    let vret = 
      if n > 0 then
	let succ_set =  succs_of v  in
	let v' = VarStringSet.diff succ_set acc in 
	VarStringSet.union v 
	  (get_vars_in_tree_b 
	     v' 
	     (n - 1)
	     (VarStringSet.union v succ_set)
	  )
      else
	v in
    VarStringSet.diff vret avoided_vars in 
  VarStringSet.diff 
    (get_vars_in_tree_b v n VarStringSet.empty) v 
(** End of graph of variables **)


(**
   ********************************
   Graph of predicates 
   ******************************** 
**)
type positivity = Pos | Neg

let oposite = function 
    Pos -> Neg
  | Neg -> Pos

let string_value_of t = 
  match t with 
      Pos -> ""
    | Neg -> "_C"


type vertexLabel = {l:string;pol:positivity} 

module Vrtx =
struct
  type t = vertexLabel
  let hash = Hashtbl.hash
  let compare n1 n2 = Pervasives.compare n1 n2
  let equal = (=)
end

module Edg =
struct
  type t = int
  let compare = Pervasives.compare
  let default = 1
end

module PdlGraph = 
  Graph.Imperative.Digraph.ConcreteLabeled(Vrtx)(Edg)
let pdlg = ref (PdlGraph.create())

let add_edge lp rp we v v'=
  (*reverse the left since it is given as a disjunction*)
  let lp = oposite lp in 
  let le = {l=v;pol=lp} in 
  let re = {l=v';pol=rp} in 
  try 
    (* edge exists and weight is too big *)
    let (_,w,_) = PdlGraph.find_edge !pdlg le re in 
    if w > we then  
      begin
	PdlGraph.remove_edge !pdlg le re ;
	PdlGraph.add_edge_e !pdlg (le,we,re) ;
      end
  with Not_found -> 
    try 
      let le = {l=v';pol=oposite rp} in 
      let re = {l=v;pol=oposite lp} in 
      (* conterpart edge exists and weight is to big *)
      let (_,w,_) = PdlGraph.find_edge !pdlg le re in 
	  if w > we then  
	    begin
	      PdlGraph.remove_edge !pdlg le re ;
	      PdlGraph.add_edge_e !pdlg (le,we,re) ;
	  end
    with Not_found -> 
	    (* none edge exists *)
	    PdlGraph.add_edge_e !pdlg (le,we,re) 



module DisplayPdlGraph = struct
  let vertex_name v = 
    let v' = PdlGraph.V.label v in 
    v'.l^(string_value_of v'.pol)
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let edge_attributes e = 
    let l = string_of_int (PdlGraph.E.label e) in  
    [`Label l]
  include PdlGraph
end
  
module DotPdlGraph = Graph.Graphviz.Dot(DisplayPdlGraph)



(** 
    updates the graph_of_predicates
**)
let update_pdlg acs = 
  let update_pdlg_c a_clause = 
    if (StringSet.cardinal (StringSet.union a_clause.pos a_clause.neg))
      <= 1 then ()
    else
      begin
	let nlab= a_clause.num-1 in 
	let neg = ref a_clause.neg  in 
	StringSet.iter 
	  (fun n -> 
	     (* dealing with (neg n or neg n')   
		             <->   
		             n -> neg n' (or equivalentely n'-> neg n) *)   
	     neg := StringSet.remove n !neg ;
	     StringSet.iter  (fun n' -> 
				if not(n = n') then 
				  add_edge Neg Neg nlab n n'
			     ) !neg ;
	     (* dealing with (neg n or p)   
		<->   
		n -> p (or equivalentely neg p -> neg n) *)   
	     	StringSet.iter  (fun p -> 
				   if not(n = p) then 
				     add_edge Neg Pos nlab n p
				) a_clause.pos
	  ) a_clause.neg; 
	let pos = ref a_clause.pos  in 
	StringSet.iter 
	  (fun p -> 
	     (* dealing with (p or p')   
		             <->   
		             neg p-> p' (or equivalentely neg p'-> p) *)   
	     pos := StringSet.remove p !pos ;
	     StringSet.iter  (fun p' -> 
				if not(p = p') then 
				  add_edge Pos Pos nlab p p'
			     ) !pos 
	  ) a_clause.pos
      end
  in
  AbstractClauseSet.iter update_pdlg_c acs; 
  if debug then 
    begin 
      let oc  =  open_out "/tmp/gwhy_pdlg_graph.dot" in 
      DotPdlGraph.output_graph oc !pdlg 
    end

(* suppose the clause cl is in nnf *) 
let add_atom atome cl = 
  match atome with 
    | Pnot (Papp (id, l, i)) 
	when not (is_comparison id or  
		    is_int_comparison id or 
		    is_real_comparison id) -> 
	{num = cl.num + 1;
	 pos = cl.pos;
	 neg = StringSet.add (Ident.string id) cl.neg}
    | Papp (id, l, i) 
	when not (is_comparison id or  
		    is_int_comparison id or 
		    is_real_comparison id) -> 
	  {num = cl.num + 1;
	 neg = cl.neg;
	 pos = StringSet.add (Ident.string id) cl.pos}
    | _ -> 
	{num = cl.num + 1;
	 neg = cl.neg;
	 pos = cl.pos }

let rec get_abstract_clauses p = 
  let rec compute_clause p ac = 
    match p with
      | Forall (_,_,_,_,_,p) -> compute_clause p ac 
      | Exists (_,_,_,p) -> compute_clause p ac   
      | Por (p1,p2) -> compute_clause p1 (compute_clause p2 ac)
      | _ as p -> add_atom p ac in
  match p with
    | Forall (_,_,_,_,_,p) -> get_abstract_clauses p 
    | Exists (_,_,_,p) ->   get_abstract_clauses p 
    | Pand (_,_,p1,p2) -> 
	AbstractClauseSet.union 
	  (get_abstract_clauses p1)
	  (get_abstract_clauses p2)
    | Papp(_) as p -> 
	AbstractClauseSet.singleton 
	  (add_atom p {num=0; pos=StringSet.empty; neg=StringSet.empty})
    | Pnot(_) as p -> 
	AbstractClauseSet.singleton 
	  (add_atom p {num=0; pos=StringSet.empty; neg=StringSet.empty})
    | Por (_) as p -> 
	AbstractClauseSet.singleton 
	  (compute_clause 
	     p {num=0; pos=StringSet.empty; neg=StringSet.empty})
    | _ -> assert false 
    

let build_pred_graph decl = 
  let compute_pred_graph = function  
    | Dpredicate_def (loc, ident, def) ->
	let bl,p = def.scheme_type in
	let rootexp = (Papp (
			 Ident.create ident, 
			 List.map (fun (i,_) -> Tvar i) bl, [])) in 
	let piff = Piff (rootexp,p) in
	let pforall = List.fold_right 
	  (fun (var,tvar) pred  -> Forall(false,var,var,tvar,[],pred)) 
	  bl piff in 
	let p' = cnf pforall in 
	let cls = get_abstract_clauses p' in
	if debug then 
	  begin 
	    Format.printf "%a" Util.print_predicate p;
	    display_cl_set cls
	  end;
	update_pdlg cls 
    | Daxiom (loc, ident, ps) -> 
	let p= ps.scheme_type in 
	let p' = cnf p in
	let cls = get_abstract_clauses p' in 
	if debug then 
	  begin 
	    Format.printf "%a" Util.print_predicate p;
	    display_cl_set cls
	  end;
	update_pdlg cls 
    | _  -> () in
  Queue.iter compute_pred_graph decl   

(** End of graph of predicates**)

(**
   ************** 
   PdlSet 
   **************
**)
module PdlSet = Set.Make(struct type t= vertexLabel
				 let compare = compare end)
let abstr_mem_of el pdl_set = 
  PdlSet.mem {l=el.l;pol=Pos} pdl_set or 
    PdlSet.mem {l=el.l;pol=Neg} pdl_set 

let  abstr_subset_of_pdl set1 set2 = 
  PdlSet.for_all 
    (fun el -> abstr_mem_of el set2) set1       

let set_of_pred_p vs  = 
  PdlSet.fold 
    (fun v s -> 
       let pred_set = 
	 try 
	   let pred_list = PdlGraph.pred !pdlg v in
           List.fold_right
	     (fun el s ->
		PdlSet.add el s) pred_list PdlSet.empty 
	 with
	     _ -> PdlSet.empty in 
       let s' = PdlSet.union s pred_set in 
       let succ_set = 
	 try 
	   let succ_list = PdlGraph.succ !pdlg {l=v.l;pol=oposite v.pol} in
           List.fold_right
	     (fun v s ->
		PdlSet.add {l=v.l;pol=oposite v.pol}  s) 
	     succ_list PdlSet.empty
	 with   
	     _ -> PdlSet.empty in 
       PdlSet.union s' succ_set 
    ) 
    vs
    PdlSet.empty


let get_preds_of p =
  let s = ref PdlSet.empty in 
  let rec get polarity = function 
    | Papp (id, l, i) when not 
	(is_comparison id or  
	   is_int_comparison id or 
	   is_real_comparison id)-> 
	s := PdlSet.add {l=Ident.string id ;
			 pol= if polarity == 1 then Pos else Neg} !s
    | Forall (w, id, b, v, tl, p) -> 
	get polarity p 
    | Exists (id, b, v, p) ->
	get polarity p 
    | Pimplies (_,p1,p2) ->
	get (-1*polarity) p1 ;
	get polarity p2 
    | Pand (_,_,p1,p2) |  Por (p1,p2) ->
	get polarity p1 ;
	get polarity p2 
    | Piff (p1,p2) -> assert false 
    | Pnot p1 -> 
	get (-1*polarity) p1 ;
    | Pvar _ | Ptrue | Pfalse -> ()
    | _ -> () in 
  get 1 p ;
  !s

    

let get_predecessor_pred p n = 
  (** av stands for tha already visited preds
      nyt stands for not yet treated preds **)
  let rec get_preds_in_graph nyv av n = 
    if n > 0 then
      let new_preds =  set_of_pred_p nyv  in
      let nyv = PdlSet.diff new_preds av in 
      PdlSet.union new_preds  
	(get_preds_in_graph 
	   nyv 
	   (PdlSet.union new_preds av)
	   (n - 1)
	)
    else
      av in 
  get_preds_in_graph p p n   

let display_symb_of_pdl_set set =
  PdlSet.iter 
    (fun el  ->
       Format.printf "(%s,%s)" el.l (string_value_of el.pol)) set;
  Format.printf "@\n@." 
    
(** end of PdlSet **)



(**
   functions for the main function: reduce
**)
let reduce_subst (l',g') = 
  let many_substs_in_predicate sl p =
    List.fold_left 
      (fun p s ->
	 tsubst_in_predicate s p 
      ) p sl 
  in
  let many_substs_in_term sl t =
    List.fold_left 
      (fun t s ->
	 tsubst_in_term s t 
      ) t sl 
  in
  let many_substs_in_context sl = function 
    | Papp (id, l, i) -> 
	Papp (id, List.map (many_substs_in_term sl ) l, i)
    | Pif (a, b ,c) -> 
	Pif (many_substs_in_term sl  a, 
	     many_substs_in_predicate sl b, 
	     many_substs_in_predicate sl c)
    | Pfpi (t, f1, f2) -> 
	Pfpi (many_substs_in_term sl t, f1, f2)
    | Forall (w, id, b, v, tl, p) -> 
	Forall (w, id, b, v, tl,
		many_substs_in_predicate sl p)
    | Exists (id, b, v, p) ->
	Exists (id, b, v, many_substs_in_predicate sl p)
    | p -> 
	map_predicate (many_substs_in_predicate sl) p
  in

  let compute_subst (sl,fl) f =
    match f with 
      | Svar (id, v) as var_def ->  (sl,var_def::fl) 
      | Spred (id, p) ->
	  begin
	    match p with 
		Papp (id, [el1;el2], _) when is_eq id ->
		  begin
		    match (el1,el2) with 
			(Tvar (v1), t2) ->
			  let subst = subst_one v1 t2 in 			
			  (subst::sl,fl)
		      | _ -> 			  
			  (sl, Spred(id,(many_substs_in_context sl p))::fl) 
		  end 
	      | _ as p -> (sl, Spred(id,(many_substs_in_context sl p))::fl)

	  end in
  let (sl,fl) = List.fold_left compute_subst ([],[]) l' in
  let l' = List.rev fl in 
  let g' = many_substs_in_predicate sl g' in 
  (l',g')
    


  
(**
   @param concl_rep the representative variable of the conclusion
   @param l the list of hypothesis
   @return a list where the hypotheses have been filtered. 
   An hypothese is selected if 
   - it is a variable declaration
   - it is an hypothese which has the same representant than 
   the conclusion
**)
let filter_acc_variables l concl_rep selection_strategy  pred_symb =
  (** UPDATE THIS ACCORDING TO THE ARRTICLE **)
  let rec filter = function  
    | [] -> []
    | Svar (id, v) :: q -> 
	if 
	  ( member_of (Ident.string id)  concl_rep ||
	      member_of (Ident.string id) avoided_vars) 
	then
	  Svar (id, v) ::filter q 
	else
	  filter q
    | Spred (t,p) :: q -> 
	let vars =  	  
	  try Hashtbl.find hash_hyp_vars p
	  with Not_found -> assert false 
	in
	let condition = match selection_strategy with
	    All -> 
	      VarStringSet.subset 
		(removes_fresh_vars vars)
		concl_rep 
	  | One -> not (VarStringSet.is_empty 
			  (VarStringSet.inter 
			     (removes_fresh_vars vars)
			     concl_rep))
	in if condition then 
	  (* the predicate symbols has to be in the list of symbols *)
	  let preds_of_p  = get_preds_of p in 
	  if abstr_subset_of_pdl preds_of_p pred_symb then 
	    Spred (t,p):: filter q
	  else 
	    filter q
	else
	  filter q in  
  filter l


let managesGoal id ax (hyps,concl) =
  match ax with 
      Dgoal(loc,id,_) -> 
	(** retrieves the list of variables in the conclusion **)
	let v = free_vars_of concl in 
	let v = VarStringSet.diff v avoided_vars in 

	let concl_preds = get_preds_of concl    in 
	let relevant_preds = get_predecessor_pred concl_preds !pb  in 

	let reachable_vars = VarStringSet.diff 
	  (get_reachable_vars v !vb)
	  avoided_vars in 	
	let relevant_vars = VarStringSet.union reachable_vars v in 

	let l' = filter_acc_variables hyps relevant_vars  All relevant_preds in
	
	if debug then 
	  begin
	    display_str "Relevant  vars " relevant_vars ;
	    Format.printf "Relevant  preds ";
	    display_symb_of_pdl_set relevant_preds;
	    let oc  =  open_out "/tmp/gwhy_var_graph.dot" in 
	    DotVG.output_graph oc !vg     
	  end;
	Dgoal (loc,id, Env.empty_scheme (l',concl))	  
    | _ -> ax 



let reset () = 
  vg := Var_graph.create();
  pdlg := PdlGraph.create() ;
  Hashtbl.clear hash_hyp_vars;
  v_count := 0 ; 
  hyp_count := 0 


let reduce q decl= 
  reset();
  
  (** memorize the theory as a graph of predicate symbols **)
  build_pred_graph decl ;
  

  (** manages goal **)
  let q' =   match q with
      Dgoal (loc, id, s)  as ax ->
        let (l,g) = s.Env.scheme_type in
        let (l',g') = Util.intros [] g my_fresh_hyp in 
	let l' = List.append l l' in 
	
	let (l',g') = reduce_subst (l',g')  in 
	(** memorize hypotheses as a graph of variables**) 
	build_var_graph (l',g');
  
	(** focus on goal **)
	managesGoal id ax (l',g');


    | _ -> failwith "goal awaited" in
  q' 
    
