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

(*i $Id: hypotheses_filtering.ml,v 1.20 2007-06-14 08:19:12 couchot Exp $ i*)

(*s Harvey's output *)

(**
   This module provides a quick way to filter hypotheses of 
   a goal. It is activated by the option 
   --prune-hyp k 
   where k is an integer that is positive or null. 
   The number of selected hypotheses increases w.r.t. k 
 
   The internal flow is:
   1) Hypotheses are expanded thanks to the intros tactic. 
   A short goal is then produced.
   2) Variables of hypothesis are stored into a tree where 
   - a variable is represented by a vertex
   - a predicate linking some variables is represented by 
   the strongly connected component between all the vertex
   corresponding to the variables 
   3) A breadth-first search algorithm, bounded by the constant k
   computes the set of relevant variables R
   4) An hypothesis is selected  by comparing its set of variables 
   with R 
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
open Graphviz 

let bound = ref Options.pruning_hyp

let set_bound n = 
  bound := n 


let bound2 = 1 

(*let symbol_counter = ref 0*)

type var_string =
  | PureVar of string
  | FreshVar of string 

module String_set = Set.Make(struct type t=var_string let compare= compare end)

let member_of_string_set str st = 
  String_set.mem (PureVar str) st || String_set.mem (FreshVar str) st


module SS_set = Set.Make(struct type t=String_set.t let compare= compare end)

(** selected variables **)
let selected_vars = ref String_set.empty 

(** avoided vars **)
let avoided_vars = String_set.singleton (PureVar "alloc") 


(** a variable name will be associated to each hypothesis **)
let hash_hyp_vars : (predicate,'a) Hashtbl.t = Hashtbl.create 20






module Var_node =
struct
  type t = var_string
  let hash = Hashtbl.hash
  let compare n1 n2 = Pervasives.compare n1 n2
  let equal = (=)
end


module Var_graph =  Graph.Imperative.Graph.Concrete(Var_node)

let vg = ref (Var_graph.create())

let v_count = ref 0

let hyp_count = ref 0




let reset () = 
  vg := Var_graph.create();
  selected_vars := String_set.empty;
  Hashtbl.clear hash_hyp_vars;
  v_count := 0 ; 
  hyp_count := 0 


let bound_variable id = 
  v_count := !v_count+1 ;
  Ident.create ((Ident.string id)^"_"^ (string_of_int !v_count))




let my_fresh_hyp ()=
    hyp_count := !hyp_count+1 ;
    Ident.create (string_of_int !hyp_count)


(**
@return (va,pr,fu) which is a triple of sets where
 - va is the set of free variables do not belong to qvars 
 - pr is the set of predicate symbols  
 - fu is the set of functionnal symbols  
@param f the formula which is analyzed
@param qvars the set of variables that are outer quantified
@TODO : REPLACE the comparison to "alloc"
**)


let f_symbols qvars t  = 
  let vars = ref String_set.empty in
  let rec collect formula  = 
    match formula with 
      | Tconst (ConstInt n) -> ()
      | Tconst (ConstBool _) -> () 
      | Tconst ConstUnit -> ()
      | Tconst (ConstFloat _) -> ()
      | Tderef _ -> ()
      | Tapp (id, tl , _)  -> 
	  List.iter collect tl 
      | Tvar (id) ->
	  if not (String_set.mem (PureVar (Ident.string id)) qvars) 
	  then
	    vars := String_set.add (PureVar (Ident.string id)) !vars 
  in
  collect t ; 
  !vars



(**
@return vars
**)


let vars_of_list qvars tl  = 
  let vars = ref SS_set.empty in
  let rec collect l ac_fv_set = 
    let inner_vars = ref String_set.empty in 
    let f t =
      match t with 
	| Tconst (ConstInt n) -> ()
	| Tconst (ConstBool _) -> () 
	| Tconst ConstUnit -> ()
	| Tconst (ConstFloat _) -> ()
	| Tderef _ -> ()
	| Tapp (id, tl, _) ->
	    let id' = (bound_variable id) in 
	    let bv = (FreshVar (Ident.string id')) in
	    inner_vars := String_set.add bv !inner_vars;
	    let l' = Tvar(id')::tl in 
	    collect l' (String_set.add bv ac_fv_set)
	| Tvar (id) ->
	    if not (member_of_string_set (Ident.string id) qvars) then
	      if not (member_of_string_set (Ident.string id) ac_fv_set)
	      then
		inner_vars := String_set.add (PureVar (Ident.string id)) !inner_vars 
	      else
		inner_vars := String_set.add (FreshVar (Ident.string id)) !inner_vars
    in
    List.iter f l ;
    vars := SS_set.add (String_set.diff !inner_vars avoided_vars) !vars 
  in
  collect tl String_set.empty ; 
  !vars


(**
@return (va,pr,fu) which is a triple of sets where
 - va is the set of free variables
 - pr is the set of predicate symbols  
 - fu is the set of functionnal symbols  
@param f the formula which is analyzed
**)
let symbols_vars  f  =
  let vars = ref String_set.empty in
  let rec collect qvars formula  = 
    match formula with 
      | Papp (id, tl, _) when is_int_comparison id  || is_real_comparison id ->
	  List.iter 
	    (fun t -> 
	       let v' = f_symbols qvars t in 
	       vars := String_set.union v' !vars)
	    tl
      | Papp (id, tl, _)  ->
	  List.iter 
	    (fun t -> 
	       let v' = f_symbols qvars t in 
	       vars := String_set.union v' !vars)
	    tl
      | Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	    Pimplies (_, a, b) ->
	  collect qvars a;
	      collect qvars b
      | Pif (a, b, c) ->
	  let v' = f_symbols qvars a in 
	  vars := String_set.union v' !vars ;
	  collect qvars b;
	  collect qvars c
      | Pnot a ->
	  collect qvars a;
      | Forall (_,id,_,_,_,p) | Exists (id,_,_,p) ->    
	  (*let n= Symbol_container.add (Ident.string id) in 
	  vars := String_set.add n !vars ;*)
	  collect (String_set.add (PureVar (Ident.string id)) qvars) p
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) -> (* TODO: print name *)
	  collect qvars p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect String_set.empty f ; 
  !vars

(**
@return vars which is a set of sets of variables
@param f the formula to be analyzed
**)
let sets_of_vars   f  =
  let vars = ref SS_set.empty  in
  let rec collect qvars formula  = 
    match formula with 
	(** TODO faire un cas particulier ici pour l'égalité ?**)
	
      | Papp (id, [el1;el2], _) when is_eq id ->
	  begin
	    match (el1,el2) with 
		(Tvar (v1), Tvar(v2)) ->
		  vars :=  SS_set.add
		    (String_set.add (PureVar (Ident.string v1)) 
		       (String_set.singleton (PureVar (Ident.string v2))) )
		    !vars
		    (* TODO memorize that V1 is equal to v2 *)
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
		  Format.printf " applications %s \n"
		    (Ident.string id);
		  let v = vars_of_list qvars tl in
		  let v' = vars_of_list qvars tl' in
		  vars := SS_set.union v !vars ; 
		  vars := SS_set.union v' !vars ; 
	      | (_,_) -> ()
	  end  
      | Papp (id, tl, _) ->
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
	  collect (String_set.add (PureVar (Ident.string id)) qvars) p
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) -> 
	  collect qvars p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect String_set.empty f ; 
  !vars






let display_symb_of set =
  String_set.iter (fun s -> 
		     let s' = 
		       match s with 
			   PureVar(id)  -> "pv "^id 
			 | FreshVar(id) -> "fv "^id
		     in
		     Format.printf "%s \n" s'
		  ) set ;
  Format.printf "@\n@." 

let display_set str set  = 
  (*if debug then begin *)
    Format.printf "%s : " str ;
    display_symb_of set; 
    Format.printf "@\n@." 
  (*end*)

let display (v,p,f)  = 
  display_set "vars" v;
  display_set "preds" p;
  display_set "func" f



(** 
    updates the graph_of_variables
**)
let update_v_g vars = 
  (* computes the vertex *)
  String_set.iter (fun n -> Var_graph.add_vertex !vg n) vars  ; 
  let rec updateb n v = 
    (* adds the edges n<->n2 for all n2 in v *)
    String_set.iter (
      fun n2 -> Var_graph.add_edge !vg n n2) v ;
    (* choose another variable and computes the other edges *) 
    if not (String_set.is_empty v) then 
      let n' = String_set.choose v in
      updateb n' (String_set.remove n' v)
  in
  if not (String_set.is_empty vars) then 
    let n' = (String_set.choose vars) in
    updateb 
      n'
      (String_set.remove n' vars)
      

 

(**
   @param l list of variable declaration or predicates (hypotheses)
   @param c is the conclusion 
   Update the hashtables 
   - symbs which associates to each hypothesis its symbols (as a triple)
     and class_of_hyp 
   - class_of_hyp which associates to each hypothesis its representative 
   variable 
**)
let memorizes_hyp_symb (l,c)= 

  
  (** retrieves the variables of the conclusion **)
  let v = (sets_of_vars c) in 
  let v = SS_set.fold (fun s  t -> 
			 update_v_g s ; 
			 String_set.union s t) v String_set.empty in

  

  let rec mem   = function  
    | [] ->  ()
    | Svar (id, v) :: q ->  mem  q 
    | Spred (_,p) :: q -> 
	(* retrieves the sets of sets of variables *)
	(*Format.printf "%a @\n@." print_predicate p; *)
	let v = sets_of_vars p in 
	(*SS_set.iter (fun s-> 
		       display_set "detected vars in hyp " s ) v; *)
	

	
	(* for each set of variables, build the CFC 
	   of the set and computes the union of all the variables*)
	let v' = 
	  SS_set.fold (fun s  t -> 
			 update_v_g s ; 
			 String_set.union s t) v String_set.empty in    
	(* v' is the union of all the variables *)
	(* associates v' to the hypothesis *)
	let v' = String_set.diff v' avoided_vars in 
	Hashtbl.add hash_hyp_vars  p v';
	mem  q   
  in
  mem l 
  

(**
   @param v the initial set of variables 
   @param n the depth of the tree of variables
   @param acc acumumulates the variables that have already been visited 
   @return the ist of variables reachable in n steps
   
**)
let rec get_vars_in_tree v n acc = 
  let vret = 
    if n > 0 then
      (* computes the list of variables reachable in one step *)
      let succ_list = String_set.fold
	(fun el l -> 
	   (*Printf.printf "vars attached to %s : " el ;*)
	   let l' = Var_graph.succ !vg el in
	   (*List.iter (fun el -> 
			Format.printf " %s," el) l';
	   Format.printf "@\n@.";*)
	   List.append l l' 
	) 
	v
	[] in
      (* computes the set of variables reachable in one step *)
      let succ_set = List.fold_right
	(fun el s ->
	   String_set.add el s) succ_list String_set.empty in
      let v' = String_set.diff succ_set acc in 
      String_set.union v 
	(get_vars_in_tree 
	   v' 
	   (n - 1)
	 (String_set.union v succ_set)
	)
    else
      v in
  String_set.diff vret avoided_vars
    

(**
   @param concl_rep the the representative variable of the conclusion
   @param l the list of hypothesis
   @return a list where the hypotheses have been filtered. 
   An hypothese is selected if 
   - it is a variable declaration
   - it is an hypothese which has the same representant than 
   the conclusion
**)
let filter_acc_variables l concl_rep=
  let rec filter = function  
    | [] -> []
    | Svar (id, v) :: q -> 
	if 
	  ( member_of_string_set (Ident.string id)  !selected_vars ||
	     member_of_string_set (Ident.string id) avoided_vars) 
	then
	  Svar (id, v) ::filter q 
	else
	  filter q
    | Spred (t,p) :: q -> 
	(*Format.printf "Predicate : %a @\n@." print_predicate p;*)
	let vars =  	  
	  try Hashtbl.find hash_hyp_vars p
	  with Not_found -> raise Exit 
	in
	(*display_set "Vars: " vars ; *)
	
	(* strong criteria: all variable 
	   of the hypothessis must be in the set of selected variables *) 
	if (String_set.subset vars !selected_vars) then  
	
	(*  weakest criteria: at least one  variable 
	   of the hypothessis should  be in the set of selected variables *) 
	  (* if (not (String_set.is_empty (String_set.inter vars !selected_vars)))
	then *)
	  Spred (t,p):: filter q  
	else
	  (* let v' = String_set.diff vars !selected_vars  
	     in
	     display_set "Diff: " v' ; *)
	  filter q in  
  filter l



(**
   @returns a set of set varaibles. 
   The variables of the set of variables represent a path 
   in the graph of variables between two varaiables of the goal

   @param v is the set of variables of the goal

**)
let get_linked_vars v = 
  let returned_set = ref SS_set.empty in 

  
  
  !returned_set
    






module Display = struct
  let vertex_name v = 
    match Var_graph.V.label v with 
	PureVar(id)  -> "pv_"^id 
      | FreshVar(id) -> "fv_"^id
  let graph_attributes _ = []
  let default_vertex_attributes _ = []
  let vertex_attributes _ = []
  let default_edge_attributes _ = []
  let get_subgraph _ = None
  let edge_attributes _ = []
  include Var_graph
end
  
module Dot = Graphviz.Dot(Display)

  


let managesGoal id ax (hyps,concl) =
  match ax with 
    Dgoal(loc,id,s) -> 
      (** retrieves the list of symbols in the conclusion **)
      let v = symbols_vars concl in 
      let v = String_set.diff v avoided_vars in 

      (** set informations about hypotheses **) 
      memorizes_hyp_symb (hyps,concl);



      (** variables liées par un chemin de variables **)
      let set_of_pairs = get_linked_vars v in 

      
      



      (** select the relevant variables **)
      selected_vars := get_vars_in_tree v !bound String_set.empty;
      

      if debug then 
	display_set " Selected vars" !selected_vars ; 
      

      let l' = filter_acc_variables hyps v in

      (** output the dot version of variables graph **)
      if debug then 
	begin 
	  let oc  =  open_out "/tmp/gwhy_var_graph.dot" in 
	  Dot.output_graph oc !vg 
	end; 
      Dgoal (loc,id, Env.empty_scheme (l',concl))
	(*Dgoal (loc,id, Env.empty_scheme (hyps,concl))*)
		   
    | _ -> ax 




 
let reduce q = 
  reset();
  let q' =   match q with
      Dgoal (loc, id, s)  as ax ->
        let (l,g) = s.Env.scheme_type in
        let (l',g') = Util.intros [] g my_fresh_hyp in 

	managesGoal id ax (List.append l l',g');


    | _ -> failwith "goal awaited" in
  q' 
  
  

  
