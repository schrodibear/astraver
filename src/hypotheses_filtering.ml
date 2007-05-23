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

(*i $Id: hypotheses_filtering.ml,v 1.14 2007-05-23 13:18:20 couchot Exp $ i*)

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


let threshold = Options.pruning_hyp

(*let symbol_counter = ref 0*)

module String_set = Set.Make(struct type t=string let compare= compare end)

module SS_set = Set.Make(struct type t=String_set.t let compare= compare end)

(** selected variables **)
let selected_vars = ref String_set.empty 

(** avoided vars **)
let avoided_vars = String_set.singleton "alloc" 


(** a variable name will be associated to each hypothesis **)
let hash_hyp_vars : (predicate,'a) Hashtbl.t = Hashtbl.create 20


(*
type node =
    {
      node_label : string;
    }
*)

module Var_node =
struct
  type t = string
  let hash = Hashtbl.hash
  let compare n1 n2 = Pervasives.compare n1 n2
  let equal = (=)
end


module Var_graph =  Graph.Imperative.Graph.Concrete(Var_node)

let vg = ref (Var_graph.create())


let reset () = 
  vg := Var_graph.create();
  selected_vars := String_set.empty;
  Hashtbl.clear hash_hyp_vars  


let bound_variable =
  let count = ref 0 in
  function id ->  
    count := !count+1 ;
    Ident.create ((Ident.string id)^"_"^ (string_of_int !count))

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
  let preds = ref String_set.empty in 
  let funcs = ref String_set.empty in
  let rec collect formula  = 
    match formula with 
      | Tconst (ConstInt n) -> ()
      | Tconst (ConstBool _) -> () 
      | Tconst ConstUnit -> ()
      | Tconst (ConstFloat _) -> ()
      | Tderef _ -> ()
      | Tapp (id, tl , _) when id == if_then_else -> 
	  List.iter collect tl 
      | Tapp (id, tl, _) when is_arith_binop id ->
	  List.iter collect tl 
      | Tapp (id, tl, _) ->
	  (*Symbol_container.add  id ;*)
	  funcs := String_set.add (Ident.string id) !funcs ;
	  List.iter collect tl 
      | Tvar (id) ->
	  if not (String_set.mem (Ident.string id) qvars) 
	  then
	    vars := String_set.add (Ident.string id) !vars 
  in
  collect t ; 
  (!vars,!preds,!funcs)



(**
@return vars
**)


let vars_of_list qvars tl  = 
  let vars = ref SS_set.empty in

  let rec collect l = 
    let inner_vars = ref String_set.empty in 
    let f t =
      match t with 
	| Tconst (ConstInt n) -> ()
	| Tconst (ConstBool _) -> () 
	| Tconst ConstUnit -> ()
	| Tconst (ConstFloat _) -> ()
	| Tderef _ -> ()
	| Tapp (id, tl, _) ->
	    let bv = bound_variable id in
	    inner_vars := String_set.add (Ident.string bv) !inner_vars;
	    let l' = Tvar(bv)::tl in 
	    collect l'
	| Tvar (id) ->
	    if not (String_set.mem (Ident.string id) qvars) 
	      (* && 	      not (String_set.mem (Ident.string id) avoided_vars)*) 
	    then
	      inner_vars := String_set.add (Ident.string id) !inner_vars
    in
    List.iter f l ;
    vars := SS_set.add !inner_vars !vars 
  in
  collect tl ; 
  !vars


(**
@return (va,pr,fu) which is a triple of sets where
 - va is the set of free variables
 - pr is the set of predicate symbols  
 - fu is the set of functionnal symbols  
@param f the formula which is analyzed
**)
let symbols  f  =
  let vars = ref String_set.empty in
  let preds = ref String_set.empty in 
  let funcs = ref String_set.empty in
  let rec collect qvars formula  = 
    match formula with 
      | Papp (id, tl, _) when is_int_comparison id  || is_real_comparison id ->
	  List.iter 
	    (fun t -> 
	       let (v',p',f') = f_symbols qvars t in 
	       vars := String_set.union v' !vars ;
	       preds := String_set.union p' !preds ; 
	       funcs := String_set.union f' !funcs) 
	    tl
      | Papp (id, tl, _)  ->
	  preds := String_set.add (Ident.string id )  !preds ;
	  List.iter 
	    (fun t -> 
	       let (v',p',f') = f_symbols qvars t in 
	       vars := String_set.union v' !vars ;
	       preds := String_set.union p' !preds ; 
	       funcs := String_set.union f' !funcs) 
	    tl
      | Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	    Pimplies (_, a, b) ->
	  collect qvars a;
	      collect qvars b
      | Pif (a, b, c) ->
	  let (v',p',f') = f_symbols qvars a in 
	  vars := String_set.union v' !vars ;
	  preds := String_set.union p' !preds ; 
	  funcs := String_set.union f' !funcs;
	  collect qvars b;
	  collect qvars c
      | Pnot a ->
	  collect qvars a;
      | Forall (_,id,_,_,_,p) | Exists (id,_,_,p) ->    
	  (*let n= Symbol_container.add (Ident.string id) in 
	  vars := String_set.add n !vars ;*)
	  collect (String_set.add (Ident.string id) qvars) p
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) -> (* TODO: print name *)
	  collect qvars p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect String_set.empty f ; 
  (!vars,!preds,!funcs)

(**
@return vars which is a set of sets of variables
   
@param f the formula which is analyzed
**)
let sets_of_vars   f  =
  let vars = ref SS_set.empty  in
  let rec collect qvars formula  = 
    match formula with 
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
	  collect (String_set.add (Ident.string id) qvars) p
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) -> (* TODO: print name *)
	  collect qvars p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect String_set.empty f ; 
  !vars






let display_symb_of set =
  String_set.iter (fun s -> Format.printf "%s \n" s) set ;
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
   Update the hashtables 
   - symbs which associates to each hypothesis its symbols (as a triple)
     and class_of_hyp 
   - class_of_hyp which associates to each hypothesis its representative 
   variable 
**)
let memorizes_hyp_symb l = 
  
  reset();
  let rec mem   = function  
    | [] ->  ()
    | Svar (id, v) :: q ->  mem  q 
    | Spred (_,p) :: q -> 
	(* retrieves the sets of sets of variables *)
	(*	Format.printf "%a @\n@." print_predicate p; *)
	let v = sets_of_vars p in 
	(*SS_set.iter (fun s-> 
		       display_set "detected vars in hyp " s ) v;*) 
	

	
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
	   (*Format.printf "vars attached to %s : " el ;*)
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
	  ( String_set.mem (Ident.string id) !selected_vars ||
	      String_set.mem (Ident.string id) avoided_vars) 
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
	
	(* (* strong criteria: all variable 
	   of the hypothessis must be in the set of selected variables *) *)
	if (String_set.subset vars !selected_vars) then  
	(* (* weakest criteria: at least one  variable 
	   of the hypothessis should  be in the set of selected variables *) 
	if (not (String_set.is_empty (String_set.inter vars !selected_vars)))
	then *)
	  Spred (t,p):: filter q  
	else
	  (* let v' = String_set.diff vars !selected_vars  
	     in
	     display_set "Diff: " v' ; *)
	  filter q in  
  filter l








let managesGoal id ax (hyps,concl) =
  match ax with 
    Dgoal(loc,id,s) -> 
      (** retrieves the list of symbols in the conclusion **)
      let (v,p,f) = symbols concl in 
      (** set informations about hypotheses **) 
      memorizes_hyp_symb hyps;
      (** select the relevant variables **)
      selected_vars := get_vars_in_tree v threshold String_set.empty;
      display_set "Selected vars: " !selected_vars ; 
      

      (* variant considering variables *)
      (** update the equivalence class of the variables **)
      let l' = filter_acc_variables hyps v in  
      Dgoal (loc,id, Env.empty_scheme (l',concl))
    | _ -> ax 



let reduce q = 
  let q' =   match q with
      Dgoal (loc, id, s)  as ax ->
        let (l,g) = s.Env.scheme_type in
        let (l',g') = Util.intros [] g in 
	(*Printf.printf "Size of l %d " (List.length l');*)
        (** TODO: REMOVE this  **)
	managesGoal id ax (List.append l l',g') 
    | _ -> failwith "goal awaited" in
  q' 
  
  

  
