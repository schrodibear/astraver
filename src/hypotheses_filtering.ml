(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
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

(*i $Id: hypotheses_filtering.ml,v 1.7 2007-04-10 15:43:06 couchot Exp $ i*)

(*s Harvey's output *)

(**
   This modules provides a quick way to filter hypotheses of 
   a goal. 
   To do so 
   1) Hypotheses are exepnaded thanks to the intros tactic
   2) All the variables of each hypothesis are stored into a class
   3) A hypothosis is selected if it is in the same class than the conclusion 
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

let symbol_counter = ref 0

(*module Int_set = Set.Make(struct type t=int let compare= compare end)*)
module String_set = Set.Make(struct type t=string let compare= compare end)

module SS_set = Set.Make(struct type t=String_set.t let compare= compare end)

(** selected variables *)
let selected_vars = String_set.empty 

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

let vg = Var_graph.create() 


let reset () = 
  vg = Var_graph.create()



(**
@return (va,pr,fu) which is a triple of sets where
 - va is the set of free variables do not belong to qvars 
 - pr is the set of predicate symbols  
 - fu is the set of functionnal symbols  
@param f the formula which is anaclyzed
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
	  funcs := String_set.add (Ident.string id) !funcs ;
	  List.iter collect tl 
      | Tvar (id) ->
	  if not (String_set.mem (Ident.string id) qvars) 
	  then
	    if 	String.compare (Ident.string id) "alloc" <> 0 then 
	      begin
		vars := String_set.add (Ident.string id) !vars 
	      end
  in
  collect t ; 
  (!vars,!preds,!funcs)


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
@return vars which is a set of  sets of variables
   
@param f the formula which is analyzed
**)
let sets_of_vars   f  =
  let vars = ref SS_set.empty  in
  let rec collect qvars formula  = 
    match formula with 
      | Papp (id, tl, _) when is_int_comparison id  || is_real_comparison id ->
	  List.iter 
	    (fun t -> 
	       let (v',_,_) = f_symbols qvars t in 
	       vars := SS_set.add v' !vars )
	    tl
      | Papp (id, tl, _)  ->
	  List.iter 
	    (fun t -> 
	       let (v',_,_) = f_symbols qvars t in 
	       vars := SS_set.add v' !vars )
	    tl
      | Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	    Pimplies (_, a, b) ->
	  collect qvars a;
	      collect qvars b
      | Pif (a, b, c) ->
	  let (v',_,_) = f_symbols qvars a in 
	  vars := SS_set.add v' !vars ;
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
  String_set.iter (fun s -> Format.printf "%s " s) set ;
  Format.printf "@\n@." 

let display str set  = 
  (*if debug then begin *)
    Format.printf "%s : " str ;
    display_symb_of set; 
    Format.printf "@\n@." 
  (*end*)

let display (v,p,f)  = 
  display "vars" v;
  display "preds" p;
  display "func" f



(** 
    updates the graph_of_variables
**)
let update_v_g vars = 
  (* computes the vertex *)
  String_set.iter (fun n -> Var_graph.add_vertex vg n) vars  ; 
  let rec updateb n v = 
    (* adds the edges n<->n2 for all n2 in v *)
    String_set.iter (
      fun n2 -> Var_graph.add_edge vg n n2) v ;
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
  Hashtbl.clear hash_hyp_vars ;
  reset();
  let rec mem   = function  
    | [] ->  ()
    | Svar (id, v) :: q ->  mem  q 
    | Spred (_,p) :: q -> 
	(* retrieves the sets of sets of variables *)
	let v = sets_of_vars p in 
	(* for each set of variables, build the CFC of the set*)
	let v' = 
	  SS_set.fold (fun s  t -> 
			 update_v_g s ; 
			 String_set.union s t) v String_set.empty in    
	(* v' is the union of all the variables *)
	(* associates v' to the hypothesis *) 
	Hashtbl.add hash_hyp_vars  p v';
	mem  q   
  in
  mem l 
  



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
    | Svar (id, v) :: q -> Svar (id, v) ::filter q 
    | Spred (t,p) :: q -> 
	let vars =  	  
	  try Hashtbl.find hash_hyp_vars p
	  with Not_found -> raise Exit in
	(* strong criteria all variable are in the set of selected variables *)
	if (String_set.subset vars selected_vars) then 
	  Spred (t,p):: filter q  
	else
	  filter q in  
    filter l


(**
   @param s the initial set of variables 
   @param n the depth of the tree of variables
   
**)  
(*let get_vars s n *)
    (* computes the set of variables reachable in one step *)
    






let managesGoal id ax (hyps,concl) =
  match ax with 
    Dgoal(loc,id,s) -> 
      (** retrieves the list of symbols in the conclusion **)
      let (v,p,f) = symbols concl in 
      (** set informations about hypotheses **) 
      memorizes_hyp_symb hyps;


      (* variant considering variables *)
      (** update the equivalence class of the variables **)
      let l' = filter_acc_variables hyps v in  
      Dgoal (loc,id, Env.empty_scheme (l',concl))
    | _ -> ax 



let reduce q = 
  
  q 
  
  

  
