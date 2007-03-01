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

(*i $Id: hypotheses_filtering.ml,v 1.1 2007-03-01 11:11:00 couchot Exp $ i*)

(*s Harvey's output *)

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
open Unionfind 

let threshold = 1

let symbol_counter = ref 0

module Int_map = Map.Make(struct type t=int let compare= compare end)

module Int_set = Set.Make(struct type t=int let compare= compare end)


module  Symbol_container = 
struct 
  module Id_map = Map.Make(struct type t=string let compare= compare end)


  let uniqueNumberGenerator () = 
    incr symbol_counter; !symbol_counter


  let m = ref Id_map.empty

  let add symb = 
    let n = uniqueNumberGenerator () in 
    m:= Id_map.add symb n !m ;
    n

  let reset () = 
    m := Id_map.empty
  
  let index_of symb =
    try 
       Id_map.find symb !m
    with 
	Not_found -> 
	  Printf.printf "Symbol %s not found \n" symb;
	  raise Exit
end


let f_symbols t  = 
  let vars = ref Int_set.empty in
  let preds = ref Int_set.empty in 
  let funcs = ref Int_set.empty in
  let rec collect formula  = 
    match formula with 
      | Tconst (ConstInt n) -> ()
      | Tconst (ConstBool _) -> () 
      | Tconst ConstUnit -> ()
      | Tconst (ConstFloat _) -> ()
      | Tderef _ -> ()
      | Tapp (id, tl , _) when id == if_then_else -> 
	  List.iter collect tl 
      | Tapp (id, tl, _) when is_relation id || is_arith id ->
	  List.iter collect tl 
      | Tapp (id, tl, _) ->
	  let n= Symbol_container.add (Ident.string id) in 
	  funcs := Int_set.add n !funcs ;
	  List.iter collect tl 
      | Tvar (id) ->
	  let n= Symbol_container.add (Ident.string id) in 
	  vars := Int_set.add n !vars ;
  in
  collect t ; 
  (!vars,!preds,!funcs)


let symbols  f  =
  let vars = ref Int_set.empty in
  let preds = ref Int_set.empty in 
  let funcs = ref Int_set.empty in
  let rec collect formula  = 
    match formula with 
      | Papp (id, tl, _) ->
	  let n = Symbol_container.add (Ident.string id) in
	  preds := Int_set.add n  !preds ;
	  List.iter 
	    (fun t -> 
	       let (v',p',f') = f_symbols t in 
	       vars := Int_set.union v' !vars ;
	       preds := Int_set.union p' !preds ; 
	       funcs := Int_set.union f' !funcs) 
	    tl
      | Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	    Pimplies (_, a, b) ->
	  collect a;
	      collect b
      | Pif (a, b, c) ->
	  let (v',p',f') = f_symbols a in 
	  vars := Int_set.union v' !vars ;
	  preds := Int_set.union p' !preds ; 
	  funcs := Int_set.union f' !funcs;
	  collect b;
	  collect c
      | Pnot a ->
	  collect a;
      | Forall (_,id,n,t,_,p) | Exists (id,n,t,p) ->    
	  let n= Symbol_container.add (Ident.string id) in 
	  vars := Int_set.add n !vars ;
	  collect p
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) -> (* TODO: print name *)
	  collect p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect f ; 
  (!vars,!preds,!funcs)

(*
let rec add_relevant_in elt s = 
  if Int_set.mem elt s then
    s
  else  
    Int_set.add elt (Int_set.fold add_relevant_in (Theory_container.depends_on elt) s)
      

let rank n s = 
  let s1 = Theory_container.produces n in 
  let r = 
    if Int_set.subset s1 s then 1 else 0 in 
  (*Printf.printf "rank %d \n" r ;*)
  r


let filter rs selectedAx notYetSelectedAx = 
  let irrelevant = ref notYetSelectedAx in
  let relevant = ref selectedAx in
  let new_rs = ref rs in 
  let f ax =
    let r = rank ax rs in 
    if r >= threshold then
      begin 
	relevant := add_relevant_in ax !relevant ;
	irrelevant := Int_set.remove ax !irrelevant;
	new_rs := Int_set.union rs (Theory_container.produces ax)
      end ; 
    if debug then begin 
	Printf.printf "ax (%d) has rank %d \n" ax r
      end    
  in
  Int_set.iter f notYetSelectedAx ;
  (!new_rs,!relevant,!irrelevant)


let display_symb_of set =
  Int_set.iter (fun s -> Printf.printf "%d " s) set 
 
let display (q,s) n = 
  let di = function 
    | Dtype (_, _, id) -> Printf.printf  "type %s (%d) : "  id 
    | Dlogic (_, id, t) -> Printf.printf  "arit %s (%d) : " id   
    | Dpredicate_def (_, id, d) -> Printf.printf  "def_pred %s (%d): " id 
    | Dfunction_def (_, id, d) -> Printf.printf  "def_func %s (%d): " id 
    | Daxiom (_, id, p)          -> Printf.printf  "axiom %s (%d): "  id 
    | Dgoal (_, id, s)   -> Printf.printf  "goal %s (%d):"  id 
  in 
  if debug then begin 
    (di q) n;
    display_symb_of s; Printf.printf "\n" 
  end
*)

let managesGoal id ax (hyps,concl) =   
  let setOfSymbols = ref (symbols concl) in 
  ()

    
let launcher decl = match decl with   
  | Dtype (_,_,_) | Dlogic (_,_,_) | Dpredicate_def (_,_,_) |Daxiom (_,_,_)
  | Dfunction_def (_,_,_)  -> () | Dgoal (_, id, s)  as ax -> 
      managesGoal id ax s.Env.scheme_type 




(**
   @param q is a logic_decl Queue 
   @returns the pruned theory 
**)

let reduce q = 
  Symbol_container.reset();  
  Queue.iter launcher q 
  
  

  
