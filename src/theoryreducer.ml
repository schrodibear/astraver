(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: theoryreducer.ml,v 1.1 2006-10-02 09:08:38 couchot Exp $ i*)

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



module FormulaContainer = 
struct 
  (**
     sContainer is the unique hash table that 
     memorizes all the elements of the theory and the goal **)  
  let fContainer :(int, 'a) Hashtbl.t = Hashtbl.create 20

  (**
     @returns a unique integer that is used to inde the 
     fContainerainer hash table
  **)    
  let uniqueNumberGenerator = 
    let x = ref 1 in
    fun () -> incr x; !x
      
  (**
     @param f is the formula we want to store
     @return n is the index where the formula has been stored
  **)
  let add f = 
    let n  = uniqueNumberGenerator () in 
    Hashtbl.add fContainer n f ;
    n
end 
  
module  SymbolContainer = 
struct 

  (**
     sContainer is the unique hash table that stores 
     all the symbol (predicative or functional) of the 
     theory and the goal **)  
  let sContainer :(string, int) Hashtbl.t = Hashtbl.create 20
    
  let outputSymbolList  e =
    Printf.printf "%s \t \n" e ; 
    let myPrint k v = 
      (Printf.printf "%s \t \n" k)
    in
    (Hashtbl.iter myPrint sContainer)


  (**
     @param e the element which we are looking for the number 
     @param n the default number that is returned if the element 
     does not belongs to the table
     @return either the number  corresponding to s or the number n otherwise
  **)
  let getClassNumberOfSymbol e n   = 
    try 
      Hashtbl.find sContainer e
    with Not_found -> n

  (**
     @param e the element we want to add 
     @param n the number that is associated to the element
     The function adds into the hashtable the (e,n) tuple 
  **)
  let addSymbol e n= 
    Hashtbl.add sContainer e n

  module StringSet = Set.Make(struct type t=string let compare= compare end)


  (**
     collects the functionnal ore predicative symbols
     of the term given in parameter 
     @paramater f : the formula we are parsing   
     @returns the StringSet that contains all the symbols 
     of the formula
  **)	
  let functionalSymbolsCollect  f  = (*: Logic_decl.t -> StringSet*) 
    (** symbols the result **)
    let symbolsSet  = ref StringSet.empty  in 
    let rec collect formula  = 
      let rec collectIntoAList  l = match l with 
	  [] -> () 
	|  p :: r -> 
	     collect p ;
	     collectIntoAList r in 
      match formula with 
	| Tconst (ConstInt n) -> 
	    symbolsSet  := StringSet.add n !symbolsSet 
	| Tconst (ConstBool b) -> () 
	| Tconst ConstUnit -> ()
	| Tconst (ConstFloat (i,f,e)) ->
	    symbolsSet  :=  StringSet.add  ("const_real_"^i^"_"^f^"_"^e) !symbolsSet
	| Tderef _ -> ()
	| Tapp (id, [a; b; c], _) when id == if_then_else -> 
	    collect a; 
	    collect b;
	    collect c  
	| Tapp (id, tl, _) when is_relation id || is_arith id ->
	    symbolsSet  := StringSet.add (Ident.string id)  !symbolsSet ;
	    collectIntoAList tl 
	| Tapp (id, [], i) -> 
	    symbolsSet  := StringSet.add (Ident.string id) !symbolsSet
	| Tapp (id, tl, i) ->
	    symbolsSet  := StringSet.add (Ident.string id) !symbolsSet;
	    collectIntoAList tl 
	| _ -> ()
    in
    collect f ; 
    !symbolsSet

  (**
     collects the functionnal and predicative 
     symbols of the formula given in parameter 
     @paramater f : the formula we are parsing   
     @returns the String set that contains all the symbols 
     of the formula
  **)	
  let rec functionalSymbolsCollectFromList  l  =  
    match l with 
	[] -> StringSet.empty
      | t :: q ->  StringSet.union  (functionalSymbolsCollect t)
	  (functionalSymbolsCollectFromList q)
	    

  (**
     collects the functionnal and predicative 
     symbols of the formula given in parameter 
     @paramater f : the formula we are parsing   
     @returns the String set that contains all the symbols 
     of the formula
  **)	
  let predicativeSymbolsCollect  f  =
    (** symbols the result **)
    let symbolsSet  = ref StringSet.empty  in 
    let rec collect formula  = 
      let rec collectIntoAList  l = match l with 
	  [] -> () 
	|  p :: r -> 
	     collect p ;
	     collectIntoAList r in 
      match formula with 
	  (* TODO update this 
	     | Papp (id, [t], _) when id == well_founded ->
	     symbolsSet  := StringSet.add (functionalSymbolsCollect id) !symbolsSet  *)
	| Papp (id, [a; b], _) when is_eq id || is_neq id || id == t_zwf_zero->
	    symbolsSet  := StringSet.union (functionalSymbolsCollect a) 
	      !symbolsSet ;
	    symbolsSet  := StringSet.union (functionalSymbolsCollect b) 
	      !symbolsSet 
	| Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	      Pimplies (_, a, b) ->
	    collect a;
		collect b
	| Papp (id, tl, _) when is_relation id || is_arith id ->
	    symbolsSet  := StringSet.union (functionalSymbolsCollectFromList tl)
	      !symbolsSet   
	| Papp (id, tl, i) -> 
	    symbolsSet  := StringSet.union (functionalSymbolsCollectFromList tl) 
	      !symbolsSet ;   
	    symbolsSet  := StringSet.add  (Ident.string id)  !symbolsSet 
	| Pif (a, b, c) ->
	    symbolsSet  := StringSet.union (functionalSymbolsCollect a) 
	      !symbolsSet ;
	    collect b;
	    collect c
	| Pnot a ->
	    collect a;
	| Forall (_,id,n,t,_,p) | Exists (id,n,t,p) ->    
	    collect p
	| Pfpi _ ->
	    failwith "fpi not yet suported "
	| Pnamed (_, p) -> (* TODO: print name *)
	    collect p 
	|_ -> ()
    in
    collect f ; 
    !symbolsSet
      

end






module  EquivClass = 
struct 

  module IntSet = Set.Make(struct type t=int let compare= compare end)

  let formulaeClassesNumber = ref IntSet.empty
    
    


  (** the union find module for using classes **)
  module UnionFindInt = Unionfind.Make (struct 
					  type t = int let 
					      hash = Hashtbl.hash 
						       let compare = compare 
						       let equal = (=) 
					end)


  (** the data structure that stores the equivalence classes 
      for the axioms number **)
  let partition : UnionFindInt.t = 
    let fill n = 
      let temp = ref [] in
      for i= 0 to n-1 do
	temp := i :: !temp
      done ;
      !temp in
    UnionFindInt.init (fill 1000)

  let addFormula n =
    formulaeClassesNumber := IntSet.add 
      n
      !formulaeClassesNumber 
      

  let merge (m:int)  (n:int) = 
    UnionFindInt.union m n partition 



  let getReducedTheory t=
    let localSet = ref IntSet.empty in 
    if IntSet.is_empty !formulaeClassesNumber  then 
      Queue.create () 
    else
      (** computes the set of remaining elements number **)
      let n = List.hd (IntSet.elements !formulaeClassesNumber)  in
      let goalClassNumber = UnionFindInt.find n partition in 
      let addToSet k v = 
	if ((UnionFindInt.find k partition) = goalClassNumber) then
	  localSet := IntSet.add k !localSet
      in
      Hashtbl.iter addToSet FormulaContainer.fContainer ;
      (** computes the ordered queue of elements **)
      let axiomQueue = Queue.create() in 
      let rec addToQueue l = match l with  
	  [] -> ()
	| q :: t -> 
	    Queue.push (Hashtbl.find  FormulaContainer.fContainer q)  axiomQueue ;
	    addToQueue t
      in 
      addToQueue  (IntSet.elements !localSet) ;
      axiomQueue


  let mergeFormulaeClasses s =
    let rec recursiveMerge n l = match (n,l) with 
	(_,[]) -> ()
      | (0,t::q) -> recursiveMerge t q 
      | (n,t::q) -> merge n t 
    in
    recursiveMerge 0 (IntSet.elements !formulaeClassesNumber)
      

	
	
end
  




let prefix id =
  if id == t_lt then assert false
  else if id == t_le then assert false
  else if id == t_gt then assert false
  else if id == t_ge then assert false
    (* int cmp *)
  else if id == t_lt_int then "<"
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
    (* int ops *)
  else if id == t_add_int then "+"
  else if id == t_sub_int then "-"
  else if id == t_mul_int then "*"
  else if id == t_div_int then "int_div"
  else if id == t_mod_int then "int_mod"
  else if id == t_neg_int then "-"
    (* real ops *)
  else if id == t_add_real 
    || id == t_sub_real 
    || id == t_mul_real 
    || id == t_div_real 
    || id == t_neg_real 
    || id == t_sqrt_real 
    || id == t_real_of_int 
    || id == t_lt_real
    || id == t_le_real
    || id == t_gt_real
    || id == t_ge_real
  then
    Ident.string id
  else (eprintf "%a@." Ident.print id; assert false)





(**given a list of symbols associated 
   to a number n, this recursive function updates the 
   SymbolContainer and the EquivClass according to 
   the presence of this symbols in other classes
   @param symbolsList : the symbolist associated to n
   @param n : the class number (that is the number of the formula)
   @returns Unit
**)
let rec manageSymbols symbolsList n = 
  match symbolsList  with 
      []     -> ()
    | s ::l  -> 
	(**Check wether s is already  present in the table **)
	let m = SymbolContainer.getClassNumberOfSymbol s n in 
	begin 
	  if m = n then 
	    (** m is not yet present in the table of symbols 
		associate n to s and add it into the symbol container **)
	    SymbolContainer.addSymbol s n 
	      
	  else
	    (** m already exists in the symbole table; we have to merge 
		the class identified by m with 
		the class identified by n **)
	    EquivClass.merge m n 
	end ;
	(** recursive call over the reduced lsit **) 
	manageSymbols l n
	  

let managesGoal ax (hyps,concl) = 
  let n = FormulaContainer.add  ax in
  (* Retrieve the list symbolList of symbols in hyps *)
  let rec managesHypotheses = function
    | [] -> SymbolContainer.predicativeSymbolsCollect  concl
    | Svar (id, v) :: q ->  managesHypotheses  q 
    | Spred (_,p) :: q -> 
	SymbolContainer.StringSet.union 
	  (SymbolContainer.predicativeSymbolsCollect p) 
	  (managesHypotheses q)
  in
  let symbolList =  SymbolContainer.StringSet.elements 
    (managesHypotheses hyps) in 
  manageSymbols symbolList n ;
  (** add the formula number into the list of known goal **)
  EquivClass.addFormula n 
    
    







(** manages the  axioms
    @ax ax is the typing predicate
    @p is is the predicative part of the definition of 
    the predicate
**) 
let managesAxiom ax p =
  let n = FormulaContainer.add  ax in 
  (* Retrieve the list symbolList of symbols in such predicate
     and we add into it the symbol id *)
  let symbolList =  SymbolContainer.StringSet.elements 
    (SymbolContainer.predicativeSymbolsCollect p) in 
  manageSymbols symbolList n
    





(** manages the  definitions of prediactes
    @param id is the symbol name
    @ax ax is the typing predicate
    @(_,_,p) is is the predicative part of the definition of 
    the predicate
**) 
let managesPredicate id ax (_,p) = 
  let n = FormulaContainer.add  ax in 
  (* Retrieve the list symbolList of symbols in such predicate
     and we add into it the symbol id *)
  let symbolList =  SymbolContainer.StringSet.elements 
    (SymbolContainer.StringSet.add id (SymbolContainer.predicativeSymbolsCollect p)) in 
  manageSymbols symbolList n




(** manages the definitions of  function 
    @param id is the symbol name
    @ax ax is the typing predicate
    @(_,_,e) is is the predicative part of the definition of 
    the function
**) 
let managesFunction id ax (_,_,e) = 
  let n = FormulaContainer.add  ax in 
  (* Retrieve the list symbolList of symbols in such function
     and we add into it the symbol id *)
  let symbolList =  SymbolContainer.StringSet.elements 
    (SymbolContainer.StringSet.add id (SymbolContainer.functionalSymbolsCollect e)) in 
  manageSymbols symbolList n


(**
   such function treats the special case of typing  definition for
   new axioms or new function. The sol itroduced symbol is 
   the predicate name  or the function name 
   @param id it the symbol name 
   @ax is the complete node**)
    
let typingPredicate id ax = 
  let n = FormulaContainer.add  ax in 
  (*Retrieve the list l of symbols in such predicate *)
  let symbolList =  SymbolContainer.StringSet.elements 
    (SymbolContainer.StringSet.add 
       id 
       SymbolContainer.StringSet.empty) in 
  manageSymbols symbolList n
    
    
    
    

    
    
let launcher decl = match decl with   
  | Dlogic (loc, id, t) as ax -> typingPredicate  id ax
  | Dpredicate_def (loc, id, d) as ax -> managesPredicate id ax d.scheme_type
  | Dfunction_def (loc, id, d)  as ax -> managesFunction  id ax d.scheme_type
  | Daxiom (_, id, p) as ax         -> managesAxiom  ax p.scheme_type
  | Dgoal (_, id, s)  as ax -> managesGoal ax s.Env.scheme_type 
  | _ -> ()   

(**
   @param q is a logic_decl Queue 
   @returns the pruned theory 
**)
let reduce q     = 
  Queue.iter launcher q ;
  EquivClass.getReducedTheory ""
    

    

