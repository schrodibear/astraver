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

(*i $Id: hypotheses_filtering.ml,v 1.4 2007-03-06 08:17:10 couchot Exp $ i*)

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
open Util

let threshold = Options.pruning_hyp

let symbol_counter = ref 0



(*module Int_set = Set.Make(struct type t=int let compare= compare end)*)

module String_set = Set.Make(struct type t=string let compare= compare end)

module Term_set = Set.Make(struct type t=Logic.term let compare= compare end)

let equality_container :(string, 'a) Hashtbl.t = Hashtbl.create 20

let symbs : (predicate,'a) Hashtbl.t = Hashtbl.create 20

let class_of_hyp : (predicate,string) Hashtbl.t = Hashtbl.create 20

(** the union find module for using classes **)
module UnionFindString = Unionfind.Make (struct 
					  type t = string let 
					      hash = Hashtbl.hash 
							  let compare = compare 
							  let equal = (=) 
					 end)





module  Symbol_container = 
struct 
  
  let global = ref 0
  let m :(string, int) Hashtbl.t = Hashtbl.create 20
  let vars_partition : UnionFindString.t = UnionFindString.init()  

  let add symb = 
    global := !global +1 ;
    try
      let n = Hashtbl.find m (Ident.string symb) in
      Hashtbl.replace m (Ident.string symb) (n+1)
    with
	Not_found ->
	  Hashtbl.add m (Ident.string symb) 1 
	    



  let merge_variables v = 
    let elt = String_set.choose v in 
    String_set.iter
      (fun v1 -> UnionFindString.union v1 elt  vars_partition)
      v ;
    UnionFindString.find elt vars_partition
	    
  let find_rep r = 
    UnionFindString.find r vars_partition
	  

  let reset () = 
    Hashtbl.clear m ;
    Hashtbl.clear equality_container;
    (* for variable variant *)
    Hashtbl.clear class_of_hyp;
    vars_partition = UnionFindString.init()


  let display () =
    Hashtbl.iter
      (fun str n -> 
	 Format.printf "%s : %d " str n)
      m;
    Format.printf "@\n@."
      
  let oposite_freq symb = 
    try 
      let n = Hashtbl.find m symb in
      !global - n 
    with Not_found -> 
      0
    
end


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
	  Symbol_container.add  id ;
	  funcs := String_set.add (Ident.string id) !funcs ;
	  List.iter collect tl 
      | Tvar (id) ->
	  if not (String_set.mem (Ident.string id) qvars) 
	  then
	    if 	String.compare (Ident.string id) "alloc" <> 0 then 
	      begin
		Symbol_container.add  id;
		vars := String_set.add (Ident.string id) !vars 
	      end
  in
  collect t ; 
  (!vars,!preds,!funcs)


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
	  Symbol_container.add  id ;
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




let stores_equality f  =
  let rec collect formula  = 
    match formula with 
	(* awaited equality *)
      | Papp (id, [a;b] , _) when is_eq id ->
	  begin 
	    let add_equal_term id t =
	      try 
		let s = Hashtbl.find equality_container (Ident.string id) in
		Hashtbl.replace 
		  equality_container (Ident.string id) (Term_set.add t s)
	      with Not_found -> 
		Hashtbl.add equality_container (Ident.string id) 
		  (Term_set.singleton t) in
	    match (a,b) with 
		(Tvar i, Tvar j)
		  ->
		    add_equal_term i (Tvar j) ;
		    add_equal_term j (Tvar i) 
	      | (Tvar i, j)  ->
		  add_equal_term i j 
	      | (j, Tvar i)  ->
		  add_equal_term i j 
	      | _ -> ()
	  end
      | Papp (id, tl, _)  -> ()
      | Pand (_, _, a, b) | Forallb (_, a, b)  | Por (a, b) | Piff (a, b) | 
	    Pimplies (_, a, b) ->
	  collect a;
	      collect  b
      | Pif (_, b, c) ->
	  collect  b;
	  collect  c
      | Pnot a ->
	  collect  a;
      | Forall (_,id,_,_,_,p) | Exists (id,_,_,p) ->    
	  (*let n= Symbol_container.add (Ident.string id) in 
	  vars := String_set.add n !vars ;*)
	  (*collect (String_set.add (Ident.string id) qvars) p*)
	  ()
      | Pfpi _ ->
	  failwith "fpi not yet suported "
      | Pnamed (_, p) -> (* TODO: print name *)
	  collect p 
      | Pvar _ | Pfalse |Ptrue -> ()
  in
  collect  f  


let add_symbols (v,p,f)  =
  let tv = ref String_set.empty in 
  let v' = ref String_set.empty in
  let p' = ref String_set.empty in
  let f' = ref String_set.empty in

  let rec collect e =    
    if String_set.mem e !tv  then 
      ()
    else
      begin
	tv := String_set.add e !tv;
	try 
	  let s = Hashtbl.find equality_container e  in
	  Term_set.iter (fun t -> 
			     let (vp,pp,fp) = f_symbols String_set.empty t in
			     String_set.iter collect vp ; 
			     v' := String_set.union !v' vp;
			     p' := String_set.union !p' pp;
			     f' := String_set.union !f' fp) s
	with Not_found ->
	  ()
      end in
  String_set.iter 
    (fun t-> collect t) v ; 
  (String_set.union !v' v,String_set.union !p' p, String_set.union !f' f)


let display_hash k s  = 
  Format.printf " %s : "  k ;
  Term_set.iter (fun t-> Format.printf "%a " Util.print_term t) s ;
  Format.printf "@\n@."  


let display_symb_of set =
  String_set.iter (fun s -> Format.printf "%s " s) set ;
  Format.printf "@\n@." 

let display str set  = 
  (*if debug then begin *)
    Format.printf "%s : " str ;
    display_symb_of set; 
    Format.printf "@\n@." 
  (*end*)

let memorizes_hyp_symb l = 
  Hashtbl.clear symbs ;
  let rec mem   = function  
    | [] ->  ()
    | Svar (id, v) :: q ->  mem  q 
    | Spred (_,p) :: q -> 
	let (v',p',f') = symbols p in 
	Hashtbl.add symbs  p (v',p',f');
	let rep = Symbol_container.merge_variables v' in 
	display_symb_of v' ;
	Hashtbl.add class_of_hyp p rep;
	mem  q    in 
  mem l 
  

    


let rank0 hyp_symbs goal_symbs = 
  let r = 
    if String_set.is_empty goal_symbs  then 1. else
      (float_of_int (String_set.cardinal (String_set.inter hyp_symbs goal_symbs))) /.
	(float_of_int (String_set.cardinal hyp_symbs )) in 
  r


let rank hyp_symbs goal_symbs = 
  let r = 
    if String_set.is_empty goal_symbs  then 1. else
      (float_of_int (String_set.cardinal (String_set.inter hyp_symbs goal_symbs))) /.
	(float_of_int (String_set.cardinal (String_set.union hyp_symbs goal_symbs))) in 
  r


let rank1 hyp_symbs goal_symbs = 
  if String_set.is_empty goal_symbs  then 1. else
    begin
      let op_freq_of_set s = String_set.fold 
	(fun elt n -> n + Symbol_container.oposite_freq elt)
	s 0 in 
      let upS = String_set.inter hyp_symbs goal_symbs in 
      let upf = op_freq_of_set upS in 
      let downf = op_freq_of_set hyp_symbs  in
      (float_of_int upf) /. (float_of_int downf)
    end


let filter l goal_symbs=
    let rec check = function  
    | [] -> []
    | Svar (id, v) :: q -> Svar (id, v) ::check q 
    | Spred (t,p) :: q -> 
	let (v',p',f') = 
	  try Hashtbl.find symbs p with Not_found -> raise Exit in
	let hyp_symbs = 
	  String_set.union v' (String_set.union p' f') in
	if rank1 hyp_symbs goal_symbs >= threshold then 
	  Spred (t,p):: check q  
	else
	  check q in  
    check l


let filter_acc_variables l concl_rep=
  let rec check = function  
    | [] -> []
    | Svar (id, v) :: q -> Svar (id, v) ::check q 
    | Spred (t,p) :: q -> 
	let rep' = 
	  try Hashtbl.find class_of_hyp p with Not_found -> raise Exit in
	if (Symbol_container.find_rep rep' 
	    = Symbol_container.find_rep concl_rep) then 
	  Spred (t,p):: check q  
	else
	  check q in  
    check l




let managesGoal id ax (hyps,concl) =
  match ax with 
    Dgoal(loc,id,s) -> 
      let (v,p,f) = symbols concl in 
      memorizes_hyp_symb hyps;

      
      (* variant with all symbols *)
      (*
      let rec get_equality = function
	| [] -> ()
	| Svar (id, v) :: q ->  get_equality q 
	| Spred (_,p) :: q -> 
	    stores_equality p ;
	    get_equality q in  
      get_equality hyps ;
      let (v,p,f) = add_symbols (v,p,f) in 
      let goal_symbs = String_set.union v (String_set.union p f) in
      let l' = filter hyps goal_symbs in  
      Dgoal (loc,id, Env.empty_scheme (l',concl))
      *)
      (* variant considering variables *)
      let var_concl_rep = Symbol_container.merge_variables v in 
      let l' = filter_acc_variables hyps var_concl_rep in  
      Dgoal (loc,id, Env.empty_scheme (l',concl))
      
      


    | _ -> ax 



let reduce q = 
  Symbol_container.reset();  
  let q' = 
    match q with 
	Dgoal (loc, id, s)  as ax -> 
	  let (l,g) = s.Env.scheme_type in
	  let (l',g') = Util.intros [] g in   
	  managesGoal id ax (List.append l l',g')
      | _ -> failwith "goal awaited"
  in
  q' 
  
  

  
