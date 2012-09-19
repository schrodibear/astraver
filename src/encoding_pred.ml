(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



open Cc
open Logic
open Logic_decl

let loc = Loc.dummy_floc

let prefix = "c_"
let suffix = "_c"
let var = "x"
let tvar = "t"
let cpt = ref 0
let axiom c = c ^ "_to_" ^ (c^suffix)
let def c = "def_"^c

(* The unique type for all terms *)
let ut = PTexternal ([], Ident.create (prefix^"unique"))

let unify ptl = List.map (fun _ -> ut) ptl
    
let prelude =
  (Dtype (loc, Ident.create (prefix^"unique"), []))::	(* The unique sort *)
  (Dlogic (loc, Ident.create (prefix^"sort"),
	   Env.empty_scheme (Predicate ([ut; ut]))))::	(* The "sort" predicate*)
  (Dlogic (loc, Ident.create (prefix^"int"),
	   Env.empty_scheme (Function ([], ut)))):: (* One synbol for each prefedined type *)
  (Dlogic (loc, Ident.create (prefix^"bool"),
	   Env.empty_scheme (Function ([], ut))))::
  (Dlogic (loc, Ident.create (prefix^"real"),
	   Env.empty_scheme (Function ([], ut))))::
  (Dlogic (loc, Ident.create (prefix^"unit"),
	   Env.empty_scheme (Function ([], ut))))::
  []
    
(* Function that creates the predicate sort(pt,term) *)
(* Uses an assoc. list of tags -> idents for type variables *)
let plunge fv term pt =
  let rec leftt pt =
    match pt with
      PTint -> Tapp (Ident.create (prefix^"int"), [], [])
    | PTbool -> Tapp (Ident.create (prefix^"bool"), [], [])
    | PTreal -> Tapp (Ident.create (prefix^"real"), [], [])
    | PTunit -> Tapp (Ident.create (prefix^"unit"), [], [])
    | PTvar ({type_val = None} as var) -> 
	let t = try (List.assoc var.tag fv) 
	with _ -> 
	  let s = string_of_int var.tag in 
	  (print_endline ("unknown vartype : "^s); s)
	in
	Tvar (Ident.create t)
    | PTvar {type_val = Some pt} -> leftt pt
    | PTexternal (ptl, id) -> Tapp (id, List.map (fun pt -> leftt pt) ptl, [])
  in
  Papp (Ident.create (prefix^"sort"), [leftt pt; term], [])

(* Generalizing a predicate scheme with foralls (can add a trigger) *)
let rec lifted  l p t =
  match l with [] -> p
  | a::[] -> Forall(false, a, a, ut, t, p)
  | a::q -> Forall(false, a, a, ut, [], lifted q p t)

(* The core *)

let queue = Queue.create ()

let reset () = 
  Queue.clear queue
      
let rec push d = 
  match d with
(* A type declaration is translated as new logical function, the arity of *)
(* which depends on the number of type variables in the declaration *)
  | Dtype (loc, ident, vars) ->
      Queue.add (Dlogic (loc, ident, 
			 Env.empty_scheme (Function (unify vars, ut)))) queue
  | Dalgtype _ ->
      assert false
(*
      failwith "encoding rec: algebraic types are not supported"
*)
(* In the case of a declaration of a function or predicate symbol, the symbol *)
(* is redefined with 'unified' arity, and in the case of a function, an axiom *)
(* is added to type the result w.r.t the arguments *)
  | Dlogic (loc, ident, arity) -> 
      let cpt = ref 0 in
      let fv = Env.Vset.fold
	  (fun tv acc -> cpt := !cpt + 1; (tv.tag, tvar^(string_of_int !cpt))::acc)
	  (arity.Env.scheme_vars) [] in
      let name = Ident.string ident in
      (match arity.Env.scheme_type with 
      | Predicate ptl ->
	  Queue.add (Dlogic (loc, ident,
			     Env.empty_scheme (Predicate (unify ptl)))) queue
      | Function (ptl, rt) -> 
	  let args = 
	    List.map
	      (fun t -> 
		Ident.create (let _ = cpt := !cpt + 1 in var^(string_of_int !cpt)), t)
	      ptl in
	  let rec mult_conjunct l p =
	    match l with [] -> p
	    | a::q -> mult_conjunct q (Pand(false, false, a, p)) in
	  let prem = 
	    mult_conjunct (List.map (fun (id,t) -> plunge fv (Tvar id) t) args) Ptrue in
	  let pattern = (Tapp (ident, List.map (fun (t, _) -> Tvar t) args, [])) in
	  let ccl = plunge fv pattern rt in
	  let ax = Env.empty_scheme 
	      (lifted 
		 ((fst (List.split args))@(List.map (fun i -> Ident.create i) (snd (List.split fv))))
		 (Pimplies (false, prem, ccl)) []) in
	  (Queue.add (Dlogic (loc, ident,
			      Env.empty_scheme (Function (unify ptl, ut)))) queue;
	   Queue.add (Daxiom (loc, axiom name, ax)) queue))
(* A predicate definition can be handled as a predicate logic definition + an axiom *)
  | Dpredicate_def (_loc, _ident, _pred_def_sch) ->
      assert false
(*
      let p = pred_def_sch.Env.scheme_type in
      let rec lifted_t l p =
	match l with 
	  | [] -> p
	  | (a,t)::q -> lifted_t q (Forall(false, a, a, t, [], p)) 
      in
      let name = Ident.string ident in
      push (Dlogic (loc, ident,
		    (Env.generalize_logic_type 
		       (Predicate (snd (List.split (fst p)))))));
      push (Daxiom (loc, def name,
		    (Env.generalize_predicate
		       (lifted_t (fst p)
			  (Piff ((Papp (ident, 
					List.map (fun (i,_) -> Tvar i) (fst p),
					[])),
			         (snd p)))))))
*)
  | Dinductive_def(_loc, _ident, _inddef) ->
      assert false
(*
      failwith "encoding rec: inductive def not yet supported"
*)
(* A function definition can be handled as a function logic definition + an axiom *)
  | Dfunction_def (_loc, _ident, _fun_def_sch) ->
      assert false
(*
      let f = fun_def_sch.Env.scheme_type in
      let rec lifted_t l p =
	match l with 
	  | [] -> p
	  | (a,t)::q -> lifted_t q (Forall(false, a, a, t, [], p)) 
      in
      let (ptl, rt, t) = f in
      let name = Ident.string ident in
      push (Dlogic (loc, ident,
		    (Env.generalize_logic_type 
		       (Function (snd (List.split ptl), rt)))));
      push (Daxiom (loc, def name,
		    (Env.generalize_predicate
		       (lifted_t ptl
			  (Papp (Ident.t_eq,
				 [(Tapp (ident, 
					 List.map (fun (i,_) -> Tvar i) ptl,
					 []));
				  t], []))))))
*)
(* Goals and axioms are just translated straightworfardly *)
  | Daxiom (loc, name, pred_sch) ->
      let cpt = ref 0 in
      let fv = Env.Vset.fold
	  (fun tv acc -> cpt := !cpt + 1; (tv.tag, tvar^(string_of_int !cpt))::acc)
	  (pred_sch.Env.scheme_vars) [] in
      let rec translate_eq = function
	| Pimplies (iswp, p1, p2) ->
	    Pimplies (iswp, translate_eq p1, translate_eq p2)
	| Pif (t, p1, p2) ->
	    Pif (t, translate_eq p1, translate_eq p2)
	| Pand (iswp, issym, p1, p2) ->
	    Pand (iswp, issym, translate_eq p1, translate_eq p2)
	| Por (p1, p2) ->
	    Por (translate_eq p1, translate_eq p2)
	| Piff (p1, p2) ->
	    Piff (translate_eq p1, translate_eq p2)
	| Pnot p ->
	    Pnot (translate_eq p)
	| Forall (iswp, id, n, pt, tl, p) ->
	    Forall (iswp, id, n, ut, tl,
		    Pimplies(false, plunge fv (Tvar n) pt, translate_eq p))
	| Plet (id, n, pt, t, p) -> 
	    Plet (id, n, pt, t, 
		  Pimplies(false, plunge fv (Tvar n) pt, translate_eq p)) 
	| Forallb (iswp, p1, p2) ->
	    Forallb (iswp, translate_eq p1, translate_eq p2)
	| Exists (id, n, pt, p) ->
	    Exists (id, n, ut, Pand (false, false, plunge fv (Tvar n) pt, translate_eq p))
	| Pnamed (s, p) ->
	    Pnamed (s, translate_eq p)
	| p -> p in
      let rec lifted  l p =
	match l with [] -> p
	| (_,a)::q -> 
	    lifted q (Forall(false, Ident.create a, Ident.create a, ut, [], p))
      in
      Queue.add (Daxiom (loc, name,
			 Env.empty_scheme
 			   (lifted fv (translate_eq pred_sch.Env.scheme_type)))) queue
  | Dgoal (loc, is_lemma, expl, name, s_sch) ->
      let cpt = ref 0 in
      let (cel, pred) = s_sch.Env.scheme_type in
      let fv = Env.Vset.fold
	  (fun tv acc -> cpt := !cpt + 1; (tv.tag, tvar^(string_of_int !cpt))::acc)
	  (s_sch.Env.scheme_vars) [] in
      let rec translate_eq = function
	| Pimplies (iswp, p1, p2) ->
	    Pimplies (iswp, translate_eq p1, translate_eq p2)
	| Pif (t, p1, p2) ->
	    Pif (t, translate_eq p1, translate_eq p2)
	| Pand (iswp, issym, p1, p2) ->
	    Pand (iswp, issym, translate_eq p1, translate_eq p2)
	| Por (p1, p2) ->
	    Por (translate_eq p1, translate_eq p2)
	| Piff (p1, p2) ->
	    Piff (translate_eq p1, translate_eq p2)
	| Pnot p ->
	    Pnot (translate_eq p)
	| Forall (iswp, id, n, pt, tl, p) ->
	    Forall (iswp, id, n, ut, tl,
		    Pimplies(false, plunge fv (Tvar n) pt, translate_eq p))
	| Plet (id, n, pt, t, p) -> 
	    Plet (id, n, pt, t, 
		  Pimplies(false, plunge fv (Tvar n) pt, translate_eq p)) 
	| Forallb (iswp, p1, p2) ->
	    Forallb (iswp, translate_eq p1, translate_eq p2)
	| Exists (id, n, pt, p) ->
	    Exists (id, n, ut, Pand (false, false, plunge fv (Tvar n) pt, translate_eq p))
	| Pnamed (s, p) ->
	    Pnamed (s, translate_eq p) 
	| p -> p in
(* dead code
      let rec lifted  l p =
	match l with [] -> p
	| (_,a)::q -> 
	    lifted q (Forall(false, Ident.create a, Ident.create a, ut, [], p))
      in 
*)
      Queue.add (Dgoal
		   (loc, is_lemma, expl, name,
		    Env.empty_scheme
		      (List.map
			 (fun s -> match s with
			   Spred (id, p) -> Spred (id, translate_eq p)
			 | s -> s) cel,
		       translate_eq pred))) queue
	
let iter f =
  (* first the prelude *)
  List.iter f prelude;
  (* then the queue *)
  Queue.iter f queue
