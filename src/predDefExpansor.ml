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
open Cc
open Logic
open Logic_decl
open Util 



let predDef = ref []
let arities = ref []

let reset()
    predDef = ref[] 

module TypeMap = Map.Make(struct type t=pure_type let compare= compare end)
module IdMap = Map.Make(struct type t=Ident.t let compare= compare end)




(* Ground instanciation of an arity (to be plunged under) *)
let instantiate_arity id inst =
  let arity = 
    try List.assoc (Ident.string id) !arities
    with e -> (print_endline ("unknown arity :"^(Ident.string id))); raise e in
  let (vs, log_type) = Env.specialize_logic_type arity in
  match log_type with 
      Function (ptl, rt) ->
	ignore (Env.Vmap.fold 
		  (fun _ v l ->
		     (match l with [] -> [] 
			| _ -> (v.type_val <- Some (List.hd l); (List.tl l))))
		  vs (List.rev inst));
	rt
    | _ -> assert false

	




let rec  genSubst ty1 ty2 m = 
  match (ty1,ty2) with
      (PTint,_) -> m
    | (PTbool,_) -> m
    | (PTreal,_) -> m
    | (PTunit,_) -> m
    | (PTvar(v),t2) as c-> 
	Format.printf "Replace %a with %a \n" 
	  Util.print_pure_type (fst c)
	  Util.print_pure_type t2 ;
	TypeMap.add (fst c) t2 m 
    | (PTexternal(l,_),PTexternal(l',_))   -> 
	genSubstL l l' m
    | _ -> assert false 
 and
    genSubstL l l' m = match (l,l') with 
	([],[]) -> m
      | (t::l, t'::l') -> 
	  genSubst t t' (genSubstL l l' m)
      | _ -> assert false 
	  

let rec generateTypeSubstMap l1 l2 =  
  let typMap = 
    match (l1,l2) with 
	([],[]) ->  TypeMap.empty
      | ((k1,ty1)::l1',(k2,ty2)::l2') ->	  
	  genSubst ty1 ty2 (generateTypeSubstMap l1' l2')
      | _ -> assert false 
  in
  typMap


let rec susbtitutesTypeVarIntoPred typeSubst pred = match pred with 
    Papp(id, pl,ins) as d -> d
  | Pimplies (wp,p1,p2) -> 
      Pimplies (wp, 
		susbtitutesTypeVarIntoPred typeSubst p1, 
		susbtitutesTypeVarIntoPred typeSubst p2)
  | Pif(t,p1,p2) ->
      Pif (t, 
	   susbtitutesTypeVarIntoPred typeSubst p1, 
	   susbtitutesTypeVarIntoPred typeSubst p2)
  | Pand (wp, is_sym, p1, p2) -> 
      Pand (wp,
	    is_sym,
	    susbtitutesTypeVarIntoPred typeSubst p1, 
	    susbtitutesTypeVarIntoPred typeSubst p2)
  | Por (p1, p2) -> 
      Por ( susbtitutesTypeVarIntoPred typeSubst p1, 
	    susbtitutesTypeVarIntoPred typeSubst p2)
  | Piff (p1, p2) -> 
      Piff (susbtitutesTypeVarIntoPred typeSubst p1, 
	    susbtitutesTypeVarIntoPred typeSubst p2)
  | Pnot (p1) -> 
      Pnot (susbtitutesTypeVarIntoPred typeSubst p1) 
  | Forall(is_wp,t1,t2,pt,tr,predicate) ->
      Forall(is_wp,t1,t2,
	     (try (TypeMap.find pt typeSubst ) with Not_found -> pt),
	     tr, 
	     susbtitutesTypeVarIntoPred typeSubst predicate) 
  | Forallb(is_wp,pr1, pr2) ->
      Forallb(is_wp,susbtitutesTypeVarIntoPred typeSubst pr1,susbtitutesTypeVarIntoPred typeSubst pr2) 
  | Exists(t1,t2,pt,predicate) ->
      Exists(t1,t2,
	     (try (TypeMap.find pt typeSubst ) with Not_found -> pt),
	     susbtitutesTypeVarIntoPred typeSubst predicate) 
  | Pnamed(str,p)->
      Pnamed(str,susbtitutesTypeVarIntoPred typeSubst p)
  | p -> p

(**
   @param pl is a list of term
   @identType= is an list that associates a type to each ident
   @return a map that associates to each term its type
**)
let rec getTypesOf pl identType = match pl with 
    [] -> []
  | t :: l' -> let ty = 
      (*Format.printf "Term : %a ; " Util.print_term t;*)
      match t with 
	| Tconst(ConstInt(_)) -> PTint
	| Tconst(ConstBool(_)) -> PTbool
	| Tconst(ConstUnit) -> PTunit
	| Tconst(ConstFloat(_)) -> PTreal
	| Tvar(v) -> begin
	    try (List.assoc v identType)
	    with _ -> assert false 
	  end
	| Tderef(r) -> begin
	    try (List.assoc r identType)
	    with _ -> assert false 
	  end
	| Tapp(id,[],_) -> begin  
	    try (List.assoc id identType)
	    with _ -> assert false   
	  end
	| Tapp(id,_,_) when Ident.is_int_arith id -> PTint
	| Tapp(id,l,inst) -> 
	    let rt = instantiate_arity id inst in       
	    match rt with 
		PTvar { type_val = Some t } -> t
	      | rt -> rt 
	  
    in 
     (t,ty)::(getTypesOf l' identType)
       
    


let substitutesPredWithDef (ident,argl,pred) (identTypeList,e) = 
  let rec predToDef identTypeList p = 
    match p with  
	Papp(id, pl,ins)   when Ident.string id = ident ->
	  (** we need to know both 
	      - the types of each parameter of the instance, i.e. the type of
	      each element of the list of terms pl
	      - the type of each parameter of the definition : this is argl
	  **)

	  Printf.printf "%s \n" ident ; 
	  Format.printf ("old_ :  %a \n ") Util.print_predicate (Papp(id, pl,ins)); 

	  let pl' = getTypesOf pl identTypeList in 
	  let displayTermType l = 
	    List.iter (fun (t,ty) ->
			 Format.printf ("%a: %a \n") 
			   Util.print_term t 
			   Util.print_pure_type ty) l in
	  displayTermType pl';
	  
	  
	  (* creer la substitution des variables de type*)
	  let typeSubst = generateTypeSubstMap argl pl'  in 

	  
	  let argl' = List.map (fun (t,ty) -> t) argl in 
	  let subst = Misc.subst_many argl' pl in
	  let pred' = Misc.tsubst_in_predicate subst pred in
	  (* appliquer la substitution des variables de type*)
	  
	  

	  let pred'' = susbtitutesTypeVarIntoPred typeSubst pred' in

	  

	  Format.printf ("new :  %a \n ") Util.print_predicate pred''; 
	  pred''
	    
      | Pimplies (wp,p1,p2) -> 
	  Pimplies (wp, 
		    predToDef identTypeList p1, 
		    predToDef identTypeList p2)
      | Pif(t,p1,p2) ->
	  Pif (t, 
	       predToDef identTypeList p1, 
	       predToDef identTypeList p2)
      | Pand (wp, is_sym, p1, p2) -> 
	  Pand (wp,
		is_sym,
		predToDef identTypeList p1, 
		predToDef identTypeList p2)
      | Por (p1, p2) -> 
	  Por ( predToDef identTypeList p1, 
		predToDef identTypeList p2)
      | Piff (p1, p2) -> 
	  Piff (predToDef identTypeList p1, 
		predToDef identTypeList p2)
      | Pnot (p1) -> 
	  Pnot (predToDef identTypeList p1) 
      | Forall(is_wp,t1,t2,pt,tr,predicate) ->
	  Forall(is_wp,t1,t2,pt,
		 List.map (fun t -> predToDefTrig ((t2,pt)::identTypeList) t) tr, 
		 predToDef ((t2,pt)::identTypeList) predicate) 
      | Forallb(is_wp,pr1, pr2) ->
	  Forallb(is_wp,predToDef identTypeList pr1,
		  predToDef identTypeList pr2) 
      | Exists(t1,t2,pt,predicate) ->
	  Exists(t1,t2,pt,predToDef ((t2,pt)::identTypeList) predicate)
      | Pnamed(str,p)->
	  Pnamed(str,predToDef identTypeList p)
      | p -> p
	  
  and predToDefTrig identTypeList pl  = 
    match pl with 
	[] -> []
      | pat::l -> 
	  begin 
	    match pat with 
		PPat(p) -> PPat(predToDef identTypeList p) 
	      | t -> t 
	  end 
	  :: (predToDefTrig identTypeList l)
  in (identTypeList, predToDef identTypeList e)
       

let expandDef (argl,pred) = 
  List.fold_right 
    substitutesPredWithDef  
    !predDef 
    (argl,pred)


let rec push d = 
  try (match d with
	 | Dtype (loc, vars, ident) as  d -> d
	 | Dlogic (loc, ident, arity) as  d -> 
	     arities := (ident, arity)::!arities;
	     d 
	 | Dpredicate_def (loc, ident, pred_def_sch) ->
	     Printf.printf "push_Pred : %s \n" ident ; 
	     let (argl, pred) = pred_def_sch.Env.scheme_type in
	     let (_,pred') =   expandDef (argl, pred) in 
	     (*let pred_scheme = Env.generalize_predicate pred' in
	       let sch_vars = pred_scheme.Env.scheme_vars in *)
	     Format.printf ("def %a \n ") Util.print_predicate pred'; 
	     predDef := (ident,argl,pred')::!predDef ;
	     (* remove the definition predicate and return the axiom definition *)
	     Dlogic (loc, ident, (Env.generalize_logic_type (Predicate (snd (List.split argl)))))

	 | Dfunction_def (loc, ident, fun_def_sch) as  d -> d
	     (*let _ = print_endline ident in
	       let (argl, rt, term) = fun_def_sch.Env.scheme_type in
	       let rootexp = (Tapp (Ident.create ident, List.map (fun (i,_) -> Tvar i) argl, [])) in
	       push (Dlogic (loc, ident, (Env.generalize_logic_type (Function (snd (List.split argl), rt)))));
	       let pred_scheme = (Env.generalize_predicate
	       (lifted_t argl 
	       (Papp (Ident.t_eq, [rootexp; term], [])) 
	       [[TPat rootexp]])) in 
	       push (Daxiom (loc, def ident,pred_scheme))*)
	     (* Axiom definitions *)
	 | Daxiom (loc, ident, pred_sch) as d -> d
	(*     
	     (*let old_pred = pred_sch.Env.scheme_type in 
	       Format.printf ("old :  %a \n ") Util.print_predicate old_pred; *)
               let new_pred = expandDef  (pred_sch.Env.scheme_type,pred_sch.Env.scheme_vars) in 
	     (*Format.printf ("new :  %a \n ") Util.print_predicate new_pred; *)
	       let new_axiom =   Env.generalize_predicate new_pred  in
	       Daxiom (loc, ident, new_axiom) 
	     (* A goal is a sequent : a context and a predicate and both have to be translated *)
	*)
	 | Dgoal (loc, ident, s_sch) as d -> d
	     (*
	       let (ctxtL, pred)= s_sch.Env.scheme_type in
	       let newCtxtL =  List.map (fun e -> match e with 
	       Svar(i,p) as s -> s
	       | Spred (i,p) -> Spred(i, expandDef p)) ctxtL in 
	       let new_sequent =
	       Env.generalize_sequent
	       (newCtxtL,
	       expandDef pred) in
	       Dgoal (loc, ident, new_sequent) *)
      )
  with
      Not_found -> 
	Format.eprintf "Exception Caught In : %a\n" Util.print_decl d;
	raise Not_found



(******************************************************************************)
open Env
open Ident
open Misc

let pred_def = Hashtbl.create 97

let rec subst_in_pure_type st = function
  | PTvar ({ type_val = None } as v) as t ->
      (try Vmap.find v st with Not_found -> t)
  | PTvar { type_val = Some t } ->
      subst_in_pure_type st t
  | PTexternal(l, id) ->
      PTexternal(List.map (subst_in_pure_type st) l, id)
  | PTint | PTreal | PTbool | PTunit as t -> 
      t

let subst_in_instance st = List.map (subst_in_pure_type st)

let rec subst_in_term s st = function
  | Tvar x as t -> 
      (try Idmap.find x s with Not_found -> t)
  | Tapp (x,l,i) -> 
      Tapp (x, List.map (subst_in_term s st) l, subst_in_instance st i)
  | Tconst _ | Tderef _ as t -> 
      t

let rec subst_in_predicate s st = function
  | Papp (id, l, i) -> 
      Papp (id, List.map (subst_in_term s st) l, subst_in_instance st i)
  | Pif (a, b ,c) -> 
      Pif (subst_in_term s st a, 
	   subst_in_predicate s st b, 
	   subst_in_predicate s st c)
  | Pfpi (t, f1, f2) -> 
      Pfpi (subst_in_term s st t, f1, f2)
  | Forall (w, id, b, v, tl, p) -> 
      Forall (w, id, b, subst_in_pure_type st v, 
	      List.map (List.map (subst_in_pattern s st)) tl,
	      subst_in_predicate s st p)
  | Exists (id, b, v, p) ->
      Exists (id, b, subst_in_pure_type st v, subst_in_predicate s st p)
  | p -> 
      map_predicate (subst_in_predicate s st) p

and subst_in_pattern s st = function
  | TPat t -> TPat (subst_in_term s st t)
  | PPat p -> PPat (subst_in_predicate s st p)

let rec expand = function
  | Papp (id, tl, i) as p ->
      begin 
	try
	  let tvars,argl,p = Hashtbl.find pred_def (Ident.string id) in
	  let st = subst_many argl tl in
	  let sty = List.fold_left2 (fun s v t -> Vmap.add v t s) Vmap.empty tvars i in
	  subst_in_predicate st sty p
	with Not_found ->
	  p
      end
  | p -> 
      map_predicate expand p

let expand_sequent (ctx,p) =
  let expand_hyp = function
    | Svar _ as h -> h
    | Spred (id, p) -> Spred (id, expand p)
  in
  (List.map expand_hyp ctx, expand p)

let push = function
  | Dtype _ as d -> d
  | Dlogic _ as  d -> d
  | Dpredicate_def (loc, ident, def) ->
      let argl,p = def.scheme_type in
      let p = expand p in
      let vars = Vset.fold (fun v l -> v :: l) def.scheme_vars [] in
      Hashtbl.add pred_def ident (vars, List.map fst argl, p);
      Dlogic (loc, ident, Env.generalize_logic_type (Predicate (List.map snd argl)))
  | Dfunction_def _ as  d -> d
  | Daxiom (loc, ident, ps) -> 
      Daxiom (loc, ident, Env.generalize_predicate (expand ps.scheme_type))
  | Dgoal (loc, ident, ps) ->
      Dgoal (loc, ident, Env.generalize_sequent (expand_sequent ps.scheme_type))

