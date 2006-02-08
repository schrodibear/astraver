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

(*i $Id: monomorph.ml,v 1.9 2006-02-08 07:16:01 filliatr Exp $ i*)

(* monomorphic output *)

open Ident
open Misc
open Logic
open Cc
open Vcg
open Env
open Format

module type S = sig
  val declare_type : formatter -> pure_type -> unit
  val print_parameter : formatter -> string -> cc_type -> unit
  val print_logic_instance : 
    formatter -> string -> instance -> logic_type -> unit
  val print_predicate_def_instance : 
    formatter -> string -> instance -> predicate_def -> unit
  val print_function_def_instance : 
    formatter -> string -> instance -> function_def -> unit
  val print_axiom_instance :
    formatter -> string -> instance -> predicate -> unit
  val print_obligation : formatter -> obligation -> unit
end

(* iteration over instances (function [f]) and types (function [g]) *)
module IterIT = struct

  let rec term f = function
    | Tapp (x, tl, i) -> f x i; List.iter (term f) tl
    | _ -> ()

  let rec predicate f g = function
    | Pand (_, _, a, b)
    | Por (a, b)
    | Piff (a, b)
    | Forallb (_, a, b)
    | Pimplies (_, a, b) -> predicate f g a; predicate f g b
    | Pif (a, b, c) -> term f a; predicate f g b; predicate f g c
    | Pnot a -> predicate f g a
    | Exists (_, _, v, p)
    | Forall (_, _, _, v, p) -> g v; predicate f g p
    | Pnamed (_, a) -> predicate f g a
    | Ptrue | Pfalse | Pvar _ | Pfpi _ -> ()
    | Papp (id, tl, i) -> f id i; List.iter (term f) tl

  let predicate_def f g (bl,p) =
    List.iter (fun (_,pt) -> g pt) bl;
    predicate f g p

  let function_def f g (bl,t,e) =
    List.iter (fun (_,pt) -> g pt) bl;
    g t;
    term f e
	
  let logic_type g = function
    | Function (l, pt) -> List.iter g l; g pt
    | Predicate l -> List.iter g l

  let rec cc_type f g = function
    | TTpure pt -> g pt
    | TTarray cc -> cc_type f g cc
    | TTarrow (b, cc)
    | TTlambda (b, cc) -> cc_binder f g b; cc_type f g cc
    | TTtuple (bl, ccopt) -> 
	List.iter (cc_binder f g) bl; 
	option_iter (cc_type f g) ccopt
    | TTpred p ->
	predicate f g p
    | TTapp (cc, ccl) ->
	cc_type f g cc; List.iter (cc_type f g) ccl
    | TTterm t ->
	term f t
    | TTSet ->
	()
	
  and cc_binder f g = function
    | _, CC_var_binder cc -> cc_type f g cc
    | _, CC_pred_binder p -> predicate f g p
    | _, CC_untyped_binder -> ()

  let sequent f g (ctx,p) =
    List.iter 
      (function 
	 | Svar (_,cc) -> cc_type f g cc | Spred (_,p) -> predicate f g p)
      ctx;
    predicate f g p
	
end

module PureType = struct

  type t = pure_type

  let rec normalize = function
    | PTvar { type_val = Some t } -> normalize t
    | PTexternal (i, id) -> PTexternal (List.map normalize i, id)
    | PTvar _ | PTint | PTbool | PTunit | PTreal as t -> t

  let equal t1 t2 = normalize t1 = normalize t2

  let hash t = Hashtbl.hash (normalize t)

end	  

module Htypes = Hashtbl.Make(PureType)


(* generic substitution parameterized by a substitution over [pure_type] *)
module type Substitution = sig
  type t
  val pure_type : t -> pure_type -> pure_type
end

module GenSubst(S : Substitution) = struct

  include S

  let logic_type s = function
    | Function (tl, tr) -> 
	Function (List.map (pure_type s) tl, pure_type s tr)
    | Predicate tl -> 
	Predicate (List.map (pure_type s) tl)

  let binder s (id,pt) = (id, pure_type s pt)

  let binders s = List.map (binder s)

  let rec term s = function
    | Tapp (x, tl, i) -> 
	Tapp (x, List.map (term s) tl, List.map (pure_type s) i)
    | t -> 
	t

  let rec predicate s = function
    | Papp (x, tl, i) ->
	Papp (x, List.map (term s) tl, List.map (pure_type s) i)
    | Pimplies (w, a, b) -> Pimplies (w, predicate s a, predicate s b)
    | Pif (a, b, c) -> Pif (a, predicate s b, predicate s c)
    | Pand (w, sym, a, b) -> Pand (w, sym, predicate s a, predicate s b)
    | Por (a, b) -> Por (predicate s a, predicate s b)
    | Piff (a, b) -> Piff (predicate s a, predicate s b)
    | Pnot a -> Pnot (predicate s a)
    | Forall (w, id, b, v, p) -> 
	Forall (w, id, b, pure_type s v, predicate s p)
    | Exists (id, b, v, p) -> 
	Exists (id, b, pure_type s v, predicate s p)
    | Forallb (w, a, b) -> Forallb (w, predicate s a, predicate s b)
    | Pfpi (t, a, b) -> Pfpi (term s t, a, b)
    | Pnamed (n, a) -> Pnamed (n, predicate s a)
    | Ptrue | Pfalse | Pvar _ as p -> p

  let predicate_def s (bl,p) = 
    List.map (fun (x,pt) -> (x, pure_type s pt)) bl, predicate s p

  let function_def s (bl,t,e) = 
    List.map (fun (x,pt) -> (x, pure_type s pt)) bl, 
    pure_type s t,
    term s e

end

(* substitution of type variables ([PTvarid]) by pure types *)
module SV = struct

  type t = pure_type Vmap.t

  let list_of s = 
    Vmap.fold (fun x pt acc -> (x, PureType.normalize pt)::acc) s []

  let equal s1 s2 = list_of s1 = list_of s2
      
  let hash s = Hashtbl.hash (list_of s)

  let rec pure_type s = function
    | PTvar ({type_val = None} as v) ->
	(try Vmap.find v s with Not_found -> assert false (*t?*))
    | PTvar {type_val = Some pt} ->
	pure_type s pt
    | PTexternal (l, id) ->
	PTexternal (List.map (pure_type s) l, id)
    | PTint | PTreal | PTbool | PTunit as t -> t

end
module SubstV = GenSubst(SV)

(* sets of symbols instances *)
module Instance = struct 
  type t = Ident.t * pure_type list 
  let normalize (id, i) = (id, List.map PureType.normalize i)
  let equal (id1, i1) (id2, i2) = id1=id2 && List.for_all2 PureType.equal i1 i2
  let hash i = Hashtbl.hash (normalize i)
  let compare (id1, i1) (id2, i2) = 
    let c = compare id1 id2 in
    if c <> 0 then 
      c 
    else 
      compare (List.map PureType.normalize i1) (List.map PureType.normalize i2)
end

module SymbolsI = Set.Make(Instance)

(* the following module collects instances (within [Tapp] and [Papp]) *)
module OpenInstances = struct

  module S = SymbolsI

  let add ((_,i) as e) s =
    let is_open pt = not (is_closed_pure_type pt) in
    if List.exists is_open i then S.add e s else s

  let rec term s = function
    | Tvar _ | Tderef _ | Tconst _ -> s
    | Tapp (id, l, i) -> List.fold_left term (add (id,i) s) l
	
  let rec predicate s = function
    | Pvar _ | Ptrue | Pfalse -> s
    | Papp (id, l, i) -> List.fold_left term (add (id,i) s) l
    | Pimplies (_, a, b) | Pand (_, _, a, b) | Por (a, b) | Piff (a, b)
    | Forallb (_, a, b) -> predicate (predicate s a) b
    | Pif (a, b, c) -> predicate (predicate (term s a) b) c
    | Pnot a -> predicate s a
    | Forall (_, _, _, _, p) -> predicate s p
    | Exists (_, _, _, p) -> predicate s p
    | Pnamed (_, p) -> predicate s p
    | Pfpi (t, _, _) -> term s t
	
end

(* unification of an open instance [t1] with a closed instance [t2];
   raises [Exit] if unification fails *)
let rec unify s t1 t2 = match (t1,t2) with
  | (PTexternal(l1,i1), PTexternal(l2,i2)) ->
      if i1 <> i2 || List.length l1 <> List.length l2 then raise Exit;
      List.fold_left2 unify s l1 l2
  | (_, PTvar {type_val=None}) ->
      unify s t2 t1
  | (_, PTvar {type_val=Some v2}) ->
      unify s t1 v2
  | (PTvar {type_val=Some v1}, _) ->
      unify s v1 t2
  | (PTvar ({type_val=None} as v1), _) ->
      begin
	try
	  let t1 = Vmap.find v1 s in
	  if t1 <> t2 then raise Exit;
	  s
	with Not_found ->
	  Vmap.add v1 t2 s
      end
  | PTint, PTint
  | PTbool, PTbool
  | PTreal, PTreal
  | PTunit, PTunit -> s
  | _ -> raise Exit

let unify_i = List.fold_left2 unify



module Make(X : S) = struct

  (* declaration of abstract types *)
  let declared_types = Htypes.create 97
  let declare_type fmt = function
    | PTexternal (i,x) as pt 
	when is_closed_pure_type pt && not (Htypes.mem declared_types pt) ->
	Htypes.add declared_types pt ();
	X.declare_type fmt pt
    | _ -> 
	()

  let print_parameter fmt id c =
    IterIT.cc_type (fun _ _ -> ()) (declare_type fmt) c;
    X.print_parameter fmt id c

  let print_logic_instance fmt id i t =
    IterIT.logic_type (declare_type fmt) t;
    X.print_logic_instance fmt id i t

  (* logic symbols (functions and predicates) *)

  type logic_symbol = 
    | Uninterp of logic_type scheme
    | PredicateDef of predicate_def scheme
    | FunctionDef of function_def scheme
	
  let logic_symbols = Hashtbl.create 97
			
  let print_logic fmt id t = 
    (*eprintf "print_logic %s@." id;*)
    if Vset.is_empty t.scheme_vars then
      print_logic_instance fmt id [] t.scheme_type
    else
      (* nothing to do until we encounter closed instances of [id] *)
      (* we only remember the type of [id] *)
      Hashtbl.add logic_symbols (Ident.create id) (Uninterp t)
	
  module Hinstance = Hashtbl.Make(Instance)
  let declared_logic = Hinstance.create 97

  let rec declare_logic fmt id i =
    if i <> [] && not (Hinstance.mem declared_logic (id,i)) then begin
      Hinstance.add declared_logic (id,i) ();
      (*eprintf "declare_logic %a@." Ident.print id;*)
      assert (Hashtbl.mem logic_symbols id);
      match Hashtbl.find logic_symbols id with
	| Uninterp t ->
	    assert (Vset.cardinal t.scheme_vars = List.length i);
	    let s = 
	      List.fold_right2 Vmap.add 
		(Vset.elements t.scheme_vars) i Vmap.empty
	    in
	    let t = SubstV.logic_type s t.scheme_type in
	    print_logic_instance fmt (Ident.string id) i t
	| PredicateDef p ->
	    assert (Vset.cardinal p.scheme_vars = List.length i);
	    let s = 
	      List.fold_right2 Vmap.add 
		(Vset.elements p.scheme_vars) i Vmap.empty
	    in
	    let p = SubstV.predicate_def s p.scheme_type in
 	    print_predicate_def_instance fmt (Ident.string id) i p
	| FunctionDef p ->
	    assert (Vset.cardinal p.scheme_vars = List.length i);
	    let s = 
	      List.fold_right2 Vmap.add 
		(Vset.elements p.scheme_vars) i Vmap.empty
	    in
	    let p = SubstV.function_def s p.scheme_type in
 	    print_function_def_instance fmt (Ident.string id) i p
    end
      
  (* predicates definitions *)

  and print_predicate_def_instance fmt id i ((bl,p) as d) =
    IterIT.predicate_def (declare_logic fmt) (declare_type fmt) d;
    X.print_predicate_def_instance fmt id i d

  and print_function_def_instance fmt id i ((bl,t,e) as d) =
    IterIT.function_def (declare_logic fmt) (declare_type fmt) d;
    X.print_function_def_instance fmt id i d
      
  let print_predicate_def fmt id p0 =
    let (bl,_) = p0.scheme_type in
    assert (bl <> []);
    if Vset.is_empty p0.scheme_vars then
      print_predicate_def_instance fmt id [] p0.scheme_type
    else 
      Hashtbl.add logic_symbols (Ident.create id) (PredicateDef p0)

  let print_function_def fmt id p0 =
    let (bl,_,_) = p0.scheme_type in
    assert (bl <> []);
    if Vset.is_empty p0.scheme_vars then
      print_function_def_instance fmt id [] p0.scheme_type
    else 
      Hashtbl.add logic_symbols (Ident.create id) (FunctionDef p0)

  (* axioms *)

  let print_axiom_instance fmt id i p =
    IterIT.predicate (declare_logic fmt) (declare_type fmt) p;
    X.print_axiom_instance fmt id i p

  module Hsubst = Hashtbl.Make(SV)
		    
  type axiom = {
    ax_pred : predicate scheme;
    ax_symbols : Ident.set;
    ax_symbols_i : SymbolsI.elt list;
    mutable ax_symbols_instances : SymbolsI.t; (*already considered instances*)
    ax_instances : unit Hsubst.t;
  }
		 
  let axioms = Hashtbl.create 97
		 
  let print_axiom fmt id p =
    if Vset.is_empty p.scheme_vars then
      print_axiom_instance fmt id [] p.scheme_type
    else
      let oi = OpenInstances.predicate SymbolsI.empty p.scheme_type in
      let os = SymbolsI.fold (fun (id,_) -> Idset.add id) oi Idset.empty in
      let a = 
	{ ax_pred = p; ax_symbols_i = SymbolsI.elements oi; 
	  ax_symbols = os; ax_symbols_instances = SymbolsI.empty;
	  ax_instances = Hsubst.create 97 } 
      in
      Hashtbl.add axioms id a

  (* instantiating axioms may generate new instances, so we have to repeat it
     again until the fixpint is reached *)
	
  let fixpoint = ref false
		   
  (* instantiate a polymorphic axiom according to new symbols instances *)
  let instantiate_axiom fmt id a =
    (* first pass: we look at all (closed) instances encountered so far
       appearing in axiom [a] *)
    let all_ci = 
      Hinstance.fold
	(fun ((id,_) as i) () s -> 
	   if Idset.mem id a.ax_symbols then SymbolsI.add i s else s)
	declared_logic SymbolsI.empty
    in
    (* second pass: 
       if this set has not been already considered we instantiate *)
    if not (SymbolsI.subset all_ci a.ax_symbols_instances) then begin
      a.ax_symbols_instances <- all_ci;
      fixpoint := false;
      let p = a.ax_pred in
      let rec iter s = function
	| [] ->
	    if Vset.for_all 
	      (fun x -> 
		 try is_closed_pure_type (Vmap.find x s) 
		 with Not_found -> false)
	      p.scheme_vars 
	    then
	      if not (Hsubst.mem a.ax_instances s) then begin
		Hsubst.add a.ax_instances s ();
		let ps = SubstV.predicate s p.scheme_type in
		let i = Vmap.fold (fun _ t acc -> t :: acc) s [] in
		print_axiom_instance fmt id i ps
	      end
	| (x,oi) :: oil ->
	    SymbolsI.iter 
	      (fun (y,ci) -> 
		 if x = y then
		   try let s = unify_i s oi ci in iter s oil
		   with Exit -> ()) 
	      all_ci;
	    iter s oil
      in
      iter Vmap.empty a.ax_symbols_i
    end

  let instantiate_axioms fmt = 
    fixpoint := false;
    while not !fixpoint do
      fixpoint := true;
      Hashtbl.iter (instantiate_axiom fmt) axioms;
    done

  (* Obligations *)
    
  let print_obligation fmt ((loc, o, s) as ob) = 
    IterIT.sequent (declare_logic fmt) (declare_type fmt) s;
    instantiate_axioms fmt;
    X.print_obligation fmt ob

  let reset () =
    Htypes.clear declared_types;
    Hinstance.clear declared_logic;
    Hashtbl.clear logic_symbols;
    Hashtbl.clear axioms

end

