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

(*i $Id: cvcl.ml,v 1.22 2004-07-20 09:55:39 filliatr Exp $ i*)

(*s CVC Lite's output *)

open Ident
open Options
open Misc
open Error
open Logic
open Vcg
open Format
open Cc
open Pp
open Ltyping
open Env
open Report

type elem = 
  | Parameter of string * cc_type
  | Logic of string * logic_type Env.scheme
  | Oblig of obligation 
  | Axiom of string * predicate Env.scheme
  | PredicateDef of string * predicate_def Env.scheme

let queue = Queue.create ()

let reset () = Queue.clear queue

let push_parameter id v = Queue.add (Parameter (id, v)) queue

let push_logic id t = Queue.add (Logic (id, t)) queue

let push_obligations = List.iter (fun o -> Queue.add (Oblig o) queue)

let push_axiom id p = Queue.add (Axiom (id, p)) queue

let push_predicate id p = Queue.add (PredicateDef (id, p)) queue

(*s Pretty print *)

let infix id =
  if id == t_lt then "<"
  else if id == t_le then "<="
  else if id == t_gt then ">"
  else if id == t_ge then ">="
  (* int cmp *)
  else if id == t_lt_int then "<"
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  (* int ops *)
  else if id == t_add_int then "+"
  else if id == t_sub_int then "-"
  else if id == t_mul_int then "*"
  else if id == t_div_int then "/"
  (* real ops *)
  else if id == t_add_real then "+"
  else if id == t_sub_real then "-"
  else if id == t_mul_real then "*"
  else if id == t_div_real then "/"
  else if id == t_lt_real then "<"
  else if id == t_le_real then "<="
  else if id == t_gt_real then ">"
  else if id == t_ge_real then ">="
  else assert false

let external_type = function
  | PTexternal _ | PTarray (PTexternal _) -> true
  | _ -> false

let underscore fmt () = fprintf fmt "_"

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "INT"
  | PTbool -> fprintf fmt "BOOLEAN"
  | PTreal -> fprintf fmt "REAL"
  | PTunit -> fprintf fmt "UNIT"
  | PTarray pt -> fprintf fmt "ARRAY INT OF %a" print_pure_type pt
  | PTvarid _ -> assert false
  | PTvar {type_val=Some pt} -> print_pure_type fmt pt
  | PTvar _ -> assert false
  | PTexternal (i,id) -> fprintf fmt "%a%a" Ident.print id instance i

and instance fmt = function
  | [] -> ()
  | ptl -> fprintf fmt "_%a" (print_list underscore print_pure_type) ptl

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%a" Ident.print id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool true) -> 
      fprintf fmt "TRUE"
  | Tconst (ConstBool false) -> 
      fprintf fmt "FALSE"
  | Tconst ConstUnit -> 
      fprintf fmt "tt" (* TODO: CORRECT? *)
  | Tconst (ConstFloat (i,f,e)) ->
      let f = if f = "0" then "" else f in
      let e = (if e = "" then 0 else int_of_string e) - String.length f in
      if e = 0 then
	fprintf fmt "%s%s" i f
      else if e > 0 then
	fprintf fmt "(%s%s * 1%s)" i f (String.make e '0')
      else
	fprintf fmt "(%s%s / 1%s)" i f (String.make (-e) '0')
  | Tderef _ -> 
      assert false
  | Tapp (id, ([_;_] as tl), _) when id == t_mod_int ->
      fprintf fmt "@[%a(%a)@]" Ident.print id print_terms tl
  | Tapp (id, [a], _) when id == t_sqrt_real || id == t_int_of_real ->
      fprintf fmt "@[%a(%a)@]" Ident.print id print_term a
  | Tapp (id, [a], _) when id == t_real_of_int ->
      fprintf fmt "@[%a@]" print_term a
  | Tapp (id, [a; b; c], _) when id == if_then_else ->
      fprintf fmt "@[(IF %a THEN@ %a ELSE@ %a)@]" 
	print_term a print_term b print_term c
  | Tapp (id, [a; b], _) when id == access ->
      fprintf fmt "@[%a[%a]@]" print_term a print_term b
  | Tapp (id, [a; b; c], _) when id == store ->
      fprintf fmt "@[(%a WITH@ [%a] := %a)@]" 
	print_term a print_term b print_term c
  | Tapp (id, [t], _) when id == t_neg_int || id == t_neg_real ->
      fprintf fmt "@[(-%a)@]" print_term t
  | Tapp (id, [a;b], _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%a %s %a)@]" print_term a (infix id) print_term b
  | Tapp (id, [], i) ->
      fprintf fmt "%a%a" Ident.print id instance i
  | Tapp (id, tl, i) ->
      fprintf fmt "@[%a%a(%a)@]" Ident.print id instance i print_terms tl

and print_terms fmt tl = 
  print_list comma print_term fmt tl

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "TRUE"
  | Pvar id when id == default_post ->
      fprintf fmt "TRUE"
  | Pfalse ->
      fprintf fmt "FALSE"
  | Pvar id -> 
      fprintf fmt "%a" Ident.print id
  | Papp (id, [t], _) when id == well_founded ->
      fprintf fmt "TRUE %% was well_founded@\n"
  | Papp (id, [a; b], _) when id == t_eq_bool ->
      fprintf fmt "@[(%a <=>@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_neq_bool ->
      fprintf fmt "@[(NOT (%a <=>@ %a))@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_eq id ->
      fprintf fmt "@[(%a =@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_neq id ->
      fprintf fmt "@[(%a /=@ %a)@]" print_term a print_term b
  | Papp (id, [a;b], _) when is_int_comparison id || is_real_comparison id ->
      fprintf fmt "@[(%a %s %a)@]" print_term a (infix id) print_term b
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[((0 <= %a) AND@ (%a < %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl, i) -> 
      fprintf fmt "@[%a%a(%a)@]" Ident.print id instance i print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(%a =>@ %a)@]" print_predicate a print_predicate b
  | Piff (a, b) ->
      fprintf fmt "@[(%a <=>@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt 
     "@[((%a=TRUE => %a) AND@ (%a=FALSE => %a))@]"
      print_term a print_predicate b print_term a print_predicate c
  | Pand (_, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(%a AND@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(%a OR@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(NOT@ %a)@]" print_predicate a
  | Forall (_,id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a:%a):@ %a)@]" 
	Ident.print id' print_pure_type t print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(EXISTS (%a:%a):@ %a)@]" 
	Ident.print id' print_pure_type t print_predicate p'
  | Pfpi _ ->
      failwith "fpi not supported with Simplify"

let cc_external_type = function
  | Cc.TTpure ty -> external_type ty
  | Cc.TTarray (Cc.TTpure (PTexternal _)) -> true
  | _ -> false

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray v -> 
      fprintf fmt "(@[ARRAY INT OF %a@])" print_cc_type v
  | TTarrow ((_,CC_var_binder t1), t2) -> 
      fprintf fmt "[%a ->@ %a]" print_cc_type t1 print_cc_type t2
  | _ -> 
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[(FORALL (%a:%a):@ %a)@]" 
	  Ident.print id print_cc_type v print_seq hyps
    | Spred (_,p) :: hyps -> 
	fprintf fmt "@[(%a =>@ %a)@]" print_predicate p print_seq hyps
  in
  print_seq fmt hyps

(* iteration over instances (function [f]) and types (function [g]) *)
module IterIT = struct

  let rec term f = function
    | Tapp (x, tl, i) -> f x i; List.iter (term f) tl
    | _ -> ()

  let rec predicate f g = function
    | Pand (_, a, b)
    | Por (a, b)
    | Piff (a, b)
    | Forallb (_, a, b)
    | Pimplies (_, a, b) -> predicate f g a; predicate f g b
    | Pif (a, b, c) -> term f a; predicate f g b; predicate f g c
    | Pnot a -> predicate f g a
    | Exists (_, _, v, p)
    | Forall (_, _, _, v, p) -> g v; predicate f g p
    | Ptrue | Pfalse | Pvar _ | Pfpi _ -> ()
    | Papp (id, tl, i) -> f id i; List.iter (term f) tl

  let predicate_def f g (bl,p) =
    List.iter (fun (_,pt) -> g pt) bl;
    predicate f g p
	
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
	
  let element f g = function
    | Parameter (_,cc) -> 
	cc_type f g cc
    | Logic (_, lt) -> 
	logic_type g lt.scheme_type
    | Oblig (_,_,s) -> 
	sequent f g s
    | Axiom (_, p) -> 
	predicate f g p.scheme_type
    | PredicateDef (_, {scheme_type=(bl,p)}) -> 
	List.iter (fun (_,pt) -> g pt) bl; predicate f g p

end

module PureType = struct

  type t = pure_type

  let rec normalize = function
    | PTvar { type_val = Some t } -> normalize t
    | PTexternal (i, id) -> PTexternal (List.map normalize i, id)
    | PTarray t -> PTarray (normalize t)
    | PTvar _ | PTvarid _ | PTint | PTbool | PTunit | PTreal as t -> t

  let equal t1 t2 = normalize t1 = normalize t2

  let hash t = Hashtbl.hash (normalize t)

end	  

module Htypes = Hashtbl.Make(PureType)

(* declaration of abstract types *)
let declared_types = Htypes.create 97
let declare_type fmt = function
  | PTexternal (i,x) as pt 
    when is_closed_pure_type pt && not (Htypes.mem declared_types pt) ->
      Htypes.add declared_types pt ();
      fprintf fmt "@[%a: TYPE;@]@\n@\n" print_pure_type pt
  | _ -> 
      ()

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
    | Pand (w, a, b) -> Pand (w, predicate s a, predicate s b)
    | Por (a, b) -> Por (predicate s a, predicate s b)
    | Piff (a, b) -> Piff (predicate s a, predicate s b)
    | Pnot a -> Pnot (predicate s a)
    | Forall (w, id, b, v, p) -> 
	Forall (w, id, b, pure_type s v, predicate s p)
    | Exists (id, b, v, p) -> 
	Exists (id, b, pure_type s v, predicate s p)
    | Forallb (w, a, b) -> Forallb (w, predicate s a, predicate s b)
    | Pfpi (t, a, b) -> Pfpi (term s t, a, b)
    | Ptrue | Pfalse | Pvar _ as p -> p

  let predicate_def s (bl,p) = 
    List.map (fun (x,pt) -> (x, pure_type s pt)) bl, predicate s p

end

(* substitution of type variables ([PTvarid]) by pure types *)
module SV = struct

  type t = (string * pure_type) list

  let equal =
    List.for_all2 (fun (x1,pt1) (x2,pt2) -> x1 = x2 && PureType.equal pt1 pt2)
      
  let hash s = 
    Hashtbl.hash (List.map (fun (x,pt) -> (x, PureType.normalize pt)) s)

  let rec pure_type s = function
    | PTvarid id as t ->
	(try List.assoc (Ident.string id) s with Not_found -> t)
    | PTvar {type_val=Some pt} ->
	pure_type s pt
    | PTexternal (l, id) ->
	PTexternal (List.map (pure_type s) l, id)
    | PTarray ta -> PTarray (pure_type s ta)
    | PTint | PTreal | PTbool | PTunit | PTvar _ as t -> t

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
    | Pimplies (_, a, b) | Pand (_, a, b) | Por (a, b) | Piff (a, b)
    | Forallb (_, a, b) -> predicate (predicate s a) b
    | Pif (a, b, c) -> predicate (predicate (term s a) b) c
    | Pnot a -> predicate s a
    | Forall (_, _, _, _, p) -> predicate s p
    | Exists (_, _, _, p) -> predicate s p
    | Pfpi (t, _, _) -> term s t
	
end

(* unification of an open instance [t1] with a closed instance [t2];
   raises [Exit] if unification fails *)
let rec unify s t1 t2 = match (t1,t2) with
  | (PTarray ta, PTarray tb) -> 
      unify s ta tb
  | (PTexternal(l1,i1), PTexternal(l2,i2)) ->
      if i1 <> i2 || List.length l1 <> List.length l2 then raise Exit;
      List.fold_left2 unify s l1 l2
  | (_, PTvar {type_val=None})
  | (_, PTvarid _) ->
      assert false
  | (_, PTvar {type_val=Some v2}) ->
      unify s t1 v2
  | (PTvar {type_val=Some v1}, _) ->
      unify s v1 t2
  | (PTvar {tag=t;type_val=None}, _) ->
      assert false
  | (PTvarid v1, _) ->
      let v1 = Ident.string v1 in
      begin
	try
	  let t1 = List.assoc v1 s in
	  if t1 <> t2 then raise Exit;
	  s
	with Not_found ->
	  (v1, t2) :: s
      end
  | PTint, PTint
  | PTbool, PTbool
  | PTreal, PTreal
  | PTunit, PTunit -> s
  | _ -> raise Exit

let unify_i = List.fold_left2 unify


let rec print_logic_type fmt = function
  | Predicate [] ->
      fprintf fmt "BOOLEAN"
  | Predicate [pt] ->
      fprintf fmt "[%a -> BOOLEAN]" print_pure_type pt
  | Predicate pl ->
      fprintf fmt "[[%a] -> BOOLEAN]" (print_list comma print_pure_type) pl
  | Function ([], pt) ->
      print_pure_type fmt pt
  | Function ([pt1], pt2) ->
      fprintf fmt "[%a -> %a]" print_pure_type pt1 print_pure_type pt2
  | Function (pl, pt) ->
      fprintf fmt "[[%a] -> %a]" 
	(print_list comma print_pure_type) pl print_pure_type pt

let print_parameter fmt id c =
  IterIT.cc_type (fun _ _ -> ()) (declare_type fmt) c;
  fprintf fmt 
    "@[%%%% Why parameter %s@]@\n" id;
  fprintf fmt 
    "@[<hov 2>%s: %a;@]@\n@\n" id print_cc_type c

(* logic symbols (functions and predicates) *)

let print_logic_instance fmt id i t =
  IterIT.logic_type (declare_type fmt) t;
  fprintf fmt "%%%% Why logic %s@\n" id;
  fprintf fmt "@[%s%a: %a;@]@\n@\n" id instance i print_logic_type t

type logic_symbol = 
  | Uninterp of logic_type scheme
  | Defined of predicate_def scheme

let logic_symbols = Hashtbl.create 97

let print_logic fmt id t = 
  if t.scheme_vars = [] then
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
    assert (Hashtbl.mem logic_symbols id);
    match Hashtbl.find logic_symbols id with
      | Uninterp t ->
	  assert (List.length t.scheme_vars = List.length i);
	  let s = List.combine t.scheme_vars i in
	  let t = SubstV.logic_type s t.scheme_type in
	  print_logic_instance fmt (Ident.string id) i t
      | Defined p ->
	  assert (List.length p.scheme_vars = List.length i);
	  let s = List.combine p.scheme_vars i in
	  let p = SubstV.predicate_def s p.scheme_type in
 	  print_predicate_def_instance fmt (Ident.string id) i p
  end

(* predicates definitions *)

and print_predicate_def_instance fmt id i ((bl,p) as d) =
  IterIT.predicate_def (declare_logic fmt) (declare_type fmt) d;
  fprintf fmt "@[%%%% Why predicate %s@]@\n" id;
  fprintf fmt "@[<hov 2>%s%a: %a =@ LAMBDA (%a):@ @[%a@];@]@\n@\n"
    id instance i
    print_logic_type (Predicate (List.map snd bl))
    (print_list comma 
       (fun fmt (x,pt) -> 
	  fprintf fmt "%a: %a" Ident.print x print_pure_type pt )) bl 
    print_predicate p

let print_predicate_def fmt id p0 =
  let (bl,_) = p0.scheme_type in
  assert (bl <> []);
  if p0.scheme_vars = [] then
    print_predicate_def_instance fmt id [] p0.scheme_type
  else 
    Hashtbl.add logic_symbols (Ident.create id) (Defined p0)

(* Axioms *)

let print_axiom_instance fmt id p =
  IterIT.predicate (declare_logic fmt) (declare_type fmt) p;
  fprintf fmt "@[%%%% Why axiom %s@]@\n" id;
  fprintf fmt "@[<hov 2>ASSERT %a;@]@\n@\n" print_predicate p

module Hsubst = Hashtbl.Make(SV)

type axiom = {
  ax_pred : predicate scheme;
  ax_symbols : Ident.set;
  ax_symbols_i : SymbolsI.elt list;
  mutable ax_symbols_instances : SymbolsI.t; (* already considered instances *)
  ax_instances : unit Hsubst.t;
}

let axioms = Hashtbl.create 97

let print_axiom fmt id p =
  if p.scheme_vars = [] then
    print_axiom_instance fmt id p.scheme_type
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
  (* second pass: if this set has not been already considered we instantiate *)
  if not (SymbolsI.subset all_ci a.ax_symbols_instances) then begin
    a.ax_symbols_instances <- all_ci;
    fixpoint := false;
    let p = a.ax_pred in
    let rec iter s = function
      | [] ->
	  if List.for_all 
	    (fun x -> List.mem_assoc x s 
	       && is_closed_pure_type (List.assoc x s)) p.scheme_vars 
	  then
	    if not (Hsubst.mem a.ax_instances s) then begin
	      Hsubst.add a.ax_instances s ();
	      let ps = SubstV.predicate s p.scheme_type in
	      print_axiom_instance fmt id ps
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
    iter [] a.ax_symbols_i
  end

let instantiate_axioms fmt = 
  fixpoint := false;
  while not !fixpoint do
    fixpoint := true;
    Hashtbl.iter (instantiate_axiom fmt) axioms;
  done

(* Obligations *)

let print_obligation fmt (loc, o, s) = 
  IterIT.sequent (declare_logic fmt) (declare_type fmt) s;
  instantiate_axioms fmt;
  fprintf fmt "@[%%%% %s, %a@]@\n" o Loc.report_obligation loc;
  fprintf fmt "@[<hov 2>QUERY %a;@]@\n@\n" print_sequent s

let print_elem fmt = function
  | Oblig o -> print_obligation fmt o
  | Axiom (id, p) -> print_axiom fmt id p
  | PredicateDef (id, p) -> print_predicate_def fmt id p
  | Logic (id, t) -> print_logic fmt id t
  | Parameter (id, t) -> print_parameter fmt id t

let prelude_done = ref false
let prelude fmt = 
  if not !prelude_done then begin
    prelude_done := true;
    fprintf fmt "
UNIT: TYPE;
tt: UNIT;
sqrt_real: [REAL -> REAL];
int_of_real: [REAL -> INT];
mod_int: [[INT, INT] -> INT];
"
  end

let predicate_of_string s =
  let st = Stream.of_string s in
  let p = Grammar.Entry.parse Parser.lexpr st in
  let env = Env.empty in
  let lenv = Env.logical_env env in
  let p = Ltyping.predicate Label.empty env lenv p in
  generalize_predicate p

(* declaring predefined symbols *)
let predefined_symbols fmt = 
  let a = PTvarid (Ident.create "a") in
  let int_array = PTarray PTint in
  List.iter 
    (fun (s,t) -> print_logic fmt s (generalize_logic_type t))
    [ "array_length", Function ([PTarray a], PTint);
      "access", Function ([PTarray a; PTint], a);
      "store", Function ([PTarray a; PTint; a], PTunit);

      "sorted_array", Predicate [int_array; PTint; PTint];
      "exchange"    , Predicate [int_array; int_array; PTint; PTint];
      "sub_permut"  , Predicate [PTint; PTint; int_array; int_array];
      "permut"      , Predicate [int_array; int_array];
      "array_le"    , Predicate [int_array; PTint; PTint; PTint];
      "array_ge"    , Predicate [int_array; PTint; PTint; PTint];
    ];
  List.iter
    (fun (s,p) -> 
       try 
	 print_axiom fmt s (predicate_of_string p)
       with e -> 
	 eprintf "error in CVC Lite prelude: %a@." explain_exception e;
	 exit 1)
    [ "array_length_store",
        "forall t:int array. forall i:int. forall v:int.
         array_length(store(t,i,v)) = array_length(t)";

      "exchange_def",
        "forall t1:int array. forall t2:int array. forall i:int. forall j:int.
         exchange(t1,t2,i,j) <-> 
         (array_length(t1) = array_length(t2) and
         t1[i] = t2[j] and t2[i] = t1[j] and
         forall k:int. (k <> i and k <> j) -> t1[k] = t2[k])";

      "permut_refl",
        "forall t:int array. permut(t,t)";
 
      "permut_sym",
        "forall t1:int array. forall t2:int array.
         permut(t1,t2) -> permut(t2,t1)";
 
      "permut_trans",
        "forall t1:int array. forall t2:int array. forall t3:int array.
         (permut(t1,t2) and permut(t2,t3)) -> permut(t1,t3)";
  
      "permut_exchange",
        "forall t:int array. forall i:int. forall j:int.
         permut(t, store(store(t,i,t[j]),j,t[i]))";

      "permut_array_length",
        "forall t1:int array. forall t2:int array.
         permut(t1,t2) -> array_length(t1) = array_length(t2)";

      "sub_permut_refl",
        "forall t:int array. forall g:int. forall d:int.
             sub_permut(g,d,t,t)";

      "sub_permut_sym",
        "forall t1:int array. forall t2:int array. forall g:int. forall d:int.
             sub_permut(g,d,t1,t2) -> sub_permut(g,d,t2,t1)";

      "sub_permut_trans",
        "forall t1:int array. forall t2:int array. forall t3:int array.
         forall g:int. forall d:int.
             sub_permut(g,d,t1,t2) -> sub_permut(g,d,t2,t3) ->
             sub_permut(g,d,t1,t3)";

      "sub_permut_exchange_1",
        "forall t:int array.
         forall g:int. forall d:int. forall i:int. forall j:int.
             (g <= i and i <= d and g <= j and j <= d) ->
             sub_permut(g,d,t,store(store(t,i,t[j]),j,t[i]))";

      "sub_permut_exchange_2",
        "forall t1:int array. forall t2:int array.
         forall g:int. forall d:int. forall i:int. forall j:int.
             (g <= i and i <= d and g <= j and j <= d and
              exchange(t1,t2,i,j)) -> sub_permut(g,d,t1,t2)";

      "sub_permut_permut",
        "forall t1:int array. forall t2:int array. forall g:int. forall d:int. 
         sub_permut(g,d,t1,t2) -> permut(t1,t2)";

      "sub_permut_array_length",
        "forall t1:int array. forall t2:int array. forall g:int. forall d:int. 
         sub_permut(g,d,t1,t2) -> array_length(t1) = array_length(t2)";

      "sorted_array_def",
        "forall t:int array. forall i:int. forall j:int.
         sorted_array(t,i,j) <->
         forall k:int. i <= k < j -> t[k] <= t[k+1]";
    ]

let output_file fwe =
  let sep = "%%%% DO NOT EDIT BELOW THIS LINE" in
  let f = fwe ^ "_why.cvc" in
  do_not_edit f
    prelude
    sep
    (fun fmt -> 
       if not no_cvcl_prelude then predefined_symbols fmt;
       Queue.iter (print_elem fmt) queue)

