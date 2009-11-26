(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Env
open Ident
open Misc
open Logic 
open Cc 
open Options
open Logic_decl

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
  | Tnamed(lab,t) -> Tnamed(lab,subst_in_term s st t)

let rec subst_in_predicate s st = function
  | Papp (id, l, i) -> 
      Papp (id, List.map (subst_in_term s st) l, subst_in_instance st i)
  | Pif (a, b ,c) -> 
      Pif (subst_in_term s st a, 
	   subst_in_predicate s st b, 
	   subst_in_predicate s st c)
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
	  let tvars,argl,p = Hashtbl.find pred_def id in
	  let st = subst_many argl tl in
	  let sty = List.fold_left2 (fun s v t -> Vmap.add v t s) Vmap.empty tvars i in
	  subst_in_predicate st sty p
	with Not_found ->
	  p
      end
  | p -> 
      map_predicate expand p

let expand_inductive_def (t,l) = (t,List.map (fun (id,p) -> (id,expand p)) l)

let expand_sequent ~recursive_expand (ctx,p) =
  let expand_hyp = function
    | Svar _ as h -> h
    | Spred (id, p) -> 
	Spred (id, if recursive_expand then expand p else p)  
  in
  (List.map expand_hyp ctx, expand p)


let push ~recursive_expand decl = 
  match decl with
  | Dpredicate_def (loc, ident, def) ->
      let argl,p = def.scheme_type in
      (*let rootexp = (Papp (Ident.create ident, List.map (fun (i,_) -> Tvar i) argl, [])) in*)
      let p = expand p  in
      let vars = Vset.fold (fun v l -> v :: l) def.scheme_vars [] in
      Hashtbl.add pred_def ident (vars, List.map fst argl, p);
      if recursive_expand then 
	Dlogic (loc, ident, Env.generalize_logic_type (Predicate (List.map snd argl)))
      else
	decl
  | Dinductive_def(loc, ident, def) when recursive_expand -> 
      Dinductive_def(loc,ident,
		     Env.generalize_inductive_def 
		       (expand_inductive_def def.scheme_type))		       
  | Daxiom (loc, ident, ps) when recursive_expand -> 
      Daxiom (loc, ident, Env.generalize_predicate(expand ps.scheme_type)) 
  | Dgoal (loc, expl, ident, ps) ->
      Dgoal (loc, expl, ident, 
	     Env.generalize_sequent (expand_sequent ~recursive_expand ps.scheme_type)) 
  | Dfunction_def _ 
  | Dinductive_def _ 
  | Daxiom _
  | Dtype _ 
  | Dalgtype _
  | Dlogic _ -> decl

(***************
 function and predicate definitions
**************)

let function_def loc id d =
  let (vars,(yv,tr,e)) = Env.specialize_function_def d in
  let zv = Ltyping.instance id vars in
  let ts = List.map (fun (y,t) -> t) yv in
  let yt = List.map (fun (y,_) -> Tvar y) yv in
  let t = Env.generalize_logic_type (Function (ts,tr)) in
  let fall (y,t) acc = Forall (false, y, y, t, [], acc) in
  let body = Papp (t_eq, [Tapp (id,yt,zv); e], [tr]) in
  let axiom = List.fold_right fall yv body in
  let name = Ident.string id in
  [ Dlogic (loc, id, t);
    Daxiom (loc, name ^ "_def", Env.generalize_predicate axiom) ]

let predicate_def loc id d =
  let (vars,(yv,e)) = Env.specialize_predicate_def d in
  let zv = Ltyping.instance id vars in
  let ts = List.map (fun (y,t) -> t) yv in
  let yt = List.map (fun (y,_) -> Tvar y) yv in
  let t = Env.generalize_logic_type (Predicate ts) in
  let fall (y,t) acc = Forall (false, y, y, t, [], acc) in
  let axiom = List.fold_right fall yv (Piff (Papp (id,yt,zv), e)) in
  let name = Ident.string id in
  [ Dlogic (loc, id, t);
    Daxiom (loc, name ^ "_def", Env.generalize_predicate axiom) ]

(***************
 inductive definitions
**************)

(*

inductive id : t1 -> .. -> tn -> prop {

  c_1 : forall x_1,..,x_k : H1 -> .. Hi -> id(e_1,..,e_n)

| ...

| c_j

}

gives (j+1) axioms : j direct axioms

a_1 : forall x_1,..,x_k : H1 -> .. Hi -> id(e_1,..,e_n)
..
a_j : ...

and one inversion axiom :

forall y_1:t_1,..,y_n:t_n, id(y_1,..,y_n) ->

  exists x_1,..,x_k: H1 /\ ... /\ Hi /\ y_1 = e1 /\ .. /\ y_n = e_n

\/ 
 
  ... 

*)

let inductive_inverse_body id yv cases =
  let eq_and (y,t) e = Misc.pand (Papp (t_eq, [Tvar y; e], [t])) in
  let rec invert = function
    | Forall(w,id,n,t,trig,p) -> Exists(id,n,t,invert p)
    | Pimplies(w,h,p) -> Misc.pand h (invert p)
    | Papp(f,l,_) when f == id -> List.fold_right2 eq_and yv l Ptrue
    | _ -> assert false (* ill-formed, should have been catch by typing *)
  in
  List.fold_right (fun (_,c) -> Misc.por (invert c)) cases Pfalse

let inversion_axiom id zv bl cases =
  let yv = List.map (fun t -> (fresh_var(),t)) bl in
  let yt = List.map (fun (y,_) -> Tvar y) yv in
  let body = inductive_inverse_body id yv cases in
  let fall (y,t) acc = Forall (false, y, y, t, [], acc) in
  List.fold_right fall yv (Pimplies (false, Papp (id,yt,zv), body))

let inductive_def loc id d =
  let (vars,(bl,cases)) = Env.specialize_inductive_def d in
  let zv = Ltyping.instance id vars in
  let t = Env.generalize_logic_type (Predicate bl) in
  let name = Ident.string id in
  Dlogic(loc,id,t)::
    (Daxiom(loc,name ^ "_inversion",
	    Env.generalize_predicate (inversion_axiom id zv bl cases)))::
    (List.map 
       (fun (id,p) -> 
	  let p = Env.generalize_predicate p in
	  Daxiom(loc,Ident.string id,p)) cases)

(***************
 algebraic types
**************)

let fresh_cons zv id pl =
  let yv = List.map (fun t -> (fresh_var (),t)) pl in
  let yt = List.map (fun (y,_) -> Tvar y) yv in
  (yv, Tapp (id,yt,zv))

let yv_exists = List.fold_right (fun (y,t) f -> Exists (y,y,t,f))
let yv_forall = List.fold_right (fun (y,t) f -> Forall (false,y,y,t,[],f))
let peq t l r = Papp (t_eq, [l;r], [t])

(*
let alg_cons_injective_axiom loc zv th (id,pl) =
  let yv1,ct1 = fresh_cons zv id pl in
  let yv2,ct2 = fresh_cons zv id pl in
  let equ (y1,t) (y2,_) = peq t (Tvar y1) (Tvar y2) in
  let eqs = List.rev_map2 equ yv1 yv2 in
  let rst = List.fold_left Misc.pand Ptrue eqs in
  let body = Pimplies (false, peq th ct1 ct2, rst) in
  let body = yv_forall yv1 (yv_forall yv2 body) in
  let pred = Env.generalize_predicate body in
  Daxiom (loc, (Ident.string id) ^ "_injective", pred)
*)

let find_global_logic_gen id =
  let _,t = find_global_logic id in
  generalize_logic_type t

let alg_proj_fun loc zv th (id,pl) =
  let r = ref 0 in
  let yv,ct = fresh_cons zv id pl in
  let proj (v,t) =
    let nm = Ident.proj_id id !r in
    let head = Tapp (nm, [ct], zv) in
    let body = yv_forall yv (peq t head (Tvar v)) in
    let pred = Env.generalize_predicate body in
    let () = incr r in
    Dlogic (loc, nm, find_global_logic_gen nm) ::
      Daxiom (loc, Ident.string nm ^ "_def", pred) :: []
  in
  List.concat (List.map proj yv)

let alg_inversion_axiom loc id zv th cs =
  let x = fresh_var () in
  let inv_cons acc (id,pl) =
    let r = ref 0 in
    let targ _ =
      let nm = Ident.proj_id id !r in
      let () = incr r in
      Tapp (nm, [Tvar x], zv)
    in
    let ct = Tapp (id, List.map targ pl, zv) in
    Misc.por acc (peq th (Tvar x) ct)
  in
  let body = List.fold_left inv_cons Pfalse cs in
  let body = Forall (false,x,x,th,[],body) in
  let pred = Env.generalize_predicate body in
  Daxiom (loc, Ident.string id ^ "_inversion", pred)

let alg_match_fun_axiom loc id zv th cs =
  let nm = Ident.match_id id in
  let nt = PTvar (new_type_var ()) in
  let vs = List.map (fun _ -> (fresh_var (), nt)) cs in
  let ts = List.map (fun (v,_) -> Tvar v) vs in
  let head t = Tapp (nm, t :: ts, nt::zv) in
  let axiom (id,pl) v =
    let yv,ct = fresh_cons zv id pl in
    let body = peq nt (head ct) v in
    let body = yv_forall vs (yv_forall yv body) in
    let pred = Env.generalize_predicate body in
    Daxiom (loc, Ident.string nm ^ "_" ^ Ident.string id, pred)
  in
  Dlogic (loc, nm, find_global_logic_gen nm) ::
    List.map2 axiom cs ts

let alg_to_int_fun_axiom loc id zv th cs =
  let cpt = ref 0 in
  let ty = Function ([th], PTint) in
  let nm = Ident.create (Ident.string id ^ "_to_int") in
  let axiom (id,pl) =
    let yv,ct = fresh_cons zv id pl in
    let lst = Tapp (nm, [ct], zv) in
    let rst = Tconst (ConstInt (string_of_int !cpt)) in
    let body = yv_forall yv (Papp (t_eq_int,[lst;rst],[])) in
    let pred = Env.generalize_predicate body in
    incr cpt;
    Daxiom (loc, Ident.string nm ^ "_" ^ Ident.string id, pred)
  in
  Dlogic (loc, nm, Env.generalize_logic_type ty) ::
    List.map axiom cs

let algebraic_type_single (loc,id,d) =
  let vars,(vs,cs) = Env.specialize_alg_type d in
  let zv = Ltyping.instance id vars in
  let th = PTexternal (vs, id) in
  List.map (fun (c,_) ->
      Dlogic (loc, c, find_global_logic_gen c)) cs @
    alg_match_fun_axiom loc id zv th cs @
    List.concat (List.map (alg_proj_fun loc zv th) cs) @
    alg_inversion_axiom loc id zv th cs ::
    alg_to_int_fun_axiom loc id zv th cs
(*
    List.map (alg_cons_injective_axiom loc zv th)
      (List.filter (fun (_,pl) -> pl <> []) cs)
*)

let algebraic_type_decl (loc,id,d) =
  let string_of_var = function
    | PTvar v -> "a" ^ (string_of_int v.tag)
    | _ -> assert false
  in
  let vs, _ = d.Env.scheme_type in
  Dtype (loc, id, List.map string_of_var vs)

let algebraic_type ls =
  List.map algebraic_type_decl ls @
  List.concat (List.map algebraic_type_single ls)

