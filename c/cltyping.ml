(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: cltyping.ml,v 1.1 2004-01-14 16:33:28 filliatr Exp $ i*)

open Clogic

(*s Logic *)

let option_app f = function Some x -> Some (f x) | None -> None

let rec type_term env t =
  assert false (*TODO*)

let rec type_predicate env = function
  | Pfalse
  | Ptrue as p -> p
  | Pvar x -> (*TODO*) Pvar x.node
  | Prel (t1, r, t2) -> (*TODO*) Prel (type_term env t1, r, type_term env t2)
  | Pand (p1, p2) -> Pand (type_predicate env p1, type_predicate env p2)
  | Por (p1, p2) -> Por (type_predicate env p1, type_predicate env p2)
  | Pimplies (p1, p2) -> 
      Pimplies (type_predicate env p1, type_predicate env p2) 
  | Pnot p -> Pnot (type_predicate env p)
  | Papp (f, tl) -> (*TODO*) Papp (f.node, List.map (type_term env) tl)
  | Pif (t, p1, p2) -> Pif (type_term env t, type_predicate env p1,
			    type_predicate env p2)
  | Pforall (s, pt, p) -> Pforall (s, pt, type_predicate env p)
  | Pexists (s, pt, p) -> Pexists (s, pt, type_predicate env p)

let type_variant env (t, r) = (type_term env t, r)

let type_loop_annot env (i,v) =
  option_app (type_predicate env) i, type_variant env v

let type_spec env (p,e,q) = 
  option_app (type_predicate env) p, e, option_app (type_predicate env) q

