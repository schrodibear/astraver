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

(*i $Id: cvcl.ml,v 1.10 2004-07-12 13:12:52 filliatr Exp $ i*)

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

type elem = 
  | Parameter of string * cc_type
  | Logic of string * logic_type Env.scheme
  | Oblig of obligation 
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme

let queue = Queue.create ()

let reset () = Queue.clear queue

let push_parameter id v = Queue.add (Parameter (id, v)) queue

let push_logic id t = Queue.add (Logic (id, t)) queue

let push_obligations = List.iter (fun o -> Queue.add (Oblig o) queue)

let push_axiom id p = Queue.add (Axiom (id, p)) queue

let push_predicate id p = Queue.add (Predicate (id, p)) queue

let defpred = Hashtbl.create 97

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
  | PTexternal ([],id) -> fprintf fmt "%a" Ident.print id
  | PTexternal (pl,id) -> 
      fprintf fmt "%a_%a" 
	(print_list underscore print_pure_type) pl Ident.print id

let instance fmt = function
  | [] -> 
      ()
  | ptl -> 
      let one fmt = function 
	| None -> assert false 
	| Some pt -> print_pure_type fmt pt 
      in 
      fprintf fmt "_%a" (print_list underscore one) ptl

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
  | Papp (id, tl, _) -> 
      fprintf fmt "@[%a(%a)@]" Ident.print id print_terms tl
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
      fprintf fmt "[%a ->@%a]" print_cc_type t1 print_cc_type t2
  | _ -> 
      assert false
(***
  | TTlambda (b, t) ->
      fprintf fmt "[%a]@,%a" print_binder b print_cc_type t
  | TTtuple ([_,CC_var_binder t], None) -> 
      print_cc_type fmt t
  | TTtuple (bl, None) ->
      fprintf fmt "(@[tuple_%d@ %a@])" (List.length bl) 
	(print_list space print_binder_type) bl
  | TTtuple (bl, Some q) -> 
      fprintf fmt "(@[sig_%d@ %a@ %a(%a)@])" (List.length bl)
	(print_list space print_binder_type) bl 
	(print_list nothing 
	   (fun fmt b -> fprintf fmt "[%a]@," print_binder b)) bl
	print_cc_type q
  | TTpred p ->
      print_predicate fmt p
  | TTapp (tt, l) ->
      fprintf fmt "(@[%a@ %a@])" print_cc_type tt
	(print_list space print_cc_type) l
  | TTterm t ->
      print_term fmt t
  | TTSet ->
      fprintf fmt "Set"
***)

(* Table of closed instances *)

module Instances = 
  Set.Make(struct type t = pure_type list let compare = compare end)

let instances_t = Hashtbl.create 97

let instances = Hashtbl.find instances_t

let add_instance x i =
  let s = try Hashtbl.find instances_t x with Not_found -> Instances.empty in
  Hashtbl.replace instances_t x (Instances.add i s)

let instance x i = 
  try 
    let ci = 
      List.map 
	(function Some pt when is_closed_pure_type pt -> pt | _ -> raise Exit)
	i
    in
    add_instance x ci
  with Exit -> 
    ()

let iter_instances f = Hashtbl.iter (fun x -> Instances.iter (f x)) instances_t

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

let print_obligation fmt (loc, o, s) = 
  fprintf fmt "@[%%%% %s, %a@]@\n" o Loc.report_obligation loc;
  fprintf fmt "@[<hov 2>QUERY %a;@]@\n@\n" print_sequent s

let print_axiom fmt id p =
  fprintf fmt "@[%%%% Why axiom %s@]@\n" id;
  fprintf fmt "@[<hov 2>ASSERT %a;@]@\n@\n" print_predicate p.Env.scheme_type

let rec print_logic_type fmt = function
  | Logic.Predicate [] ->
      fprintf fmt "BOOLEAN"
  | Logic.Predicate [pt] ->
      fprintf fmt "[%a -> BOOLEAN]" print_pure_type pt
  | Logic.Predicate pl ->
      fprintf fmt "[[%a] -> BOOLEAN]" (print_list comma print_pure_type) pl
  | Function ([], pt) ->
      print_pure_type fmt pt
  | Function ([pt1], pt2) ->
      fprintf fmt "[%a -> %a]" print_pure_type pt1 print_pure_type pt2
  | Function (pl, pt) ->
      fprintf fmt "[[%a] -> %a]" 
	(print_list comma print_pure_type) pl print_pure_type pt

let print_predicate fmt id p =
  fprintf fmt "@[%%%% Why predicate %s@]@\n" id;
  let (bl,p) = p.Env.scheme_type in
  assert (bl <> []);
  fprintf fmt "@[<hov 2>%s: %a =@ LAMBDA (%a):@ @[%a@];@]@\n@\n"
    id
    print_logic_type (Logic.Predicate (List.map snd bl))
    (print_list comma 
       (fun fmt (x,pt) -> 
	  fprintf fmt "%a: %a" Ident.print x print_pure_type pt )) bl 
    print_predicate p

let print_parameter fmt id c =
  fprintf fmt 
    "@[%%%% Why parameter %s@]@\n" id;
  fprintf fmt 
    "@[<hov 2>%s: %a;@]@\n@\n" id print_cc_type c

let rec subst_pure_type s = function
  | PTvarid id as t ->
      (try List.assoc (Ident.string id) s with Not_found -> t)
  | PTexternal (l, id) ->
      PTexternal (List.map (subst_pure_type s) l, id)
  | PTarray ta -> PTarray (subst_pure_type s ta)
  | PTint | PTreal | PTbool | PTunit | PTvar _ as t -> t

let subst_logic_type s = function
  | Function (tl, tr) -> 
      Function (List.map (subst_pure_type s) tl, subst_pure_type s tr)
  | Logic.Predicate tl -> 
      Logic.Predicate (List.map (subst_pure_type s) tl)

let print_logic fmt id t = 
  fprintf fmt "%%%% Why logic %s@\n" id;
  if t.scheme_vars = [] then
    fprintf fmt "@[%s: %a;@]@\n@\n" id print_logic_type t.scheme_type
  else
    try
      Instances.iter 
	(fun i -> 
	   assert (List.length t.scheme_vars = List.length i);
	   let s = List.combine t.scheme_vars i in
	   let t = subst_logic_type s t.scheme_type in
	   fprintf fmt "@[%s_%a: %a;@]@\n" id 
	     (print_list underscore print_pure_type) i print_logic_type t)
	(instances (Ident.create id));
      fprintf fmt "@\n"
    with Not_found ->
      fprintf fmt "%%%% no closed instance@\n@\n"

let print_elem fmt = function
  | Oblig o -> print_obligation fmt o
  | Axiom (id, p) -> print_axiom fmt id p
  | Predicate (id, p) -> print_predicate fmt id p
  | Logic (id, t) -> print_logic fmt id t
  | Parameter (id, t) -> print_parameter fmt id t

let prelude fmt = 
fprintf fmt "
UNIT: TYPE;
tt: UNIT;
sqrt_real: [REAL -> REAL];
int_of_real: [REAL -> INT];
mod_int: [[INT, INT] -> INT];
"

(* ieration over terms (function [f]) and types (function [g]) *)
module IterTT = struct

  let rec predicate f g = function
    | Pand (_, a, b)
    | Por (a, b)
    | Piff (a, b)
    | Forallb (_, a, b)
    | Pimplies (_, a, b) -> predicate f g a; predicate f g b
    | Pif (a, b, c) -> f a; predicate f g b; predicate f g c
    | Pnot a -> predicate f g a
    | Exists (_, _, v, p)
    | Forall (_, _, _, v, p) -> g v; predicate f g p
    | Ptrue | Pfalse | Pvar _ | Pfpi _ -> ()
    | Papp (_, tl, _) -> List.iter f tl
	
  let logic_type g = function
    | Function (l, pt) -> List.iter g l; g pt
    | Logic.Predicate l -> List.iter g l

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
	f t
    | TTSet ->
	()
	
  and cc_binder f g = function
    | _, CC_var_binder cc -> cc_type f g cc
    | _, CC_pred_binder p -> predicate f g p
    | _, CC_untyped_binder -> ()
	
  let element f g = function
    | Parameter (_,cc) -> 
	cc_type f g cc
    | Logic (_, lt) -> 
	logic_type g lt.scheme_type
    | Oblig (_,_,(ctx,p)) -> 
	List.iter 
	  (function 
	     | Svar (_,cc) -> cc_type f g cc | Spred (_,p) -> predicate f g p)
	  ctx;
	predicate f g p
    | Axiom (_, p) -> 
	predicate f g p.scheme_type
    | Predicate (_, {scheme_type=(bl,p)}) -> 
	List.iter (fun (_,pt) -> g pt) bl; predicate f g p

end

(* first pass: we traverse all elements to collect types and closed instances
   of function symbols *)
let first_pass fmt = 
  let rec collect_term = function
    | Tapp (id, tl, i) -> instance id i; List.iter collect_term tl
    | _ -> ()
  in
  let types_to_declare = Hashtbl.create 97 in
  let collect_type = function
    | PTexternal (i, id) as pt when is_closed_pure_type pt ->
	if not (Hashtbl.mem types_to_declare pt) then 
	  Hashtbl.add types_to_declare pt ()
    | _ -> ()
  in
  Queue.iter (IterTT.element collect_term collect_type) queue;
  (* declaring types *)
  Hashtbl.iter
    (fun pt () -> fprintf fmt "@[%a: TYPE;@]@\n@\n" print_pure_type pt)
    types_to_declare;
  (* declaring predefined symbols *)
  List.iter (fun (s,t) -> print_logic fmt s (generalize_logic_type t))
    [ "array_length", 
      Function ([PTarray (PTvarid (Ident.create "a"))], PTint);
      "access",
      let a = PTvarid (Ident.create "a") in Function ([PTarray a; PTint], a)
    ]

let output_file fwe =
  let sep = "%%%% DO NOT EDIT BELOW THIS LINE" in
  let f = fwe ^ "_why.cvc" in
  do_not_edit f
    (fun fmt -> if not no_cvcl_prelude then prelude fmt)
    sep
    (fun fmt -> 
       first_pass fmt;
       Queue.iter (print_elem fmt) queue)

