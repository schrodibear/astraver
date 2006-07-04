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

(*i $Id: pretty.ml,v 1.3 2006-07-04 09:08:54 filliatr Exp $ i*)

open Format
open Pp
open Ident
open Logic
open Logic_decl

let queue = Queue.create ()

let push_decl d = Queue.add d queue

let ident = Ident.print

let type_vars = Hashtbl.create 17

let type_var fmt n =
  try
    fprintf fmt "'a%d" (Hashtbl.find type_vars n)
  with Not_found -> 
    assert false

let specialize s =
  Hashtbl.clear type_vars;
  let n = ref 0 in
  Env.Vset.iter 
    (fun tv -> incr n; Hashtbl.add type_vars tv.tag !n) s.Env.scheme_vars;
  s.Env.scheme_type

let rec pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTreal -> fprintf fmt "real"
  | PTexternal ([],id) -> fprintf fmt "%a" ident id
  | PTvar {tag=t; type_val=None} -> type_var fmt t
  | PTvar {tag=t; type_val=Some pt} -> pure_type fmt pt
  | PTexternal ([t],id) -> 
      fprintf fmt "%a %a" pure_type t ident id
  | PTexternal (l,id) -> fprintf fmt "(%a) %a" 
      (print_list comma pure_type) l ident id

let rec term fmt = function
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "%b" b
  | Tconst ConstUnit -> 
      fprintf fmt "void" 
  | Tconst (ConstFloat (i,f,"")) -> 
      fprintf fmt "%s.%s" i f
  | Tconst (ConstFloat (i,f,e)) -> 
      fprintf fmt "%s.%se%s" i f e
  | Tvar id | Tderef id | Tapp (id, [], _) -> 
      ident fmt id
  | Tapp (id, [t1; t2], _) when id == t_add_int ->
      fprintf fmt "(%a + %a)" term t1 term t2
  | Tapp (id, [t1; t2], _) when id == t_sub_int ->
      fprintf fmt "(%a - %a)" term t1 term t2
  | Tapp (id, [t1; t2], _) when id == t_mul_int ->
      fprintf fmt "(%a * %a)" term t1 term t2
  | Tapp (id, [t1], _) when id == t_neg_int ->
      fprintf fmt "(-%a)" term t1
  | Tapp (id, tl, _) -> 
      fprintf fmt "%a(%a)" ident id (print_list comma term) tl

let int_relation_string id =
  if id == t_lt_int then "<" 
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  else assert false

let rec predicate fmt = function
  | Pvar id | Papp (id, [], _) -> 
      ident fmt id
  | Papp (id, [t1; t2], _) when is_eq id ->
      fprintf fmt "(%a = %a)" term t1 term t2
  | Papp (id, [t1; t2], _) when is_neq id ->
      fprintf fmt "(%a <> %a)" term t1 term t2
  | Papp (id, [t1; t2], _) when is_int_comparison id ->
      fprintf fmt "(%a %s %a)" term t1 (int_relation_string id) term t2
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[((0 <= %a) and@ (%a < %a))@]" term b term a term b
  | Papp (id, l, _) ->
      fprintf fmt "%s(%a)" (Ident.string id) (print_list comma term) l
  | Ptrue ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pimplies (_, a, b) -> 
      fprintf fmt "(@[%a ->@ %a@])" predicate a predicate b
  | Piff (a, b) -> 
      fprintf fmt "(@[%a <->@ %a@])" predicate a predicate b
  | Pif (a, b, c) -> 
      fprintf fmt "(@[if %a then@ %a else@ %a@])" 
	term a predicate b predicate c
  | Pand (_, _, a, b) ->
      fprintf fmt "(@[%a and@ %a@])" predicate a predicate b
  | Forallb (_, ptrue, pfalse) ->
      fprintf fmt "(@[forallb(%a,@ %a)@])" 
	predicate ptrue predicate pfalse
  | Por (a, b) ->
      fprintf fmt "(@[%a or@ %a@])" predicate a predicate b
  | Pnot a ->
      fprintf fmt "(not %a)" predicate a
  | Forall (_,_,b,v,tl,p) ->
      fprintf fmt "@[<hov 2>(forall %a:%a%a.@ %a)@]"
	ident b 
	pure_type v print_triggers tl predicate p
  | Exists (_,b,_,p) ->
      fprintf fmt "@[<hov 2>(exists %a:@ %a)@]" 
	ident b predicate p
  | Pfpi (t, (i1,f1,e1), (i2,f2,e2)) ->
      fprintf fmt "@[<hov 2>fpi(%a,@ %s.%se%s,@ %s.%se%s)@]" 
	term t i1 f1 e1 i2 f2 e2
  | Pnamed (n, p) ->
      fprintf fmt "@[(%S:@ %a)@]" n predicate p

and print_pattern fmt = function
  | TPat t -> term fmt t
  | PPat p -> predicate fmt p

and print_triggers fmt = function
  | [] -> 
      ()
  | tl -> 
      fprintf fmt " [%a]" (print_list alt (print_list comma print_pattern)) tl

let sequent fmt (ctx, p) =
  let context fmt = function
    | Cc.Svar (id, pt) ->
	fprintf fmt "forall %a:%a." ident id pure_type pt
    | Cc.Spred (_, p) ->
	fprintf fmt "@[%a ->@]" predicate p
  in
  print_list newline context fmt ctx;
  if ctx <> [] then fprintf fmt "@\n";
  predicate fmt p

let logic_binder fmt (id, pt) =
  fprintf fmt "%a: %a" ident id pure_type pt

let logic_type fmt = function
  | Predicate ptl -> 
      fprintf fmt "%a -> prop" (print_list comma pure_type) ptl
  | Function (ptl, pt) -> 
      fprintf fmt "%a -> %a" (print_list comma pure_type) ptl pure_type pt

let type_parameters fmt l = 
  let type_var fmt id = fprintf fmt "'%s" id in
  match l with
  | [] -> ()
  | [id] -> fprintf fmt "%a " type_var id
  | l -> fprintf fmt "(%a) " (print_list comma type_var) l

let decl fmt = function
  | Dtype (_, pl, id) ->
      fprintf fmt "@[type %a%s@]" type_parameters pl id
  | Dlogic (_, id, lt) ->
      let lt = specialize lt in
      fprintf fmt "@[logic %s : %a@]" id logic_type lt
  | Dpredicate_def (_, id, def) ->
      let bl,p = specialize def in
      fprintf fmt "@[<hov 2>predicate %s(%a) =@ %a@]" id 
	(print_list comma logic_binder) bl predicate p
  | Dfunction_def (_, id, def) ->
      let bl,pt,t = specialize def in
      fprintf fmt "@[<hov 2>function %s(%a) : %a =@ %a@]" id
	(print_list comma logic_binder) bl pure_type pt term t
  | Daxiom (_, id, p) ->
      let p = specialize p in
      fprintf fmt "@[<hov 2>axiom %s:@ %a@]" id predicate p
  | Dgoal (_, id, sq) ->
      let sq = specialize sq in
      fprintf fmt "@[<hov 2>goal %s:@\n%a@]" id sequent sq

let decl fmt d = fprintf fmt "@[%a@]@\n@\n" decl d

let print_file fmt = Queue.iter (decl fmt) queue

let output_file f =
  print_in_file print_file (f ^ "_why.why")

