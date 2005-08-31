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

(*s Isabelle/HOL output *)

open Ident
open Misc
open Error
open Logic
open Vcg
open Format
open Cc
open Pp
(*
type elem = 
  | Parameter of string * cc_type
  | Obligation of obligation
  | Logic of string * logic_type Env.scheme
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme

let elem_q = Queue.create ()

let reset () = Queue.clear elem_q

let push_parameter id v = Queue.add (Parameter (id, v)) elem_q

let push_logic id t = Queue.add (Logic (id, t)) elem_q

let push_axiom id p = Queue.add (Axiom (id, p)) elem_q

let push_predicate id p = Queue.add (Predicate (id, p)) elem_q

let push_obligations = List.iter (fun o -> Queue.add (Obligation o) elem_q)
*)
(*s Pretty print *)

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | PTbool -> fprintf fmt "bool"
  | PTunit -> fprintf fmt "unit"
  | PTreal -> fprintf fmt "real"
  | PTarray v -> fprintf fmt "(%a list)" print_pure_type v (* TODO *)
  | PTexternal([],id) -> Ident.print fmt id
  | PTexternal([t],id) -> 
      fprintf fmt "(%a %a)"
      print_pure_type t
      Ident.print id
  | PTexternal(l,id) -> 
      fprintf fmt "((%a) %a)"
      (print_list comma print_pure_type) l
      Ident.print id
  | PTvar { type_val = Some t} -> 
      fprintf fmt "%a" print_pure_type t      
  | PTvar v -> fprintf fmt "'a%d" v.tag
  | PTvarid _ -> assert false

let prefix_id id =
  (* int cmp *)
  if id == t_lt_int then "(op <)" 
  else if id == t_le_int then "(op <=)"
  else if id == t_gt_int then "(%x y. y < x)"
  else if id == t_ge_int then "(%x y. y <= x)"
  else if id == t_eq_int then "(op =)"
  else if id == t_neq_int then "(%x y. x ~= y)"
  (* real cmp *)
  else if id == t_lt_real then "(op <)" 
  else if id == t_le_real then "(op <=)"
  else if id == t_gt_real then "(%x y. y < x)"
  else if id == t_ge_real then "(%x y. y <= x)"
  else if id == t_eq_real then "(op =)"
  else if id == t_neq_real then "(%x y. x ~= y)"
  (* bool cmp *)
  else if id == t_eq_bool then "(op =)"
  else if id == t_neq_bool then "(%x y. x ~= y)"
  (* unit cmp *)
  else if id == t_eq_unit then "(op =)"
  else if id == t_neq_unit then "(%x y. x ~= y)"
  (* int ops *)
  else if id == t_add_int then "(op +)"
  else if id == t_sub_int then "(op -)"
  else if id == t_mul_int then "(op *)"
  else if id == t_div_int then "(op div)"
  else if id == t_mod_int then "(op mod)"
  else if id == t_neg_int then "(%x. - x)"
  (* real ops *)
  else if id == t_add_real then "(op +)"
  else if id == t_sub_real then "(op -)"
  else if id == t_mul_real then "(op *)"
  else if id == t_div_real then "(op /)"
  else if id == t_neg_real then "(%x. - x)"
  else if id == t_sqrt_real then assert false (* TODO *)
  else if id == t_real_of_int then "real"
  else if id == t_int_of_real then assert false (* TODO *)
  else assert false

let rec print_term fmt = function
  | Tvar id -> 
      Ident.print fmt id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool true) -> 
      fprintf fmt "True" 
  | Tconst (ConstBool false) -> 
      fprintf fmt "False" 
  | Tconst ConstUnit -> 
      fprintf fmt "()" 
  | Tconst (ConstFloat (i,f,e)) ->
      let e = (if e = "" then 0 else int_of_string e) - String.length f in
      if e = 0 then
	fprintf fmt "(real (%s%s::int))" i f
      else if e > 0 then
	fprintf fmt "(real (%s%s::int * 1%s))" i f (String.make e '0')
      else
	fprintf fmt "(real (%s%s::int) / real (1%s::int))" 
	  i f (String.make (-e) '0')
  | Tderef _ -> 
      assert false
  (* arithmetic *)
  | Tapp (id, [a; b], _) when id == t_add_int || id == t_add_real ->
      fprintf fmt "(@[%a +@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _ ) when id == t_sub_int || id == t_sub_real ->
      fprintf fmt "(@[%a -@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _) when id == t_mul_int || id == t_mul_real ->
      fprintf fmt "(@[%a *@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _) when id == t_div_real ->
      fprintf fmt "(@[%a /@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _) when id == t_mod_int ->
      fprintf fmt "(@[%a mod@ %a@])" print_term a print_term b
  | Tapp (id, [a; b], _) when id == t_div_int ->
      fprintf fmt "(@[%a div@ %a@])" print_term a print_term b
  | Tapp (id, [a], _) when id == t_neg_int || id == t_neg_real ->
      fprintf fmt "(@[-%a@])" print_term a
  | Tapp (id, [a; b; c], _) when id == if_then_else -> 
      fprintf fmt "(@[if %a@ then %a@ else %a@])" 
	print_term a print_term b print_term c
  | Tapp (id, tl, _) when is_relation id || is_arith id -> 
      fprintf fmt "(@[%s %a@])" (prefix_id id) print_terms tl
  (* arrays *)
  | Tapp (id, [a; b], _) when id == access ->
      fprintf fmt "(@[%a !(nat %a) @])" print_term a print_term b
  | Tapp (id, [a], _) when id == Ident.array_length ->
      fprintf fmt "(@[int (length %a)@])" print_term a
  (* any other application *)
  | Tapp (id, tl, _) ->
      fprintf fmt "@[(%a@ %a)@]" 
	Ident.print id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "True"
  | Pvar id when id == default_post ->
      fprintf fmt "True"
  | Pfalse ->
      fprintf fmt "False"
  | Pvar id -> 
      fprintf fmt "%a" Ident.print id
  | Papp (id, [a; b], _) when is_eq id ->
      fprintf fmt "@[(%a =@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_neq id ->
      fprintf fmt "@[~(%a =@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_lt_int || id == t_lt_real ->
      fprintf fmt "@[(%a <@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_le_int || id == t_le_real ->
      fprintf fmt "@[(%a <=@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_gt_int || id == t_gt_real ->
      fprintf fmt "@[(%a <@ %a)@]" print_term b print_term a
  | Papp (id, [a; b], _) when id == t_ge_int || id == t_ge_real ->
      fprintf fmt "@[(%a <=@ %a)@]" print_term b print_term a
  | Papp (id, [a; b], _) when id == t_zwf_zero ->
      fprintf fmt "@[((0 <= %a) &@ (%a < %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix_id id) print_terms tl
  | Papp (id, tl, _) -> 
      fprintf fmt "@[(%a@ %a)@]" Ident.print id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "(@[%a -->@ %a@])" print_predicate a print_predicate b
  | Piff (a, b) ->
      fprintf fmt "(@[%a =@ %a@])" 
	print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt "(@[if %a@ then %a@ else %a@])" 
	print_term a print_predicate b print_predicate c
  | Pand (_, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(%a &@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(%a |@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[~(%a)@]" print_predicate a
  | Forall (_,id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "(@[(!%s::%a.@ %a)@])" (Ident.string id')
	print_pure_type t print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "(@[? %s::%a.@ %a@])" (Ident.string id')
	print_pure_type t print_predicate p'
  | Pfpi _ ->
      failwith "fpi not supported in Isabelle/HOL"
  | Pnamed (n, p) ->
      fprintf fmt "@[(* %s: *) %a@]" n print_predicate p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray v -> 
      fprintf fmt "(@[%a list@])" print_cc_type v
  | _ ->
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	fprintf fmt "shows \"@[%a@]\"@\n" print_predicate concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "fixes %a::\"%a\"@\n" Ident.print id print_cc_type v;
	print_seq fmt hyps
    | Spred (id, p) :: hyps -> 
	fprintf fmt "assumes %a: \"@[%a@]\"@\n" Ident.print id print_predicate p;
	print_seq fmt hyps
  in
  fprintf fmt "@[%a@]@?" print_seq hyps

let print_predicate_scheme fmt p =
  let (l,p) = Env.specialize_predicate p in
  print_predicate fmt p

let reprint_parameter fmt id c =
  fprintf fmt 
    "@[<hov 2>(*Why*) consts %s ::@ @[\"%a\"@]@];@\n" id print_cc_type c

let print_parameter = reprint_parameter


let print_logic_type fmt s = 
  let (l,t) = Env.specialize_logic_type s in
  match t with
  | Logic.Function ([], t) ->
      print_pure_type fmt t
  | Logic.Function (pl, t) ->
      fprintf fmt "[%a] => %a" 
	(print_list comma print_pure_type) pl print_pure_type t
  | Logic.Predicate [] ->
      fprintf fmt "bool"
  | Logic.Predicate pl ->
      fprintf fmt "[%a] => bool" (print_list comma print_pure_type) pl

let reprint_logic fmt id t =
  fprintf fmt 
    "@[<hov 2>(*Why logic*) consts %s ::@ @[\"%a\"@]@];@\n" 
    id print_logic_type t

let print_logic fmt id t = reprint_logic fmt id t

let reprint_axiom fmt id p =
  fprintf fmt "(*Why axiom*) axioms %s: \"%a\";@\n@\n" id print_predicate_scheme p

let print_axiom fmt id p = 
  reprint_axiom fmt id p

let reprint_obligation fmt (loc,id,s) =
  fprintf fmt "@[(* %a *)@]@\n" Loc.report_obligation loc;
  fprintf fmt "(*Why goal*) lemma %s: %a;@\n" id print_sequent s

let print_obligation fmt o = 
  reprint_obligation fmt o;
  fprintf fmt "(* FILL PROOF HERE *)@\n@\n"

let reprint_predicate fmt id p =
  let (l,(bl,p)) = Env.specialize_predicate_def p in
  let print_binder_type fmt (x,pt) = 
      fprintf fmt "%a" print_pure_type pt in
  let print_binder fmt (x,pt) = 
      fprintf fmt "%a" Ident.print x in
  fprintf fmt
     "@[<hov 2>(*Why predicate*) constdefs %s :: @[\"[%a] => bool\"@]@]@\n" 
    id 
    (print_list comma print_binder_type) bl;
  fprintf fmt
     "@[<hov 2>     \"%s %a == @[%a@]\"@];@\n" 
    id 
    (print_list space print_binder) bl
    print_predicate p 

let print_predicate fmt id p = reprint_predicate fmt id p

let reprint_function fmt id p =
  let (l,(bl,t,e)) = Env.specialize_function_def p in
  let print_binder_type fmt (x,pt) = 
      fprintf fmt "%a" print_pure_type pt in
  let print_binder fmt (x,pt) = 
      fprintf fmt "%a" Ident.print x in
  fprintf fmt
     "@[<hov 2>(*Why function*) constdefs %s :: @[\"[%a] => %a\"@]@]@\n" 
    id 
    (print_list comma print_binder_type) bl print_pure_type t;
  fprintf fmt
     "@[<hov 2>     \"%s %a == @[%a@]\"@];@\n" 
    id 
    (print_list space print_binder) bl
    print_term e 

let print_function fmt id p = reprint_function fmt id p

let theory_name = ref ""

open Regen

module Gen = Regen.Make(
struct

  let print_element fmt e = 
    begin match e with
      | Parameter (id, c) -> print_parameter fmt id c
      | Obligation o -> print_obligation fmt o
      | Logic (id, t) -> print_logic fmt id t
      | Axiom (id, p) -> print_axiom fmt id p
      | Predicate (id, p) -> print_predicate fmt id p
      | Function (id, f) -> print_function fmt id f
    end;
    fprintf fmt "@\n"
      
  let reprint_element fmt = function
    | Parameter (id, c) -> reprint_parameter fmt id c
    | Obligation o -> reprint_obligation fmt o
    | Logic (id, t) -> reprint_logic fmt id t
    | Axiom (id, p) -> reprint_axiom fmt id p
    | Predicate (id, p) -> reprint_predicate fmt id p
    | Function (id, f) -> reprint_function fmt id f

  let re_oblig_loc = Str.regexp "(\\* Why obligation from .*\\*)"

  let first_time fmt =
    fprintf fmt "\
(* This file was originally generated by why.
   It can be modified; only the generated parts will be overwritten. *)@\n
theory %s = %s:@\n@\n" (!theory_name) Options.isabelle_base_theory

  let first_time_trailer fmt = fprintf fmt "end@\n"

  let not_end_of_element _ s =
    let n = String.length s in n = 0 || s.[n-1] <> ';'

end)


let reset = Gen.reset

let push_obligations = 
  List.iter (fun ((_,l,_) as o) -> Gen.add_elem (Oblig, l) (Obligation o))

let push_parameter id v =
  Gen.add_elem (Param, id) (Parameter (id,v))

let push_logic id t = 
  Gen.add_elem (Lg, id) (Logic (id, t))

let push_axiom id p =
  Gen.add_elem (Ax, id) (Axiom (id, p))

let push_predicate id p =
  Gen.add_elem (Pr, id) (Predicate (id, p))

let push_function id p =
  Gen.add_elem (Fun, id) (Function (id, p))

let _ = 
  Gen.add_regexp 
    "lemma[ ]+\\(.*_po_[0-9]+\\)[ ]*:[ ]*" Oblig;
  Gen.add_regexp 
    "(\\*Why goal\\*) lemma[ ]+\\([^ ]*\\)[ ]*:[ ]*" Oblig;
  Gen.add_regexp 
    "(\\*Why\\*) consts[ ]+\\([^ ]*\\)[ ]*::[ ]*" Param;
  Gen.add_regexp 
    "(\\*Why axiom\\*) axioms[ ]+\\([^ ]*\\):[ ]*" Ax;
  Gen.add_regexp 
    "(\\*Why logic\\*) consts[ ]+\\([^ ]*\\)[ ]*::[ ]*" Lg;
  Gen.add_regexp 
    "(\\*Why predicate\\*) constdefs[ ]+\\([^ ]*\\)[ ]*::[ ]*" Pr;
  Gen.add_regexp 
    "(\\*Why function\\*) constdefs[ ]+\\([^ ]*\\)[ ]*::[ ]*" Fun

let output_file fwe =
  let f = fwe ^ "_why.thy" in
  theory_name := Filename.basename fwe ^ "_why";
  Gen.output_file f
