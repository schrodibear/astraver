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

(*i $Id: mizar.ml,v 1.21 2004-12-01 17:10:03 filliatr Exp $ i*)

(*s Mizar output *)

open Options
open Ident
open Misc
open Error
open Logic
open Vcg
open Format
open Cc
open Pp

type elem = 
  | Parameter of string * cc_type
  | Obligation of obligation
  | Logic of string * logic_type Env.scheme
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme

let elem_q = Queue.create ()

let reset () = Queue.clear elem_q

let push_parameter id v = Queue.add (Parameter (id, v)) elem_q

let push_obligations = List.iter (fun o -> Queue.add (Obligation o) elem_q)

let push_logic id t = Queue.add (Logic (id, t)) elem_q

let push_axiom id p = Queue.add (Axiom (id, p)) elem_q

let push_predicate id p = Queue.add (Predicate (id, p)) elem_q

(*s Pretty print *)

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "Integer"
  | PTbool -> fprintf fmt "Element of BOOLEAN"
  | PTunit -> fprintf fmt "Element of {0}"
  | PTreal -> fprintf fmt "Real"
  | PTexternal([],id) -> Ident.print fmt id
  | PTarray PTunit -> fprintf fmt "XFinSequence of {0}"
  | PTarray PTbool -> fprintf fmt "XFinSequence of BOOLEAN"
  | PTarray PTint -> fprintf fmt "XFinSequence of INT"
  | PTarray PTreal -> fprintf fmt "XFinSequence of REAL"
  | PTarray (PTexternal([],id)) -> fprintf fmt "XFinSequence of %a" Ident.print id
  | PTarray (PTarray _) -> assert false
  | PTarray (PTexternal _)
  | PTarray (PTvar _)
  | PTexternal _ | PTvar _ ->  failwith "no polymorphism with Mizar yet"
  | PTvarid _  
  | PTarray (PTvarid _) -> assert false

let prefix_id id =
  (* int cmp *)
  if id == t_lt_int then "int_lt" 
  else if id == t_le_int then "int_le"
  else if id == t_gt_int then "int_gt"
  else if id == t_ge_int then "int_ge"
  else if id == t_eq_int then assert false (* TODO *)
  else if id == t_neq_int then assert false (* TODO *)
  (* real cmp *)
  else if id == t_lt_real then "real_lt" 
  else if id == t_le_real then "real_le"
  else if id == t_gt_real then "real_gt"
  else if id == t_ge_real then "real_ge"
  else if id == t_eq_real then assert false (* TODO *)
  else if id == t_neq_real then assert false (* TODO *)
  (* bool cmp *)
  else if id == t_eq_bool then assert false (* TODO *)
  else if id == t_neq_bool then assert false (* TODO *)
  (* unit cmp *)
  else if id == t_eq_unit then assert false (* TODO *)
  else if id == t_neq_unit then assert false (* TODO *)
  (* int ops *)
  else if id == t_add_int then "int_add"
  else if id == t_sub_int then "int_sub"
  else if id == t_mul_int then "int_mul"
  else if id == t_div_int then assert false (* TODO *)
  else if id == t_mod_int then assert false (* TODO *)
  else if id == t_neg_int then "int_neg"
  (* real ops *)
  else if id == t_add_real then "real_add"
  else if id == t_sub_real then "real_sub"
  else if id == t_mul_real then "real_mul"
  else if id == t_div_real then "real_div"
  else if id == t_neg_real then "real_neg"
  else if id == t_sqrt_real then assert false (* TODO *)
  else if id == t_real_of_int then assert false (* TODO *)
  else assert false

let rec print_term fmt t = 
  let rec print0 fmt = function
    | Tapp (id, [a; b], _) when is_relation id -> 
	fprintf fmt "@[%s(@[%a,@ %a@])@]" 
	  (prefix_id id) print0 a print0 b
    | t ->
	print1 fmt t
  and print1 fmt = function
    | Tapp (id, [a; b], _) when id == t_add_int || id == t_add_real ->
	fprintf fmt "%a +@ %a" print1 a print2 b
    | Tapp (id, [a; b], _) when id == t_sub_int || id == t_sub_real ->
	fprintf fmt "%a -@ %a" print1 a print2 b
    | t ->
	print2 fmt t
  and print2 fmt = function
    | Tapp (id, [a; b], _) when id == t_mul_int || id == t_mul_real ->
	fprintf fmt "%a *@ %a" print2 a print3 b
    | Tapp (id, [a; b], _) when id == t_div_int || id == t_div_real ->
	fprintf fmt "%a /@ %a" print2 a print3 b
    | Tapp (id, [a; b], _) when id == t_mod_int ->
	fprintf fmt "%a mod %a" print2 a print3 b
    | t -> 
	print3 fmt t
  and print3 fmt = function
    | Tvar id -> 
	Ident.print fmt id
    | Tconst (ConstInt n) -> 
	fprintf fmt "%d" n
    | Tconst (ConstBool true) -> 
	fprintf fmt "TRUE" 
    | Tconst (ConstBool false) -> 
	fprintf fmt "FALSE" 
    | Tconst ConstUnit -> 
	fprintf fmt "(Extract 0)" 
    | Tconst (ConstFloat (i,f,"")) ->
	fprintf fmt "%s.%s" i f
    | Tconst (ConstFloat (i,f,e)) ->
	fprintf fmt "%s.%se%s" i f e
    | Tderef _ -> 
	assert false
    (* arithmetic *)
    | Tapp (id, [a], _) when id == t_neg_int || id == t_neg_real ->
	fprintf fmt "(@[-%a@])" print3 a
    | Tapp (id, [_;_], _) as t when is_relation id || is_int_arith_binop id ->
	fprintf fmt "(@[%a@])" print0 t
    | Tapp (id, [a; b; c], _) when id == if_then_else -> 
	fprintf fmt "@[if-then-else(@[%a,@ %a,@ %a@])@]" 
	print0 a print0 b print0 c
    (* arrays *)
    | Tapp (id, [a; b], _) when id == access ->
	fprintf fmt "(@[%a.%a@])" print0 a print0 b
    | Tapp (id, [a; b; c], _) when id == store ->
	fprintf fmt "(@[%a+*(%a,@ %a)@])" 
	print3 b print0 a print0 c
    | Tapp (id, [a], _) when id == Ident.array_length ->
	fprintf fmt "(@[len %a@])" print0 a
    (* any other application *)
    | Tapp (id, tl, _) when is_relation id || is_arith id -> 
	fprintf fmt "%s(@[%a@])" (prefix_id id) print_terms tl
    | Tapp (id, tl, _) ->
	fprintf fmt "%a(@[%a@])" Ident.print id print_terms tl
  in
  print0 fmt t

and print_terms fmt tl = 
  print_list comma print_term fmt tl

let infix_relation id =
       if id == t_lt_int || id == t_lt_real then "<" 
  else if id == t_le_int || id == t_le_real then "<="
  else if id == t_gt_int || id == t_gt_real then ">"
  else if id == t_ge_int || id == t_ge_real then ">="
  else if is_eq id then "="
  else if is_neq id then "<>"
  else assert false

let print_predicate fmt p = 
  let rec print0 fmt = function
    | Pimplies (_, a, b) ->
	fprintf fmt "(@[%a implies@ %a@])" print1 a print0 b
    | Piff ( a, b) ->
	fprintf fmt "(@[%a iff@ %a@])" print1 a print0 b
    | Pif (a, b, c) ->
	fprintf fmt "(@[(%a = TRUE implies %a) &@ (%a = FALSE implies %a)@])" 
	print_term a print0 b print_term a print0 c
    | p -> 
	print1 fmt p
  and print1 fmt = function
    | Por (a, b) ->
	fprintf fmt "@[%a or@ %a@]" print2 a print1 b
    | p ->
	print2 fmt p
  and print2 fmt = function
    | Pand (_, a, b) | Forallb (_, a, b) ->
	fprintf fmt "@[%a &@ %a@]" print3 a print2 b
    | p ->
	print3 fmt p
  and print3 fmt = function
    | Ptrue ->
	fprintf fmt "not contradiction"
    | Pvar id when id == default_post ->
	fprintf fmt "not contradiction"
    | Pfalse ->
	fprintf fmt "contradiction"
    | Pvar id -> 
	fprintf fmt "%a" Ident.print id
    | Papp (id, [a; b], _) when is_relation id ->
	fprintf fmt "@[%a %s@ %a@]" 
	print_term a (infix_relation id) print_term b
    | Papp (id, [a; b], _) when id == t_zwf_zero ->
	fprintf fmt "@[(0 <= %a &@ %a < %a)@]" 
	print_term b print_term a print_term b
    | Papp (id, tl, _) when is_relation id || is_arith id ->
	fprintf fmt "@[%s(%a)@]" (prefix_id id) print_terms tl
    | Papp (id, tl, _) -> 
	fprintf fmt "@[%a(%a)@]" Ident.print id print_terms tl
    | Pnot a ->
	fprintf fmt "@[not %a@]" print3 a
    | Forall (_,id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[for %s@ being %a holds@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Exists (id,n,t,p) -> 
	let id' = next_away id (predicate_vars p) in
	let p' = subst_in_predicate (subst_onev n id') p in
	fprintf fmt "(@[ex %s being %a st@ %a@])" (Ident.string id')
	  print_pure_type t print0 p'
    | Pfpi _ ->
	failwith "fpi not supported with Mizar"
    | Pnamed (_, p) -> (* TODO: print name *)
	print3 fmt p
    | (Por _ | Piff _ | Pand _ | Pif _ | Pimplies _ | Forallb _) as p -> 
	fprintf fmt "(%a)" print0 p
  in
  print0 fmt p

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray (TTpure pt) -> 
      print_pure_type fmt (PTarray pt)
  | _ ->
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[for %a being @[%a@] holds@]@\n" 
	  Ident.print id print_cc_type v;
	print_seq fmt hyps
    | Spred (_, p) :: hyps -> 
	fprintf fmt "@[(@[%a@]) %s@]@\n" print_predicate p
	  (match hyps with Spred _ :: _ -> "&" | _ -> "implies");
	print_seq fmt hyps
  in
  let print_intro fmt = function
    | Svar (id, v) -> 
	fprintf fmt "let %a be @[%a@];@\n" Ident.print id print_cc_type v
    | Spred (id, p) -> 
	fprintf fmt "assume %a: @[%a@];@\n" Ident.print id print_predicate p
  in
  let print_intros fmt = List.iter (print_intro fmt) in
  fprintf fmt "@[ @[%a@]@\nproof@\n @[%a@]:: EDIT BELOW THIS LINE@]" 
    print_seq hyps print_intros hyps

let rec print_thesis fmt = function
  | Pand (_, t1, t2) -> fprintf fmt "%a@ %a" print_thesis t1 print_thesis t2
  | t -> fprintf fmt "@[thus %a@];" print_predicate t

let reprint_obligation fmt (loc,id,s) =
  fprintf fmt "@[ :: %a @]@\n" Loc.report_obligation loc;
  fprintf fmt "@[ theorem %s:@\n @[%a@]@]@\n" id print_sequent s

let print_obligation fmt ((_,_,(_,t)) as o) = 
  reprint_obligation fmt o;
  fprintf fmt "@[  :: FILL PROOF HERE@\n  @[%a@]@]@\n end;@\n" print_thesis t

let reprint_parameter fmt id c =
  fprintf fmt 
    "@[<hov 2> :: Why Parameter (TODO)@]@\n" (* id print_cc_type c *)

let print_parameter = reprint_parameter

let print_logic fmt id t = 
  let (l,t) = Env.specialize_logic_type t in
  assert false (*TODO*)

let reprint_logic fmt id t = print_logic fmt id t

let reprint_axiom fmt id p =
  let (l,p) = Env.specialize_predicate p in
  assert false; (*TODO*)
  fprintf fmt "@[ :: Why Axiom @]@\n";
  fprintf fmt "@[ theorem %s:@\n @[%a@];@]@\n" id print_predicate p

let print_axiom = reprint_axiom

open Regen

module Gen = Regen.Make(
struct

  let print_element fmt e = 
    begin match e with
      | Parameter (id, c) -> print_parameter fmt id c
      | Obligation o -> print_obligation fmt o
      | Logic (id, t) -> print_logic fmt id t
      | Axiom (id, p) -> print_axiom fmt id p
      | Predicate _ -> assert false (*TODO*)
    end;
    fprintf fmt "@\n"
      
  let reprint_element fmt = function
    | Parameter (id, c) -> reprint_parameter fmt id c
    | Obligation o -> reprint_obligation fmt o
    | Logic (id, t) -> reprint_logic fmt id t
    | Axiom (id, p) -> reprint_axiom fmt id p
    | Predicate _ -> assert false (*TODO*)

  let re_oblig_loc = Str.regexp " :: Why obligation from .*"

  let environ = " vocabulary INT_1, ARYTM_1, MARGREL1, ALGSTR_1, FUNCT_1, FUNCT_4, FINSEQ_1,
  AFINSQ_1, WHY;
 notation TARSKI, SUBSET_1, ARYTM_0, XCMPLX_0, XREAL_0, REAL_1, INT_1,
  MARGREL1, ALGSTR_1, AFINSQ_1, WHY;
 constructors NAT_1, ALGSTR_1, AFINSQ_1, WHY;
 clusters XREAL_0, INT_1, WHY;
 requirements BOOLE, SUBSET, ARITHM, REAL, NUMERALS;
 theorems AXIOMS, XCMPLX_1, SQUARE_1, REAL_1, INT_1, WHY;"

  let first_time fmt =
    fprintf fmt "\
:: This file was originally generated by why.
:: It can be modified; only the generated parts will be overwritten. 

environ
%s

begin :: proof obligations start here
" (match mizar_environ with None -> environ | Some s -> s)

  let edit_below = Str.regexp "[ ]*:: EDIT BELOW THIS LINE[ ]*"
  let not_end_of_element _ s = not (Str.string_match edit_below s 0)

end)

let reset = Gen.reset

let push_obligations = 
  List.iter (fun ((_,l,_) as o) -> Gen.add_elem (Oblig, l) (Obligation o))

let push_parameter id v =
  Gen.add_elem (Param, id) (Parameter (id,v))

let _ = 
  Gen.add_regexp 
    " theorem[ ]+\\(.*_po_[0-9]+\\)[ ]*:[ ]*" Oblig;
  Gen.add_regexp 
    "(\\*Why\\*) Parameter[ ]+\\([^ ]*\\)[ ]*:[ ]*" Param

let output_file fwe =
  let f = fwe ^ "_why.miz" in
  Gen.output_file ~margin:75 f
