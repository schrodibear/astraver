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

(*i $Id: cvcl.ml,v 1.9 2004-07-09 15:38:29 filliatr Exp $ i*)

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

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "INT"
  | PTbool -> fprintf fmt "BOOLEAN"
  | PTreal -> fprintf fmt "REAL"
  | PTunit -> fprintf fmt "UNIT"
  | PTarray pt -> fprintf fmt "ARRAY INT OF %a" print_pure_type pt
  | PTvarid _ -> assert false
  | PTvar {type_val=Some pt} -> print_pure_type fmt pt
  | PTvar _ -> assert false
  | PTexternal (_,id) -> fprintf fmt "%a" Ident.print id

let instance fmt = function
  | [] -> 
      ()
  | ptl -> 
      let one fmt = function 
	| None -> assert false 
	| Some pt -> print_pure_type fmt pt 
      in 
      fprintf fmt "_%a" 
	(print_list (fun fmt () -> fprintf fmt "_") one) ptl

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

let print_predicate fmt id p =
  fprintf fmt "@[%%%% Why predicate %s@]@\n" id;
  let (bl,p) = p.Env.scheme_type in
  fprintf fmt "@[<hov 2>%s: [%a -> BOOLEAN] =@ LAMBDA (%a):@ @[%a@];@]@\n@\n"
    id
    (print_list space (fun fmt (_,pt) -> print_pure_type fmt pt)) bl 
    (print_list comma 
       (fun fmt (x,pt) -> 
	  fprintf fmt "%a: %a" Ident.print x print_pure_type pt )) bl 
    print_predicate p

let print_parameter fmt id c =
  fprintf fmt 
    "@[%%%% Why parameter %s@]@\n" id;
  fprintf fmt 
    "@[<hov 2>%s: %a;@]@\n@\n" id print_cc_type c

let rec print_logic_type fmt = function
  | Logic.Predicate pl ->
      fprintf fmt "[%a -> BOOLEAN]" (print_list space print_pure_type) pl
  | Function (pl, pt) ->
      fprintf fmt "[%a -> %a]" 
	(print_list space print_pure_type) pl print_pure_type pt


let print_logic fmt id t = 
  let (l,t) = Env.specialize_logic_type t in
  fprintf fmt "%%%% Why logic %s@\n@[%s: %a;@]@\n@\n" id id print_logic_type t

let print_elem fmt = function
  | Oblig o -> print_obligation fmt o
  | Axiom (id, p) -> print_axiom fmt id p
  | Predicate (id, p) -> print_predicate fmt id p
  | Logic (id, t) -> print_logic fmt id t
  | Parameter (id, t) -> print_parameter fmt id t

let prelude = ref 
(* TODO pas de polymorphisme pour array_length: que faire ? *)
"
UNIT: TYPE;
tt: UNIT;
array_length: [ARRAY INT OF INT -> INT]; %% should be polymorphic
sqrt_real: [REAL -> REAL];
int_of_real: [REAL -> INT];
mod_int: [[INT, INT] -> INT];
"
(*TODO prelude about exchange, permut and sorted
"(BG_PUSH 
  ; array_length
  (FORALL (t i v) (EQ (array_length (store t i v)) (array_length t)))
  ; booleans
  (DISTINCT |@true| |@false|)
  ; exchange
  (FORALL (t1 t2 i j)
	  (IFF (EQ (exchange t1 t2 i j) |@true|)
	       (AND (EQ (array_length t1) (array_length t2))
		    (EQ (select t1 i) (select t2 j))
		    (EQ (select t1 j) (select t2 i))
		    (FORALL (k) (IMPLIES (AND (NEQ k i) (NEQ k j))
					 (EQ (select t1 k) (select t2 k)))))))
  (FORALL (t1 t2 i j)
	  (IMPLIES (EQ (exchange t1 t2 i j) |@true|)
		   (EQ (array_length t1) (array_length t2))))
  ; permut
  (FORALL (t) (EQ (permut t t) |@true|))
  (FORALL (t1 t2) (IMPLIES (EQ (permut t1 t2) |@true|)
			   (EQ (permut t2 t1) |@true|)))
  (FORALL (t1 t2 t3) (IMPLIES (AND (EQ (permut t1 t2) |@true|)
				   (EQ (permut t2 t3) |@true|))
			      (EQ (permut t1 t3) |@true|)))
  (FORALL 
   (t i j) 
   (EQ (permut t (store (store t i (select t j)) j (select t i))) |@true|))
  (FORALL (t1 t2)
	  (IMPLIES (EQ (permut t1 t2) |@true|)
		   (EQ (array_length t1) (array_length t2))))
  ; sub_permut
  (FORALL (t g d) (EQ (sub_permut g d t t) |@true|))
  (FORALL (t1 t2 g d) (IMPLIES (EQ (sub_permut g d t1 t2) |@true|)
			   (EQ (sub_permut g d t2 t1) |@true|)))
  (FORALL (t1 t2 t3 g d) (IMPLIES (AND (EQ (sub_permut g d t1 t2) |@true|)
				       (EQ (sub_permut g d t2 t3) |@true|))
				  (EQ (sub_permut g d t1 t3) |@true|)))
  (FORALL 
   (t g d i j) 
   (IMPLIES (AND (<= g i) (<= i d) (<= g j) (<= j d))
	    (EQ (sub_permut g d t 
			    (store (store t i (select t j)) j (select t i))) 
		|@true|)))
  (FORALL 
   (t1 t2 g d i j)
   (IMPLIES (AND (EQ (exchange t1 t2 i j) |@true|)
		 (<= g i) (<= i d) (<= g j) (<= j d))
	    (EQ (sub_permut g d t1 t2) |@true|)))
  (FORALL (t1 t2 i j) 
	  (IMPLIES (EQ (sub_permut i j t1 t2) |@true|)
		   (EQ (permut t1 t2) |@true|)))
  (FORALL (t1 t2 i j)
	  (IMPLIES (EQ (sub_permut i j t1 t2) |@true|)
		   (EQ (array_length t1) (array_length t2))))
  ; sorted_array
  (FORALL 
   (t i j) 
   (IFF (EQ (sorted_array t i j) |@true|)
	(IMPLIES (<= i j)
		 (FORALL (k) (IMPLIES (AND (<= i k) (< k j))
				      (<= (select t k) (select t (+ k 1))))))))
)"
*)

let output_file fwe =
  let sep = "%%%% DO NOT EDIT BELOW THIS LINE" in
  let f = fwe ^ "_why.cvc" in
  do_not_edit f
    (fun fmt -> if not no_cvcl_prelude then fprintf fmt "@[%s@]@\n" !prelude)
    sep
    (fun fmt -> Queue.iter (print_elem fmt) queue)

