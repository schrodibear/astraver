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

(*i $Id: simplify.ml,v 1.34 2005-06-16 07:30:34 filliatr Exp $ i*)

(*s Simplify's output *)

open Ident
open Options
open Misc
open Error
open Logic
open Vcg
open Format
open Pp

type elem = 
  | Oblig of obligation 
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme
  | FunctionDef of string * function_def Env.scheme

let queue = Queue.create ()

let reset () = Queue.clear queue

let push_obligations = List.iter (fun o -> Queue.add (Oblig o) queue)

let push_axiom id p = Queue.add (Axiom (id, p)) queue

let push_predicate id p = Queue.add (Predicate (id, p)) queue

let push_function id p = Queue.add (FunctionDef (id, p)) queue

let defpred = Hashtbl.create 97

(*s Pretty print *)

let prefix id =
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
  else if id == t_div_int then "int_div"
  else if id == t_mod_int then "int_mod"
  (* real ops *)
  else if id == t_add_real then "add_real"
  else if id == t_sub_real then "sub_real"
  else if id == t_mul_real then "mul_real"
  else if id == t_div_real then "div_real"
  else if id == t_neg_real then "neg_real"
  else if id == t_sqrt_real then "sqrt_real"
  else if id == t_real_of_int then "real_of_int"
  else if id == t_int_of_real then "int_of_real"
  else if id == t_lt_real then "lt_real"
  else if id == t_le_real then "le_real"
  else if id == t_gt_real then "gt_real"
  else if id == t_ge_real then "ge_real"
  else assert false

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%a" Ident.print id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%d" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "|@@%b|" b
  | Tconst ConstUnit -> 
      fprintf fmt "tt" (* TODO: CORRECT? *)
  | Tconst (ConstFloat (i,f,e)) ->
      let f = if f = "0" then "" else f in
      let e = (if e = "" then 0 else int_of_string e) - String.length f in
      if e = 0 then
	fprintf fmt "(real_of_int %s%s)" i f
      else if e > 0 then
	fprintf fmt "(real_of_int (* %s%s 1%s))" i f (String.make e '0')
      else
	fprintf fmt "(div_real (real_of_int %s%s) (real_of_int 1%s))" 
	  i f (String.make (-e) '0')
  | Tderef _ -> 
      assert false
  | Tapp (id, [a; b; c], _) when id == if_then_else ->
      assert false; (* SUPPORTED IN SIMPLIFY? *)
      (*
      fprintf fmt "@[(ite@ %a@ %a@ %a)@]" print_term a print_term b
	print_term c *)
  | Tapp (id, [a; b], _) when id == access ->
      fprintf fmt "@[(select@ %a@ %a)@]" print_term a print_term b
  | Tapp (id, [a; b; c], _) when id == store ->
      fprintf fmt "@[(store@ %a@ %a@ %a)@]" 
	print_term a print_term b print_term c
  | Tapp (id, [t], _) when id == t_neg_int ->
      fprintf fmt "@[(- 0 %a)@]" print_term t
  | Tapp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, [], _) ->
      Ident.print fmt id 
  | Tapp (id, tl, _) ->
      fprintf fmt "@[(%a@ %a)@]" 
	Ident.print id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let external_type = function
  | PTexternal _ | PTarray (PTexternal _) -> true
  | _ -> false

let has_type ty fmt id = match ty with
  | PTexternal(_, ty) ->
      fprintf fmt "(EQ (IS%a %a) |@@true|)" Ident.print ty Ident.print id
  | PTarray (PTexternal(_,ty)) ->
      fprintf fmt "(FORALL (k) (EQ (IS%a (select %a k)) |@@true|))" 
	Ident.print ty Ident.print id
  | _ -> 
      assert false

let rec print_predicate pos fmt p = 
  let pp = print_predicate pos in 
  match p with
  | Ptrue ->
      fprintf fmt "TRUE"
  | Pvar id when id == default_post ->
      fprintf fmt "TRUE"
  | Pfalse ->
      fprintf fmt "FALSE"
  | Pvar id -> 
      fprintf fmt "%a" Ident.print id
  | Papp (id, [t], _) when id == well_founded ->
      fprintf fmt "TRUE ; was well_founded@\n"
  | Papp (id, [a; b], _) when is_eq id ->
      fprintf fmt "@[(EQ %a@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_neq id ->
      fprintf fmt "@[(NEQ %a@ %a)@]" print_term a print_term b
  | Papp (id, tl, _) when is_int_comparison id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[(AND (<= 0 %a)@ (< %a %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl, _) when Hashtbl.mem defpred id -> 
      fprintf fmt "@[(%a@ %a)@]" Ident.print id print_terms tl
  | Papp (id, tl, _) -> 
      fprintf fmt "@[(EQ (%a@ %a) |@@true|)@]" Ident.print id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]" (print_predicate (not pos)) a pp b
  | Piff (a, b) ->
      fprintf fmt "@[(IFF@ %a@ %a)@]" pp a pp b
  | Pif (a, b, c) ->
      fprintf fmt 
     "@[(AND@ (IMPLIES (EQ %a |@@true|) %a)@ (IMPLIES (NEQ %a |@@true|) %a))@]"
      print_term a pp b print_term a pp c
  | Pand (_, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" pp a pp b
  | Por (a, b) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" pp a pp b
  | Pnot a ->
      fprintf fmt "@[(NOT@ %a)@]" pp a
  | Forall (_, id, n, ty, p) when simplify_typing && external_type ty -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a) (IMPLIES %a@ %a))@]" 
	Ident.print id' (has_type ty) id' pp p'
  | Forall (_,id,n,_,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a)@ %a)@]" Ident.print id' pp p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(EXISTS (%a)@ %a)@]" Ident.print id' pp p'
  | Pfpi _ ->
      failwith "fpi not supported with Simplify"
  | Pnamed (n, p) when pos ->
      fprintf fmt "@[(LBLPOS@ |%s|@ %a)@]" n pp p
  | Pnamed (n, p) ->
      fprintf fmt "@[(LBLNEG@ |%s|@ %a)@]" n pp p

let cc_external_type = function
  | Cc.TTpure ty -> external_type ty
  | Cc.TTarray (Cc.TTpure (PTexternal _)) -> true
  | _ -> false

let cc_has_type ty fmt id = match ty with
  | Cc.TTpure ty when external_type ty ->
      has_type ty fmt id
  | Cc.TTarray (Cc.TTpure (PTexternal(_,ty))) ->
      fprintf fmt "(FORALL (k) (EQ (IS%a (select %a k)) |@@true|))" 
	Ident.print ty Ident.print id
  | _ -> 
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate false fmt concl
    | Svar (id, ty) :: hyps when simplify_typing && cc_external_type ty -> 
	fprintf fmt "@[(FORALL (%a) (IMPLIES %a@ %a))@]" 
	  Ident.print id (cc_has_type ty) id print_seq hyps
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[(FORALL (%a)@ %a)@]" Ident.print id print_seq hyps
    | Spred (_,p) :: hyps -> 
	fprintf fmt "@[(IMPLIES %a@ %a)@]" 
	  (print_predicate true) p print_seq hyps
  in
  print_seq fmt hyps

let print_obligation fmt (loc, o, s) = 
  fprintf fmt "@[;; %s, %a@]@\n" o Loc.report_obligation loc;
  fprintf fmt "@[<hov 2>%a@]@\n@\n" print_sequent s

let push_foralls p =
  let change = ref false in
  let split vars p =
    let vars_p = predicate_vars p in
    List.fold_left 
      (fun (in_p, out_p) ((_,_,b,_) as v) -> 
	 if Idset.mem b vars_p then v :: in_p, out_p else in_p, v :: out_p)
      ([],[]) vars
  in
  let quantify = List.fold_right (fun (w,id,b,v) p -> Forall (w,id,b,v,p)) in
  let rec push vars = function
    | Forall (w, id, b, v, p) -> 
	push ((w,id,b,v) :: vars) p
    | Pimplies (w, p1, p2) -> 
	let in_p1, out_p1 = split vars p1 in 
	if out_p1 <> [] then change := true;
	quantify in_p1 (Pimplies (w, p1, push out_p1 p2))
    | p ->
	quantify vars p
  in
  push [] p, !change

let print_axiom fmt id p =
  fprintf fmt "@[(BG_PUSH@\n ;; Why axiom %s@\n" id;
  let p = p.Env.scheme_type in
  fprintf fmt " @[<hov 2>%a@]" (print_predicate true) p;
  let p,c = push_foralls p in
  if c then fprintf fmt "@\n@\n @[<hov 2>%a@]" (print_predicate true) p;
  fprintf fmt ")@]@\n@\n" 

let print_predicate fmt id p =
  let (bl,p) = p.Env.scheme_type in
  fprintf fmt "@[(DEFPRED (%s %a) @[%a@])@]@\n@\n" id
    (print_list space (fun fmt (x,_) -> Ident.print fmt x)) bl 
    (print_predicate false) p;
  Hashtbl.add defpred (Ident.create id) ()

let print_function fmt id p =
  let (bl,_,e) = p.Env.scheme_type in
  fprintf fmt "@[(BG_PUSH@\n ;; Why function %s@\n" id;
  fprintf fmt "  @[(FORALL (%a) (EQ (%s %a) %a))@])@]@\n@\n"
    (print_list space (fun fmt (x,_) -> Ident.print fmt x)) bl 
    id
    (print_list space (fun fmt (x,_) -> Ident.print fmt x)) bl 
    print_term e

let print_elem fmt = function
  | Oblig o -> print_obligation fmt o
  | Axiom (id, p) -> print_axiom fmt id p
  | Predicate (id, p) -> print_predicate fmt id p
  | FunctionDef (id, f) -> print_function fmt id f

(* for each function symbol [f : t1,...,tn -> t] where [t] is an abstract type
   we generate an axiom 
   [FORALL (x1 ... xn) (IMPLIES (AND (ISti xi)) (ISt (f x1 ... xn)))] *)
let logic_typing fmt =
  Env.iter_global_logic
    (fun f s -> match s.Env.scheme_type with
       | Function ([], PTexternal (_,ty)) ->
	   fprintf fmt
	     "@[(BG_PUSH (EQ (IS%a %a) |@@true|))@]@\n@\n" 
	     Ident.print ty Ident.print f 
       | Function (pl, PTexternal (_,ty)) ->
	   let n = ref 0 in
	   let pl = List.map (fun pt -> incr n; "x"^string_of_int !n, pt) pl in
	   let epl = 
	     List.fold_right 
	       (fun p acc -> match p with
		  | (x, PTexternal(_,t)) -> (x, Ident.string t) :: acc
		  | _ -> acc) pl []
	   in
	   fprintf fmt
             "@[(BG_PUSH (FORALL (%a)@\n;; @[(PATS (IS%a (%a %a)))@]@\n(IMPLIES (AND %a)
               (EQ (IS%a (%a %a)) |@@true|))))@]@\n@\n"
	     (print_list space (fun fmt (x,_) -> fprintf fmt "%s" x)) pl
	     Ident.print ty Ident.print f 
	     (print_list space (fun fmt (x,_) -> fprintf fmt "%s" x)) pl
	     (print_list space (fun fmt (x,t) -> 
				  fprintf fmt "(EQ (IS%s %s) |@@true|)" t x))
	     epl
             Ident.print ty Ident.print f 
	     (print_list space (fun fmt (x,_) -> fprintf fmt "%s" x)) pl
       | Function _ | Logic.Predicate _ -> ())

let prelude = ref 
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

let output_file fwe =
  let sep = ";; DO NOT EDIT BELOW THIS LINE" in
  let f = fwe ^ "_why.sx" in
  do_not_edit f
    (fun fmt -> 
       if not no_simplify_prelude then fprintf fmt "@[%s@]@\n" !prelude)
    sep
    (fun fmt -> 
       if simplify_typing then logic_typing fmt; 
       Queue.iter (print_elem fmt) queue)

