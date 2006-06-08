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

(*i $Id: simplify.ml,v 1.48 2006-06-08 09:14:21 lescuyer Exp $ i*)

(*s Simplify's output *)

open Ident
open Options
open Misc
open Error
open Logic
open Logic_decl
open Cc
open Format
open Pp

type elem = 
  | Oblig of Loc.position * string * sequent Env.scheme
  | Axiom of string * predicate Env.scheme
  | Predicate of string * predicate_def Env.scheme
  | FunctionDef of string * function_def Env.scheme
  | PredDef of string * pure_type list

let queue = Queue.create ()

let reset () = Queue.clear queue; Encoding.reset ()

let decl_to_elem = function
  | Dgoal (loc, id, s) -> Queue.add (Oblig (loc, id, s)) queue
  | Daxiom (_, id, p) -> Queue.add (Axiom (id, p)) queue
  | Dpredicate_def (_, id, p) -> Queue.add (Predicate (id, p)) queue
  | Dfunction_def (_, id, p) -> Queue.add (FunctionDef (id, p)) queue
  | Dtype _ -> ()
  | Dlogic (_, id, logic_scheme) -> 
      (match logic_scheme.Env.scheme_type with
	Function (_,_) -> ()
      | Logic.Predicate args -> (* Queue.add (PredDef (id, args)) queue *) ())

let push_decl = 
  Encoding.push

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
  else (print_endline (Ident.string id); assert false)

let is_simplify_ident s =
  let is_simplify_char = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true 
    | _ -> false
  in
  try 
    if String.length s >= 2 && s.[0] = '_' && s.[1] = '_' then raise Exit;
    String.iter (fun c -> if not (is_simplify_char c) then raise Exit) s; true
  with Exit ->
    false

let idents fmt s =
  if is_simplify_ident s then fprintf fmt "%s" s else fprintf fmt "|%s|" s

let ident fmt id = idents fmt (Ident.string id)

let sortp fmt id = idents fmt ("IS" ^ Ident.string id)

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%a" ident id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
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
(**
  | Tapp (id, [a; b], _) when id == access ->
      fprintf fmt "@[(select@ %a@ %a)@]" print_term a print_term b
  | Tapp (id, [a; b; c], _) when id == store ->
      fprintf fmt "@[(store@ %a@ %a@ %a)@]" 
	print_term a print_term b print_term c
**)
  | Tapp (id, [t], _) when id == t_neg_int ->
      fprintf fmt "@[(- 0 %a)@]" print_term t
  | Tapp (id, tl, _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a)@]" (prefix id) print_terms tl
  | Tapp (id, [], _) ->
      ident fmt id
  | Tapp (id, tl, _) ->
      fprintf fmt "@[(%a@ %a)@]" 
	ident id (print_list space print_term) tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let external_type = function
  | PTexternal _ -> true
  | _ -> false

let has_type ty fmt id = match ty with
| PTexternal([PTexternal (_,ty)], id) when id == farray ->
    fprintf fmt "(FORALL (k) (EQ (%a (select %a k)) |@@true|))" 
      sortp ty ident id
| PTexternal(_, ty) ->
    fprintf fmt "(EQ (%a %a) |@@true|)" sortp ty ident id
| _ -> 
    assert false

let rec print_predicate pos trig fmt p = 
  let pp = print_predicate pos None in
  match p with
  | Ptrue ->
      fprintf fmt "TRUE"
  | Pvar id when id == Ident.default_post ->
      fprintf fmt "TRUE"
  | Pfalse ->
      fprintf fmt "FALSE"
  | Pvar id -> 
      fprintf fmt "%a" ident id
  | Papp (id, [], _) ->
      ident fmt id
  | Papp (id, [t], _) when id == well_founded ->
      fprintf fmt "TRUE ; was well_founded@\n"
  | Papp (id, [a; b], _) when is_eq id && trig = Some true ->
      fprintf fmt "@[(PATS %a)@]@\n@[(EQ %a@ %a)@]"
	print_term a print_term a print_term b
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
      fprintf fmt "@[(%a@ %a)@]" ident id print_terms tl
  | Papp (id, tl, _) -> 
      fprintf fmt "@[(EQ (%a@ %a) |@@true|)@]" ident id print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(IMPLIES@ %a@ %a)@]" 
	(print_predicate (not pos) None) a pp b
  | Piff (a, b) when trig = Some true ->
      (match a with Papp (id, tl, _) ->
	fprintf fmt "@[(PATS (%a %a))@]@\n@[(IFF@ %a@ %a)@]"
	  ident id print_terms tl pp a pp b
      | _ ->  fprintf fmt "@[(IFF@ %a@ %a)@]"
	    (print_predicate (not pos) None) a pp b)
  | Piff (a, b) ->
      fprintf fmt "@[(IFF@ %a@ %a)@]" pp a pp b
  | Pif (a, b, c) ->
      fprintf fmt 
     "@[(AND@ (IMPLIES (EQ %a |@@true|) %a)@ (IMPLIES (NEQ %a |@@true|) %a))@]"
      print_term a pp b print_term a pp c
  | Pand (_, _, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(AND@ %a@ %a)@]" pp a pp b
  | Por (a, b) ->
      fprintf fmt "@[(OR@ %a@ %a)@]" pp a pp b
  | Pnot a ->
      fprintf fmt "@[(NOT@ %a)@]" pp a
(*   | Forall (_, id, n, ty, p) when simplify_typing && external_type ty -> *)
(*       let id' = next_away id (predicate_vars p) in *)
(*       let p' = subst_in_predicate (subst_onev n id') p in *)
(*       fprintf fmt "@[(FORALL (%a) (IMPLIES %a@ %a))@]" *)
(* 	ident id' (has_type ty) id' pp p' *)
  | Forall (_,id,n,_,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(FORALL (%a)@ %a)@]" ident id' 
	(print_predicate pos (match trig with Some _ -> Some true | _ -> None)) p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(EXISTS (%a)@ %a)@]" ident id' pp p'
  | Pfpi _ ->
      failwith "fpi not supported with Simplify"
  | Pnamed (_, p) ->
      pp fmt p
  (** BUG Simplify
  | Pnamed (n, p) when pos ->
      fprintf fmt "@[(LBLPOS@ |%s|@ %a)@]" n pp p
  | Pnamed (n, p) ->
      fprintf fmt "@[(LBLNEG@ |%s|@ %a)@]" n pp p
  **)

let cc_external_type = function
  | Cc.TTpure ty -> external_type ty
  | Cc.TTarray (Cc.TTpure (PTexternal _)) -> true
  | _ -> false

let cc_has_type ty fmt id = match ty with
  | Cc.TTpure ty when external_type ty ->
      has_type ty fmt id
  | Cc.TTarray (Cc.TTpure (PTexternal(_,ty))) ->
      fprintf fmt "(FORALL (k) (EQ (%a (select %a k)) |@@true|))" 
	sortp ty ident id
  | _ -> 
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate false None fmt concl
(*     | Svar (id, ty) :: hyps when simplify_typing && external_type ty ->  *)
(* 	fprintf fmt "@[(FORALL (%a) (IMPLIES %a@ %a))@]"  *)
(* 	  ident id (has_type ty) id print_seq hyps *)
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[(FORALL (%a)@ %a)@]" ident id print_seq hyps
    | Spred (_,p) :: hyps -> 
	fprintf fmt "@[(IMPLIES %a@ %a)@]" 
	  (print_predicate true None) p print_seq hyps
  in
  print_seq fmt hyps

let print_obligation fmt loc o s = 
  fprintf fmt "@[;; %s, %a@]@\n" o Loc.report_obligation_position loc;
  fprintf fmt "@[<hov 2>%a@]@\n@\n" print_sequent s.Env.scheme_type

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
  let trigger = 
    let reg = Str.regexp ".*_to_.*_c" in
    if Str.string_match reg id 0 then Some false else None in
  fprintf fmt "@[(BG_PUSH@\n ;; Why axiom %s@\n" id;
  let p = p.Env.scheme_type in
  fprintf fmt " @[<hov 2>%a@]" (print_predicate true trigger) p;
  let p,c = push_foralls p in
  if c then fprintf fmt "@\n@\n @[<hov 2>%a@]" (print_predicate true trigger) p;
  fprintf fmt ")@]@\n@\n" 

let print_predicate fmt id p =
  let (bl,p) = p.Env.scheme_type in
  fprintf fmt "@[(DEFPRED (%a %a) @[%a@])@]@\n@\n" idents id
    (print_list space (fun fmt (x,_) -> ident fmt x)) bl
    (print_predicate false None) p;
  Hashtbl.add defpred (Ident.create id) ()

let print_preddef fmt id args =
  if args = [] then ()
  else
    let cpt = ref 0 in
    fprintf fmt "@[(DEFPRED (%a %a))@]@\n@\n" idents id
      (print_list space 
	 (fun fmt _ -> ident fmt (Ident.create ("x"^(string_of_int !cpt))); cpt := !cpt + 1))
      args;
    Hashtbl.add defpred (Ident.create id) ()

let idents_plus_prefix fmt s  =
  match Ident.create s with
    id when id == t_neg_int -> (* hack *)
      fprintf fmt "@[- 0@]"
  | id when is_arith id || is_relation id ->
      fprintf fmt "%s" (prefix id)
  | _ when is_simplify_ident s ->
      fprintf fmt "%s" s
  | _ ->
      fprintf fmt "|%s|" s

let print_function fmt id p =
  let (bl,pt,e) = p.Env.scheme_type in
  match bl with 
    [] -> 
      fprintf fmt "@[(BG_PUSH@\n ;; Why function %s@\n" id;
      fprintf fmt "  @[(EQ %a %a)@])@]@\n@\n" idents id	print_term e
  |_ -> 
      fprintf fmt "@[(BG_PUSH@\n ;; Why function %s@\n" id;
      fprintf fmt "  @[(FORALL (%a) (EQ (%a %a) %a))@])@]@\n@\n"
	(print_list space (fun fmt (x,_) -> ident fmt x)) bl
	idents_plus_prefix id
	(print_list space (fun fmt (x,_) -> ident fmt x)) bl 
	print_term e

let print_elem fmt = function
  | Oblig (loc, id, s) -> print_obligation fmt loc id s
  | Axiom (id, p) -> print_axiom fmt id p
  | Predicate (id, p) -> print_predicate fmt id p
  | FunctionDef (id, f) -> print_function fmt id f
  | PredDef (id, args) -> print_preddef fmt id args

(* (\* for each function symbol [f : t1,...,tn -> t] where [t] is an abstract type *)
(*    we generate an axiom  *)
(*    [FORALL (x1 ... xn) (IMPLIES (AND (ISti xi)) (ISt (f x1 ... xn)))] *\) *)
(* let logic_typing fmt = *)
(*   Env.iter_global_logic *)
(*     (fun f s -> match s.Env.scheme_type with *)
(*        | Function ([], PTexternal (_,ty)) -> *)
(* 	   fprintf fmt *)
(* 	     "@[(BG_PUSH (EQ (%a %a) |@@true|))@]@\n@\n"  *)
(* 	     sortp ty ident f  *)
(*        | Function (pl, PTexternal (_,ty)) -> *)
(* 	   let n = ref 0 in *)
(* 	   let pl = List.map (fun pt -> incr n; "x"^string_of_int !n, pt) pl in *)
(* 	   let epl =  *)
(* 	     List.fold_right  *)
(* 	       (fun p acc -> match p with *)
(* 		  | (x, PTexternal(_,t)) -> (x, Ident.string t) :: acc *)
(* 		  | _ -> acc) pl [] *)
(* 	   in *)
(* 	   fprintf fmt *)
(*              "@[(BG_PUSH (FORALL (%a)@\n;; @[(PATS (%a (%a %a)))@]@\n(IMPLIES (AND %a) *)
(*                (EQ (IS%a (%a %a)) |@@true|))))@]@\n@\n" *)
(* 	     (print_list space (fun fmt (x,_) -> fprintf fmt "%s" x)) pl *)
(* 	     sortp ty ident f  *)
(* 	     (print_list space (fun fmt (x,_) -> fprintf fmt "%s" x)) pl *)
(* 	     (print_list space  *)
(* 		(fun fmt (x,t) ->  *)
(* 		   fprintf fmt "(EQ (%a %s) |@@true|)" idents t x)) *)
(* 	     epl *)
(*              Ident.print ty ident f  *)
(* 	     (print_list space (fun fmt (x,_) -> fprintf fmt "%s" x)) pl *)
(*        | Function _ | Logic.Predicate _ -> ()) *)

let output_file fwe =
  let sep = ";; DO NOT EDIT BELOW THIS LINE" in
  let file = out_file (fwe ^ "_why.sx") in
  do_not_edit_below ~file
    ~before:(fun fmt -> ())
    ~sep
    ~after:(fun fmt -> 
   Encoding.iter decl_to_elem;
   fprintf fmt "(BG_PUSH (NEQ |@@true| |@@false|))@\n@\n";
   Queue.iter (print_elem fmt) queue)
    
