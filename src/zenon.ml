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

(*i $Id: zenon.ml,v 1.5 2006-03-07 09:39:41 filliatr Exp $ i*)

(*s Zenon output *)

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
  | FunctionDef of string * function_def Env.scheme

let queue = Queue.create ()

let push_parameter id v = Queue.add (Parameter (id, v)) queue

let push_logic id t = Queue.add (Logic (id, t)) queue

let push_obligations = List.iter (fun o -> Queue.add (Oblig o) queue)

let push_axiom id p = Queue.add (Axiom (id, p)) queue

let push_predicate id p = Queue.add (PredicateDef (id, p)) queue

let push_function id p = Queue.add (FunctionDef (id, p)) queue

(*s Pretty print *)

let is_zenon_keyword =
  let ht = Hashtbl.create 17 in
  List.iter (fun kw -> Hashtbl.add ht kw ()) 
    ["True"; "False"];
  Hashtbl.mem ht

let is_zenon_ident s =
  let is_zenon_char = function
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true 
    | _ -> false
  in
  try 
    String.iter (fun c -> if not (is_zenon_char c) then raise Exit) s; true
  with Exit ->
    false

let renamings = Hashtbl.create 17
let fresh_name = 
  let r = ref 0 in fun () -> incr r; "zenon__" ^ string_of_int !r

let rename s =
  if is_zenon_keyword s then
    "zenon__" ^ s
  else if not (is_zenon_ident s) then begin
    try
      Hashtbl.find renamings s
    with Not_found ->
      let s' = fresh_name () in
      Hashtbl.add renamings s s';
      s'
  end else
    s

let ident fmt id = fprintf fmt "%s" (rename (string id))
let idents fmt s = fprintf fmt "%s" (rename s)

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
  | PTexternal _ -> true
  | _ -> false

let rec print_pure_type fmt = function
  | PTint -> fprintf fmt "INT"
  | PTbool -> fprintf fmt "BOOLEAN"
  | PTreal -> fprintf fmt "REAL"
  | PTunit -> fprintf fmt "UNIT"
  | PTexternal ([pt], id) when id == farray -> 
      fprintf fmt "ARRAY_%a" print_pure_type pt
  | PTvar {type_val=Some pt} -> print_pure_type fmt pt
  | PTvar _ -> assert false
  | PTexternal (i,id) -> fprintf fmt "%a%a" ident id instance i

and instance fmt = function
  | [] -> ()
  | ptl -> fprintf fmt "_%a" (print_list underscore print_pure_type) ptl

let rec print_term fmt = function
  | Tvar id -> 
      fprintf fmt "%a" ident id
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool true) -> 
      fprintf fmt "true"
  | Tconst (ConstBool false) -> 
      fprintf fmt "false"
  | Tconst ConstUnit -> 
      fprintf fmt "tt" (* TODO: CORRECT? *)
  | Tconst (ConstFloat (i,f,e)) ->
      let f = if f = "0" then "" else f in
      let e = (if e = "" then 0 else int_of_string e) - String.length f in
      if e = 0 then
	fprintf fmt "%s%s" i f
      else if e > 0 then
	fprintf fmt "(* %s%s 1%s)" i f (String.make e '0')
      else
	fprintf fmt "(/ %s%s 1%s)" i f (String.make (-e) '0')
  | Tderef _ -> 
      assert false
  | Tapp (id, ([_;_] as tl), _) when id == t_mod_int ->
      fprintf fmt "@[(%a %a)@]" ident id print_terms tl
  | Tapp (id, [a], _) when id == t_sqrt_real || id == t_int_of_real ->
      fprintf fmt "@[(%a %a)@]" ident id print_term a
  | Tapp (id, [a], _) when id == t_real_of_int ->
      fprintf fmt "@[(%a %a)@]" ident id print_term a
  | Tapp (id, [a; b; c], _) when id == if_then_else ->
      fprintf fmt "@[(ITE %a@ %a@ %a)@]" 
	print_term a print_term b print_term c
  | Tapp (id, [a; b], _) when id == access ->
      fprintf fmt "@[(access@ %a@ %a)@]" print_term a print_term b
  | Tapp (id, [a; b; c], _) when id == store ->
      fprintf fmt "@[(update@ %a@ %a@ %a)@]" 
	print_term a print_term b print_term c
  | Tapp (id, [t], _) when id == t_neg_int || id == t_neg_real ->
      fprintf fmt "@[(- 0 %a)@]" print_term t
  | Tapp (id, [a;b], _) when is_relation id || is_arith id ->
      fprintf fmt "@[(%s %a %a)@]" (infix id) print_term a print_term b
  | Tapp (id, [], i) ->
      fprintf fmt "%a%a" ident id instance i
  | Tapp (id, tl, i) ->
      fprintf fmt "@[(%a%a %a)@]" ident id instance i print_terms tl

and print_terms fmt tl = 
  print_list space print_term fmt tl

let rec print_predicate fmt = function
  | Ptrue ->
      fprintf fmt "True"
  | Pvar id when id == Ident.default_post ->
      fprintf fmt "True"
  | Pfalse ->
      fprintf fmt "False"
  | Pvar id -> 
      fprintf fmt "%a" ident id
  | Papp (id, [t], _) when id == well_founded ->
      fprintf fmt "True ;; was well_founded@\n"
  | Papp (id, [a; b], _) when id == t_eq_bool ->
      fprintf fmt "@[(= %a@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when id == t_neq_bool ->
      fprintf fmt "@[(-. (= %a@ %a))@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_eq id ->
      fprintf fmt "@[(= %a@ %a)@]" print_term a print_term b
  | Papp (id, [a; b], _) when is_neq id ->
      fprintf fmt "@[(-. (= %a@ %a))@]" print_term a print_term b
  | Papp (id, [a;b], _) when is_int_comparison id || is_real_comparison id ->
      fprintf fmt "@[(%s %a %a)@]" (infix id) print_term a print_term b
  | Papp (id, [a;b], _) when id == t_zwf_zero ->
      fprintf fmt "@[(/\\ (<= 0 %a)@ (< %a %a))@]" 
	print_term b print_term a print_term b
  | Papp (id, tl, i) -> 
      fprintf fmt "@[(%a%a@ %a)@]" ident id instance i print_terms tl
  | Pimplies (_, a, b) ->
      fprintf fmt "@[(=> %a@ %a)@]" print_predicate a print_predicate b
  | Piff (a, b) ->
      fprintf fmt "@[(<=> %a@ %a)@]" print_predicate a print_predicate b
  | Pif (a, b, c) ->
      fprintf fmt 
     "@[(/\\ (=> (= %a true) %a)@ (=> (= %a false) %a))@]"
      print_term a print_predicate b print_term a print_predicate c
  | Pand (_, _, a, b) | Forallb (_, a, b) ->
      fprintf fmt "@[(/\\ %a@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(\\/ %a@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(-.@ %a)@]" print_predicate a
  | Forall (_,id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(A. ((%a \"%a\")@ %a))@]" 
	ident id' print_pure_type t print_predicate p'
  | Exists (id,n,t,p) -> 
      let id' = next_away id (predicate_vars p) in
      let p' = subst_in_predicate (subst_onev n id') p in
      fprintf fmt "@[(E. ((%a \"%a\")@ %a))@]" 
	ident id' print_pure_type t print_predicate p'
  | Pfpi _ ->
      failwith "fpi not supported with Zenon"
  | Pnamed (_, p) -> (* TODO: print name *)
      print_predicate fmt p

let cc_external_type = function
  | Cc.TTpure ty -> external_type ty
  | Cc.TTarray (Cc.TTpure (PTexternal _)) -> true
  | _ -> false

let rec print_cc_type fmt = function
  | TTpure pt -> 
      print_pure_type fmt pt
  | TTarray v -> 
      fprintf fmt "(@[ARRAY_%a@])" print_cc_type v
  | _ -> 
      assert false

let print_sequent fmt (hyps,concl) =
  let rec print_seq fmt = function
    | [] ->
	print_predicate fmt concl
    | Svar (id, v) :: hyps -> 
	fprintf fmt "@[(A. ((%a \"%a\")@ %a))@]" 
	  ident id print_cc_type v print_seq hyps
    | Spred (_,p) :: hyps -> 
	fprintf fmt "@[(=> %a@ %a)@]" print_predicate p print_seq hyps
  in
  print_seq fmt hyps

let rec print_logic_type fmt = function
  | Predicate [] ->
      fprintf fmt "prop"
  | Predicate [pt] ->
      fprintf fmt "%a -> prop" print_pure_type pt
  | Predicate pl ->
      fprintf fmt "%a -> prop)" (print_list comma print_pure_type) pl
  | Function ([], pt) ->
      print_pure_type fmt pt
  | Function ([pt1], pt2) ->
      fprintf fmt "%a -> %a" print_pure_type pt1 print_pure_type pt2
  | Function (pl, pt) ->
      fprintf fmt "%a -> %a" 
	(print_list comma print_pure_type) pl print_pure_type pt

module Mono = struct

  let declare_type fmt pt = 
    fprintf fmt "@[;; type %a@]@\n@\n" print_pure_type pt

  let print_parameter fmt id c =
    fprintf fmt 
      "@[;; Why parameter %a@]@\n" idents id;
    fprintf fmt 
      "@[<hov 2>;;  %a: %a@]@\n@\n" idents id print_cc_type c

  let print_logic_instance fmt id i t =
    fprintf fmt ";; Why logic %a@\n" idents id;
    fprintf fmt "@[;; %a%a: %a@]@\n@\n" idents id instance i print_logic_type t

  let print_predicate_def_instance fmt id i (bl,p) =
    fprintf fmt "@[;; Why predicate %a@]@\n" idents id;
    fprintf fmt "@[<hov 2>\"%a%a\" " idents id instance i;
    List.iter (fun (x,_) -> fprintf fmt "(A. ((%a)@ " ident x) bl;
    fprintf fmt "(<=> (%a%a %a)@ %a)" 
      idents id instance i
      (print_list space (fun fmt (x,_) -> fprintf fmt "%a" ident x)) bl
      print_predicate p;
    List.iter (fun _ -> fprintf fmt "))") bl;
    fprintf fmt "@]@\n"

  let print_function_def_instance fmt id i (bl,t,e) =
    fprintf fmt "@[;; Why function %a@]@\n" idents id;
    fprintf fmt "@[<hov 2>\"%a%a\" " idents id instance i;
    List.iter (fun (x,_) -> fprintf fmt "(A. ((%a)@ " ident x) bl;
    fprintf fmt "(= (%a%a %a)@ %a)" 
      idents id instance i
      (print_list space (fun fmt (x,_) -> fprintf fmt "%a" ident x)) bl
      print_term e;
    List.iter (fun _ -> fprintf fmt "))@]@\n") bl;
    fprintf fmt "@]@\n"

  let print_axiom_instance fmt id i p =
    fprintf fmt "@[;; Why axiom %s@]@\n" id;
    fprintf fmt "@[<hov 2>\"%s\" %a@]@\n@\n" id print_predicate p

  let print_obligation fmt (loc, o, s) = 
    fprintf fmt "@[;; %s, %a@]@\n" o Loc.report_obligation_position loc;
    fprintf fmt "@[<hov 2>$goal %a@]@\n\n" print_sequent s

end

module Output = Monomorph.Make(Mono)

let print_elem fmt = function
  | Oblig o -> Output.print_obligation fmt o
  | Axiom (id, p) -> Output.print_axiom fmt id p
  | PredicateDef (id, p) -> Output.print_predicate_def fmt id p
  | FunctionDef (id, p) -> Output.print_function_def fmt id p
  | Logic (id, t) -> Output.print_logic fmt id t
  | Parameter (id, t) -> Output.print_parameter fmt id t

let prelude_done = ref false
let prelude fmt = 
  if not !prelude_done then begin
    prelude_done := true;
    fprintf fmt "
;; Zenon prelude
"
  end

let reset () = Queue.clear queue; Output.reset ()

let output_file fwe =
  let sep = ";; DO NOT EDIT BELOW THIS LINE" in
  let file = fwe ^ "_why.znn" in
  do_not_edit_below ~file
    ~before:prelude
    ~sep
    ~after:(fun fmt -> Queue.iter (print_elem fmt) queue)

