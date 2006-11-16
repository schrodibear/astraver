(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: simplify_towhy.ml,v 1.1 2006-11-16 21:14:30 filliatr Exp $ i*)

open Format
open Ident
open Pp
open Logic
open Simplify_ast

type decl = 
  | Goal of string * predicate
  | Axiom of string * predicate

let decls = Queue.create ()
let reset () = Queue.clear decls

let add_goal =
  let r = ref 0 in
  fun p -> incr r; Queue.add (Goal ("goal_" ^ string_of_int !r, p)) decls

let add_axiom =
  let r = ref 0 in
  fun p -> incr r; Queue.add (Axiom ("axiom_" ^ string_of_int !r, p)) decls

let rec translate_term = function
  | _ -> assert false

let rec translate_predicate = function
  | _ -> assert false

let translate_axiom s = add_axiom (translate_predicate s)

let translate_decl = function
  | Slist (Satom BG_PUSH :: l) -> List.iter translate_axiom l
  | Slist [Satom DEFPRED; _] -> ()
  | s -> add_goal (translate_predicate s)

let translate = List.iter translate_decl

let pure_type fmt = function
  | PTint -> fprintf fmt "int"
  | _ -> assert false

let rec print_term fmt = function
  | Tconst (ConstInt n) -> 
      fprintf fmt "%s" n
  | Tconst (ConstBool b) -> 
      fprintf fmt "%b" b
  | Tvar id | Tapp (id, [], _) -> 
      Ident.print fmt id
  | Tapp (id, [t1; t2], _) when id == t_add_int ->
      fprintf fmt "(%a + %a)" print_term t1 print_term t2
  | Tapp (id, [t1; t2], _) when id == t_sub_int ->
      fprintf fmt "(%a - %a)" print_term t1 print_term t2
  | Tapp (id, [t1; t2], _) when id == t_mul_int ->
      fprintf fmt "(%a * %a)" print_term t1 print_term t2
  | Tapp (id, [t1], _) when id == t_neg_int ->
      fprintf fmt "(-%a)" print_term t1
  | Tapp (id, tl, _) -> 
      fprintf fmt "%a(%a)" Ident.print id (print_list comma print_term) tl
  | Tderef _ | Tconst _ ->
      assert false

let int_relation_string id =
  if id == t_lt_int then "<" 
  else if id == t_le_int then "<="
  else if id == t_gt_int then ">"
  else if id == t_ge_int then ">="
  else assert false

let rec print_predicate fmt = function
  | Pvar id | Papp (id, [], _) -> 
      Ident.print fmt id
  | Papp (id, [t1; t2], _) when is_eq id ->
      fprintf fmt "(%a = %a)" print_term t1 print_term t2
  | Papp (id, [t1; t2], _) when is_neq id ->
      fprintf fmt "(%a <> %a)" print_term t1 print_term t2
  | Papp (id, [t1; t2], _) when is_int_comparison id ->
      fprintf fmt "(%a %s %a)" print_term t1 (int_relation_string id) print_term t2
  | Papp (id, l, _) ->
      fprintf fmt "%s(%a)" (Ident.string id) (print_list comma print_term) l
  | Ptrue ->
      fprintf fmt "true"
  | Pfalse ->
      fprintf fmt "false"
  | Pimplies (_, a, b) -> 
      fprintf fmt "(@[%a ->@ %a@])" print_predicate a print_predicate b
  | Piff (a, b) -> 
      fprintf fmt "(@[%a <->@ %a@])" print_predicate a print_predicate b
  | Pand (_, _, a, b) ->
      fprintf fmt "(@[%a and@ %a@])" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "(@[%a or@ %a@])" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "(not %a)" print_predicate a
  | Forall (_,_,b,v,tl,p) ->
      fprintf fmt "@[<hov 2>(forall %a:%a%a.@ %a)@]"
	Ident.print b pure_type v print_triggers tl print_predicate p
  | Exists (_,b,v,p) ->
      fprintf fmt "@[<hov 2>(exists %a:%a.@ %a)@]" 
	Ident.print b pure_type v print_predicate p
  | Pnamed (n, p) ->
      fprintf fmt "@[(%S:@ %a)@]" n print_predicate p
  | Pfpi _ | Forallb _ | Pif _ ->
      assert false

and print_pattern fmt = function
  | TPat t -> print_term fmt t
  | PPat p -> print_predicate fmt p

and print_triggers fmt = function
  | [] -> 
      ()
  | tl -> 
      fprintf fmt " [%a]" (print_list alt (print_list comma print_pattern)) tl


let print_decl fmt = function
  | Axiom (id, p) -> 
      fprintf fmt "@[<hov 2>axiom %s:@ %a@]@\n@\n" id print_predicate p 
  | Goal (id, p) ->
      fprintf fmt "@[<hov 2>goal %s:@ %a@]@\n@\n" id print_predicate p 

let translate_file f =
  reset ();
  let c = open_in f in
  let lb = Lexing.from_channel c in
  let s = Simplify_parser.start Simplify_lexer.token lb in
  close_in c;
  translate s;
  let whyf = f ^ ".why" in
  let c = open_out whyf in
  let fmt = formatter_of_out_channel c in
  Queue.iter (print_decl fmt) decls;
  fprintf fmt "@.";
  close_out c

let files = Queue.create ()
let () = Arg.parse [] (fun f -> Queue.add f files) ""
let () = Queue.iter translate_file files


