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

(*i $Id: simplify_towhy.ml,v 1.3 2006-11-16 22:22:43 filliatr Exp $ i*)

open Format
open Ident
open Pp
open Logic
open Simplify_ast

type decl = 
  | Goal of string * predicate
  | Axiom of string * predicate

let funs : (Ident.t, int) Hashtbl.t = Hashtbl.create 97
let preds = Hashtbl.create 97

let declare_fun = Hashtbl.add funs
let declare_pred = Hashtbl.add preds

let decls = Queue.create ()
let reset () = Queue.clear decls

let add_goal =
  let r = ref 0 in
  fun p -> incr r; Queue.add (Goal ("goal_" ^ string_of_int !r, p)) decls

let add_axiom =
  let r = ref 0 in
  fun p -> incr r; Queue.add (Axiom ("axiom_" ^ string_of_int !r, p)) decls

(* debug *)
let print_atom fmt = function
  | DEFPRED -> fprintf fmt "DEFPRED"
  | BG_PUSH -> fprintf fmt "BG_PUSH"
  | AT_TRUE -> fprintf fmt "AT_TRUE"
  | TRUE -> fprintf fmt "TRUE"
  | FALSE -> fprintf fmt "FALSE"
  | IMPLIES -> fprintf fmt "IMPLIES"
  | IFF -> fprintf fmt "IFF"
  | FORALL -> fprintf fmt "FORALL"
  | MPAT -> fprintf fmt "MPAT"
  | PATS -> fprintf fmt "PATS"
  | AND -> fprintf fmt "AND"
  | OR -> fprintf fmt "OR"
  | NOT -> fprintf fmt "NOT"
  | EQ -> fprintf fmt "EQ"
  | NEQ -> fprintf fmt "NEQ"
  | DISTINCT -> fprintf fmt "DISTINCT"
  | LBLPOS -> fprintf fmt "LBLPOS"
  | LBLNEG -> fprintf fmt "LBLNEG"
  | INTEGER d -> fprintf fmt "%s" d
  | IDENT s -> fprintf fmt "%s" s

let rec print_sexp fmt = function
  | Satom a -> print_atom fmt a
  | Slist l -> fprintf fmt "@[(%a)@]" (print_list space print_sexp) l

let at_true = Ident.create "at_true"

let rec translate_term = function
  | Slist [s] ->
      translate_term s
  | Satom (IDENT s) -> 
      let id = Ident.create s in
      declare_fun id 0;
      Tapp (id, [], [])
  | Slist (Satom (IDENT s) :: l) ->
      let id = Ident.create s in
      declare_fun id (List.length l);
      Tapp (id, List.map translate_term l, [])
  | Satom (INTEGER s) ->
      Tconst (ConstInt s)
  | Satom AT_TRUE ->
      Tapp (at_true, [], [])
  | Slist []
  | Slist (Slist _::_::_)
  | Slist
      (Satom
	 (LBLNEG|LBLPOS|DISTINCT|NEQ|EQ|OR|AND|PATS|MPAT|FORALL|IFF|IMPLIES|
	      FALSE|TRUE|AT_TRUE|BG_PUSH|DEFPRED|NOT)::_::_)
  | Satom
      (LBLNEG|LBLPOS|DISTINCT|NEQ|EQ|OR|AND|PATS|MPAT|FORALL|IFF|IMPLIES|FALSE|
	   TRUE|BG_PUSH|DEFPRED|NOT)
  | Slist (Satom (INTEGER _) :: _) as s ->
      Format.eprintf "%a@." print_sexp s;
      assert false

let pand p1 p2 = match p1, p2 with
  | Ptrue, p | p, Ptrue -> p
  | _ -> Pand (false, false, p1, p2)

let por p1 p2 = match p1, p2 with
  | Pfalse, p | p, Pfalse -> p
  | _ -> Por (p1, p2)

let t_distinct = Ident.create "distinct"

let foralls vl tl p =
  let rec mk_forall = function
    | [] -> assert false
    | [x] -> Forall (false, x, x, PTint, tl, p)
    | x :: xl -> Forall (false, x, x, PTint, [], mk_forall xl)
  in
  mk_forall vl

let trigger = function
  | Slist (Satom MPAT :: l) -> List.map (fun s -> TPat (translate_term s)) l
  | s -> [TPat (translate_term s)]

let variable = function
  | Satom (IDENT id) -> Ident.create id
  | _ -> assert false

let rec translate_predicate = function
  | Slist (Satom AND :: l) -> 
      List.fold_right (fun s acc -> pand (translate_predicate s) acc) l Ptrue
  | Slist (Satom OR :: l) ->	
      List.fold_right (fun s acc -> por (translate_predicate s) acc) l Pfalse
  | Slist [Satom NOT; s] ->	
      Pnot (translate_predicate s)
  | Slist (Satom NOT :: _) ->
      assert false
  | Slist [Satom EQ; s; Satom AT_TRUE] ->
      translate_predicate s
  | Slist [Satom EQ; s1; s2] ->
      Papp (t_eq, [translate_term s1; translate_term s2], [])
  | Slist (Satom EQ :: _) ->
      assert false
  | Slist [Satom NEQ; s1; s2] ->
      Papp (t_neq, [translate_term s1; translate_term s2], [])
  | Slist (Satom NEQ :: _) ->
      assert false
  | Slist (Satom (IDENT s) :: l) ->
      let id = Ident.create s in
      declare_pred id (List.length l);
      Papp (id, List.map translate_term l, [])
  | Slist [Satom IMPLIES; s1; s2] ->
      Pimplies (false, translate_predicate s1, translate_predicate s2)
  | Slist (Satom IMPLIES :: _) ->
      assert false
  | Slist [Satom IFF; s1; s2] ->
      Piff (translate_predicate s1, translate_predicate s2)
  | Slist (Satom IFF :: _) ->
      assert false
  | Slist [s] ->
      translate_predicate s
  | Slist (Satom DISTINCT :: l) ->
      Papp (t_distinct, List.map translate_term l, [])
  | Slist [Satom FORALL; Slist vl; Slist (Satom PATS :: tl); s] ->
      let vl = List.map variable vl in
      let tl = List.map trigger tl in
      foralls vl tl (translate_predicate s)
  | Slist [Satom FORALL; Slist vl; s] ->
      let vl = List.map variable vl in
      foralls vl [] (translate_predicate s)
  | Slist (Satom FORALL :: _ ) ->
      assert false
  | Slist [Satom (LBLPOS | LBLNEG); _; s] ->
      translate_predicate s
  | Slist (Satom (LBLPOS | LBLNEG) :: _) ->
      assert false
  | Satom TRUE ->
      Ptrue
  | Satom FALSE ->
      Pfalse
  | Satom (IDENT s) ->
      let id = Ident.create s in
      declare_pred id 0;
      Papp (id, [], [])
  | Slist ([] | 
           Slist _ :: _ | 
           Satom (PATS | MPAT | BG_PUSH | DEFPRED | AT_TRUE) :: _) 
  | Slist (Satom (FALSE|TRUE | INTEGER _)::_::_)
  | Satom (PATS | MPAT | BG_PUSH | DEFPRED | AT_TRUE | INTEGER _)
  | Satom (LBLNEG|LBLPOS|DISTINCT|NEQ|EQ|OR|AND|FORALL|IFF|IMPLIES|NOT) ->
      assert false

let translate_axiom s = add_axiom (translate_predicate s)

let translate_decl = function
  | Slist [Satom BG_PUSH; Slist (Satom AND :: l)]
  | Slist (Satom BG_PUSH :: l) -> 
      List.iter translate_axiom l
  | Slist [Satom DEFPRED; _] -> 
      ()
  | s -> 
      add_goal (translate_predicate s)

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
      fprintf fmt "@[(%a ->@ %a)@]" print_predicate a print_predicate b
  | Piff (a, b) -> 
      fprintf fmt "@[(%a <->@ %a)@]" print_predicate a print_predicate b
  | Pand (_, _, a, b) ->
      fprintf fmt "@[(%a and@ %a)@]" print_predicate a print_predicate b
  | Por (a, b) ->
      fprintf fmt "@[(%a or@ %a)@]" print_predicate a print_predicate b
  | Pnot a ->
      fprintf fmt "@[(not@ %a)@]" print_predicate a
  | Forall (_,_,b,v,tl,p) ->
      fprintf fmt "@[<hov 2>(forall@ %a:%a%a.@ %a)@]"
	Ident.print b pure_type v print_triggers tl print_predicate p
  | Exists (_,b,v,p) ->
      fprintf fmt "@[<hov 2>(exists@ %a:%a.@ %a)@]" 
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
      fprintf fmt "@ [%a]" (print_list alt (print_list comma print_pattern)) tl


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


