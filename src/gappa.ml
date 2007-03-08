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

(*i $Id: gappa.ml,v 1.11 2007-03-08 10:00:23 filliatr Exp $ i*)

(*s Gappa's output *)

open Ident
open Options
open Misc
open Error
open Logic
open Cc
open Format
open Pp

(* Gappa terms and formulas *)

type exact = Exact | Double

type mode = Mnearest_even

type gterm =
  | Gvar of exact * string
  | Grnd of exact * mode * gterm
  | Gcst of real_constant
  | Gneg of gterm
  | Gadd of gterm * gterm
  | Gsub of gterm * gterm
  | Gmul of gterm * gterm
  | Gdiv of gterm * gterm
  | Gabs of gterm

type gpred =
  | Gle of gterm * real_constant
  | Gge of gterm * real_constant
  | Gin of gterm * real_constant * real_constant
  | Gimplies of gpred * gpred
  | Gand of gpred * gpred
  | Gor of gpred * gpred
  | Gnot of gpred

type gobligation = (string * gterm) list * gpred

exception NotGappa

(* compilation to Gappa formulas *)

let real_of_int = Ident.create "real_of_int"

let nearest_even = Ident.create "nearest_even"

let t_double = Ident.create "double"
let neg_double = Ident.create "neg_double"
let add_double = Ident.create "add_double"
let sub_double = Ident.create "sub_double"
let mul_double = Ident.create "mul_double"
let div_double = Ident.create "div_double"
let d_to_r = Ident.create "d_to_r"
let r_to_d = Ident.create "r_to_d"

let mode = function
  | Tapp (id, [], _) | Tvar id when id == nearest_even ->
      Mnearest_even
  | _ ->
      raise NotGappa

let rec term e = function
  | Tconst (ConstFloat f) -> 
      Gcst f
  | Tconst (ConstInt n) ->
      Gcst (n, "0", "")
  | Tconst _ ->
      raise NotGappa
  | Tvar id -> 
      Gvar (e, Ident.string id)
  | Tderef id -> 
      Gvar (e, Ident.string id)
  (* real ops *)
  | Tapp (id, [t], _) when id == t_neg_real -> 
      Gneg (term e t)
  | Tapp (id, [t1; t2], _) when id == t_add_real -> 
      Gadd (term e t1, term e t2)
  | Tapp (id, [t1; t2], _) when id == t_sub_real -> 
      Gsub (term e t1, term e t2)
  | Tapp (id, [t1; t2], _) when id == t_mul_real -> 
      Gmul (term e t1, term e t2)
  | Tapp (id, [t1; t2], _) when id == t_div_real -> 
      Gdiv (term e t1, term e t2)
  (* float ops *)
  | Tapp (id, [m; t], _) when id == neg_double -> 
      Grnd (e, mode m, Gneg (term e t))
  | Tapp (id, [m; t1; t2], _) when id == add_double -> 
      Grnd (e, mode m, Gadd (term e t1, term e t2))
  | Tapp (id, [m; t1; t2], _) when id == sub_double -> 
      Grnd (e, mode m, Gsub (term e t1, term e t2))
  | Tapp (id, [m; t1; t2], _) when id == mul_double -> 
      Grnd (e, mode m, Gmul (term e t1, term e t2))
  | Tapp (id, [m; t1; t2], _) when id == div_double -> 
      Grnd (e, mode m, Gdiv (term e t1, term e t2))
  (* conversions *)
  | Tapp (id, [t], _) when id == real_of_int ->
      term Exact t
  | Tapp (id, [t], _) when id == d_to_r ->
      term Double t
  | Tapp (id, [m; t], _) when id == r_to_d ->
      Grnd (Double, mode m, term Exact t)
  (* anything else is discarded *)
  | Tapp _ -> 
      raise NotGappa

let termo e t = try Some (term e t) with NotGappa -> None

(* recognition of a Gappa predicate *)

let rec gpred = function
  | Papp (id, [t1; t2], _) when id == t_le_real ->
      begin match termo Exact t1, termo Exact t2 with
	| Some (Gcst c1), Some t2 -> Some (Gge (t2, c1))
	| Some t1, Some (Gcst c2) -> Some (Gle (t1, c2))
	| _ -> None
      end
  | Pand (_, _, 
	  Papp (id1, [Tconst (ConstFloat f1); t1], _),
	  Papp (id2, [t2; Tconst (ConstFloat f2)], _))
    when id1 == t_le_real && id2 == t_le_real && t1 = t2 ->
      begin try Some (Gin (term Double t1, f1, f2)) with NotGappa -> None end
  | Pand (_, _, p1, p2) ->
      begin match gpred p1, gpred p2 with
	| Some p1, Some p2 -> Some (Gand (p1, p2))
	| (Some p as v), None | None, (Some p as v) -> v
	| None, None -> None
      end
  | Por (p1, p2) ->
      begin match gpred p1, gpred p2 with
	| Some p1, Some p2 -> Some (Gor (p1, p2))
	| _ -> None
      end
  | Pimplies (_, p1, p2) ->
      begin match gpred p1, gpred p2 with
	| Some p1, Some p2 -> Some (Gimplies (p1, p2))
	| _ -> None
      end
  | Pnamed (_, p) ->
      gpred p
  | Forall _ 
  | Papp _
  | Pif _
  | Piff _
  | Pnot _
  | Forallb _
  | Exists _
  | Pfpi _
  | Ptrue | Pfalse | Pvar _ -> (* discarded *)
      None

(* extraction of a list of equalities and possibly a Gappa predicate *)

let rec ghyp = function
  | Papp (id, [Tvar x; t2], _) when is_eq id ->
      [(Ident.string x, term Double t2)], None
  | p ->
      [], gpred p

(* Processing obligations.
   One Why obligation can be split into several Gappa obligations *)

let queue = Queue.create ()

let reset () = Queue.clear queue

let add_ctx_vars =
  List.fold_left 
    (fun acc -> function Svar (id,_) -> Idset.add id acc | _ -> acc)

let rec intros ctx = function
  | Forall (true, id, n, t, _, p) ->
      (*let id' = next_away id (predicate_vars p) in*)
      let id' = next_away id (add_ctx_vars (predicate_vars p) ctx) in
      let p' = subst_in_predicate (subst_onev n id') p in
      intros (Svar (id', t) :: ctx) p'
  | Pimplies (true, a, b) -> 
      let h = fresh_hyp () in 
      intros (Spred (h, a) :: ctx) b
  | Pnamed (_, p) ->
      intros ctx p
  | c -> 
      ctx, c

let gands = function
  | [] -> assert false
  | p0 :: l -> List.fold_right (fun p acc -> Gand (p, acc)) l p0

let gimplies l p = match l with
  | [] -> p
  | _ -> Gimplies (gands l, p)

let process_obligation (ctx, concl) =
  let ctx,concl = intros ctx concl in
  match gpred concl with
    | None -> (* goal is not a gappa prop *)
	if debug then Format.eprintf "not a gappa prop; skipped@."
    | Some p ->
	let el,pl = 
	  List.fold_left 
	    (fun ((el,pl) as acc) h -> match h with
	      | Svar _ -> acc
	      | Spred (_, p) -> 
		  let ep,pp = ghyp p in
		  let pl = match pp with None -> pl | Some pp -> pp::pl in
		  ep :: el, pl)
	    ([],[]) ctx
	in
	let gconcl = gimplies pl p in
	Queue.add (List.flatten el, gconcl) queue

let push_decl = function
  | Logic_decl.Dgoal (_,_,s) -> process_obligation s.Env.scheme_type
  | _ -> ()

let print_real fmt = function
  | (i,f,"") -> fprintf fmt "%s.%s" i f
  | (i,f,e) -> fprintf fmt "%s.%se%s" i f e

let rec print_term fmt = function
  | Gvar (Double, x) -> fprintf fmt "%s" x
  | Gvar (Exact, x) -> fprintf fmt "exact_%s" x
  | Grnd (Exact, _, t) -> print_term fmt t
  | Grnd (Double, Mnearest_even, t) -> fprintf fmt "dne(%a)" print_term t
  | Gcst r -> print_real fmt r
  | Gneg t -> fprintf fmt "(-%a)" print_term t
  | Gadd (t1, t2) -> fprintf fmt "(%a + %a)" print_term t1 print_term t2
  | Gsub (t1, t2) -> fprintf fmt "(%a - %a)" print_term t1 print_term t2
  | Gmul (t1, t2) -> fprintf fmt "(%a * %a)" print_term t1 print_term t2
  | Gdiv (t1, t2) -> fprintf fmt "(%a / %a)" print_term t1 print_term t2
  | Gabs t -> fprintf fmt "|%a|" print_term t

let rec print_pred fmt = function
  | Gle (t, r1) ->
      fprintf fmt "%a <= %a" print_term t print_real r1
  | Gge (t, r1) ->
      fprintf fmt "%a >= %a" print_term t print_real r1
  | Gin (t, r1, r2) ->
      fprintf fmt "%a in [%a, %a]" print_term t print_real r1 print_real r2
  | Gimplies (p1, p2) ->
      fprintf fmt "(%a ->@ %a)" print_pred p1 print_pred p2
  | Gand (p1, p2) ->
      fprintf fmt "(%a /\\ %a)" print_pred p1 print_pred p2
  | Gor (p1, p2) ->
      fprintf fmt "(%a \\/ %a)" print_pred p1 print_pred p2
  | Gnot p ->
      fprintf fmt "(not %a)" print_pred p

let print_equation fmt (x, t) = 
  fprintf fmt "@[%s = %a;@]@\n" x print_term t

let print_obligation fmt (eq,p) =
  fprintf fmt "@@dne = float<ieee_64, ne>;@\n@\n";
  fprintf fmt "%a@\n" (print_list newline print_equation) eq;
  fprintf fmt "@[{ %a }@]@." print_pred p

let output_file fwe =
  let sep = "### DO NOT EDIT ABOVE THIS LINE" in
  let i = ref 0 in
  Queue.iter
    (fun o ->
       incr i;
       if debug then eprintf "gappa obligation %d@." !i;
       let file = fwe ^ "_why_po_" ^ string_of_int !i ^ ".gappa" in
       do_not_edit_above ~file
	 ~before:(fun fmt -> print_obligation fmt o)
	 ~sep
	 ~after:(fun fmt -> ()))
    queue


