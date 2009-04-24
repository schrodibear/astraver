(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2009                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Guillaume MELQUIOND                                                 *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: gappa.ml,v 1.39 2009-04-24 15:55:17 melquion Exp $ i*)

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

(* fields of the float model *)
type float_field = Rounded | Exact | Model
(* formats of the float model *)
type float_fmt = Single | Double
(* modes of the float model *)
type mode = RndNE | RndZR | RndUP | RndDN | RndNA

type gterm =
  | Gvar of string
  | Gfld of float_field * string
  | Grnd of float_fmt * mode * gterm
  | Gcst of string
  | Gneg of gterm
  | Gadd of gterm * gterm
  | Gsub of gterm * gterm
  | Gmul of gterm * gterm
  | Gdiv of gterm * gterm
  | Gabs of gterm

type gpred =
  | Gle of gterm * string
  | Gge of gterm * string
  | Gin of gterm * string * string
  | Gimplies of gpred * gpred
  | Gand of gpred * gpred
  | Gor of gpred * gpred
  | Gnot of gpred

type gobligation = (string * gterm) list * gpred

exception NotGappa

(* compilation to Gappa formulas *)

let real_of_int = Ident.create "real_of_int"

let rnd_ne = Ident.create "nearest_even"
let rnd_zr = Ident.create "to_zero"
let rnd_up = Ident.create "up"
let rnd_dn = Ident.create "down"
let rnd_na = Ident.create "nearest_away"

let max_gen_float = Ident.create "max_gen_float"
let round_float = Ident.create "round_float"

let float_value = Ident.create "float_value"
let exact_value = Ident.create "exact_value"
let model_value = Ident.create "model_value"

let fmt_single = Ident.create "Single"
let fmt_double = Ident.create "Double"

let is_int_constant = function
  | Tconst (ConstInt _) -> true
  | Tapp (id, [Tconst (ConstInt _)], _) when id == t_neg_int -> true
  | _ -> false

let eval_int_constant = function
  | Tconst (ConstInt n) -> n
  | Tapp (id, [Tconst (ConstInt n)], _) when id == t_neg_int -> "-"^n
  | _ -> assert false

let is_pos_constant = function
  | Tconst (ConstInt _) -> true
  | Tconst (ConstFloat _) -> true
  | Tapp (id, [Tconst (ConstInt _)], _) when id == real_of_int -> true
  | Tapp (id, [Tapp (id', [], _)], _) when id == max_gen_float &&
      (id' == fmt_single || id' == fmt_double) -> true
  | _ -> false

let is_constant = function
  | t when is_int_constant t -> true
  | t when is_pos_constant t -> true
  | Tapp (id, [t], _) when id == real_of_int && is_int_constant t -> true
  | Tapp (id, [t], _) when id == t_neg_real  && is_pos_constant t -> true
  | _ -> false

let eval_rconst = function
  | RConstDecimal (i, f, None)   -> Printf.sprintf "%s.%s"      i f
  | RConstDecimal (i, f, Some e) -> Printf.sprintf "%s.%se%s"   i f e
  | RConstHexa (i, f, e)         -> Printf.sprintf "0x%s.%sp%s" i f e

let eval_pos_constant = function
  | Tconst (ConstInt n) -> n
  | Tconst (ConstFloat f) -> eval_rconst f
  | Tapp (id, [Tconst (ConstInt n)], _) when id == real_of_int -> "-" ^ n
  | Tapp (id, [Tapp (id', [], _)], _) when id == max_gen_float ->
      if id' == fmt_single then "0x1.FFFFFEp127" else
      if id' == fmt_double then "0x1.FFFFFFFFFFFFFp1023" else
      raise NotGappa
  | _ -> raise NotGappa

let eval_constant = function
  | t when is_int_constant t -> eval_int_constant t
  | t when is_pos_constant t -> eval_pos_constant t
  | Tapp (id, [t], _) when id == real_of_int && is_int_constant t
      -> eval_int_constant t
  | Tapp (id, [t], _) when id == t_neg_real  && is_pos_constant t
      -> "-" ^ (eval_pos_constant t)
  | _ -> raise NotGappa

let field_of_id s =
  if s == float_value then Rounded else
  if s == exact_value then Exact else
  if s == model_value then Model else
  assert false

(* contains all the terms that have been generalized away,
   because they were not recognized *)
let gen_table = Hashtbl.create 10

(* contains the terms associated to variables, especially gen_float variables *)
let var_table = Hashtbl.create 10

(* contains the roundings used *)
let rnd_table = Hashtbl.create 10

(* contains the names already defined,
   so new definitions should be as equalities *)
let def_table = Hashtbl.create 10

let rec term = function
  | t when is_constant t ->
      Gcst (eval_constant t)
  | Tconst _ ->
      raise NotGappa
  | Tvar id ->
    begin
      try
        Hashtbl.find var_table id
      with Not_found ->
        Gvar (Ident.string id)
    end
  | Tderef id ->
      Gvar (Ident.string id)
  (* int and real ops *)
  | Tapp (id, [t], _) when id == t_neg_real || id = t_neg_int ->
      Gneg (term t)
  | Tapp (id, [t], _) when id == t_abs_real ->
      Gabs (term t)
  | Tapp (id, [t1; t2], _) when id == t_add_real || id = t_add_int ->
      Gadd (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_sub_real || id = t_sub_int ->
      Gsub (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_mul_real || id = t_mul_int ->
      Gmul (term t1, term t2)
  | Tapp (id, [t1; t2], _) when id == t_div_real ->
      Gdiv (term t1, term t2)
  (* conversions *)
  | Tapp (id, [t], _) when id == real_of_int ->
      term t
  (* [Jessie] rounding *)
  | Tapp (id, [Tapp (fmt, [], _); Tapp (m, [], _); t], _)
      when id = round_float ->
      let fmt =
        if fmt == fmt_single then Single else
        if fmt == fmt_double then Double else
        raise NotGappa in
      let mode =
        if m == rnd_ne then RndNE else
        if m == rnd_zr then RndZR else
        if m == rnd_up then RndUP else
        if m == rnd_dn then RndDN else
        if m == rnd_na then RndNA else
        raise NotGappa in
      Hashtbl.replace rnd_table (fmt, mode) ();
      Grnd (fmt, mode, term t)
  | Tapp (id, [Tvar _ as x], _)
      when (id == float_value || id == exact_value || id == model_value) ->
    begin
      match term x with
        | Gvar v -> Gfld (field_of_id id, v)
        | _ -> raise NotGappa
    end
  (* anything else is generalized as a fresh variable *)
  | Tapp _ as t ->
      Gvar (
        try
          Hashtbl.find gen_table t
        with Not_found ->
          let n = Ident.string (fresh_var ()) in
          Hashtbl.replace gen_table t n;
          n
        )
  | Tnamed(_,t) -> term t

let termo t = try Some (term t) with NotGappa -> None

let gando = function
  | Some p1, Some p2 -> Some (Gand (p1, p2))
  | (Some p as v), None | None, (Some p as v) -> v
  | None, None -> None

(* recognition of a Gappa predicate *)

let rec gpred def = function
  | Papp (id, [t1; t2], _) when id == t_le_real || id == t_le_int ->
      begin match termo t1, termo t2 with
	| Some (Gcst c1), Some t2 -> Some (Gge (t2, c1))
	| Some t1, Some (Gcst c2) -> Some (Gle (t1, c2))
        | Some t1, Some t2 -> Some (Gle (Gsub (t1, t2), "0"))
	| _ -> None
      end
  | Papp (id, [t1; t2], _) when id == t_ge_real || id == t_ge_int ->
      begin match termo t1, termo t2 with
	| Some (Gcst c1), Some t2 -> Some (Gle (t2, c1))
	| Some t1, Some (Gcst c2) -> Some (Gge (t1, c2))
        | Some t1, Some t2 -> Some (Gge (Gsub (t1, t2), "0"))
	| _ -> None
      end
  | Pand (_, _, Papp (id1, [f1; t1], _), Papp (id2, [t2; f2], _))
    when (id1 == t_le_real || id1 == t_le_int) && (id2 == t_le_real || id2 == t_le_int)
    && t1 = t2 && is_constant f1 && is_constant f2 ->
    begin 
      try Some (Gin (term t1, eval_constant f1, eval_constant f2))
      with NotGappa -> None
    end
  | Papp (id, [t1; t2], _) when is_eq id ->
      begin match termo t1, termo t2 with
        | Some (Gcst c1), Some t2 -> Some (Gin (t2, c1, c1))
        | Some t1, Some (Gcst c2) -> Some (Gin (t1, c2, c2))
        | Some t1, Some t2 -> Some (Gin (Gsub (t1, t2), "0", "0"))
        | _ -> None
      end
  | Papp (id, [t1; t2], _) when is_neq id ->
      begin match termo t1, termo t2 with
        | Some (Gcst c1), Some t2 -> Some (Gnot (Gin (t2, c1, c1)))
        | Some t1, Some (Gcst c2) -> Some (Gnot (Gin (t1, c2, c2)))
        | Some t1, Some t2 -> Some (Gnot (Gin (Gsub (t1, t2), "0", "0")))
        | _ -> None
      end
  | Pand (_, _, p1, p2) ->
      begin match gpred def p1, gpred def p2 with
        | Some p1, Some p2 -> Some (Gand (p1, p2))
        | (Some _ as p1), None when def = true -> p1
        | None, (Some _ as p2) when def = true -> p2
        | _-> None
      end
  | Por (p1, p2) ->
      begin match gpred def p1, gpred def p2 with
        | Some p1, Some p2 -> Some (Gor (p1, p2))
        | (Some _ as p1), None when def = false -> p1
        | None, (Some _ as p2) when def = false -> p2
        | _ -> None
      end
  | Pimplies (_, p1, p2) ->
      begin match gpred (not def) p1, gpred def p2 with
        | Some p1, Some p2 -> Some (Gimplies (p1, p2))
        | Some p1, None        when def = false -> Some (Gnot p1)
        | None, (Some _ as p2) when def = false -> p2
        | _ -> None
      end
  | Pnamed (_, p) ->
      gpred def p
  | Pnot p ->
      begin match gpred (not def) p with
        | Some p -> Some (Gnot p)
        | _ -> None
      end
  | Forall _ 
  | Papp _
  | Pif _
  | Piff _
  | Forallb _
  | Exists _
  | Ptrue | Pfalse | Pvar _ -> (* discarded *)
      None

let gpred p =
  (*Format.printf "gpred %a@." Util.print_predicate p;*)
  gpred p

(* extraction of a list of equalities and possibly a Gappa predicate *)

let rec ghyp = function
  | Papp (id, [Tvar x; t], _) when is_eq id ->
    begin
      match termo t with
      | Some t' ->
          Hashtbl.replace var_table x t';
          [], None
      | None -> [], None
    end
  | Papp (id, [Tapp (id', [Tvar x], _); t], _) as p
      when is_eq id && (id' == float_value || id' == exact_value || id' == model_value) ->
    begin
      match termo t with
      | Some t ->
          let f = field_of_id id' in
          if Hashtbl.mem def_table (f, x) then
           (Hashtbl.add def_table (f, x) ();
            [f, Ident.string x, t], None)
          else
            [], gpred true p
      | None ->
          [], gpred true p
    end
  | Pand (_, _, p1, p2) as p ->
      begin match ghyp p1, ghyp p2 with
        | ([], _), ([], _) -> [], gpred true p
        | (e1,p1), (e2, p2) -> e1 @ e2, gando (p1, p2)
      end
  | Pnamed (_, p) ->
      ghyp p
  | p ->
      [], gpred true p

(* Processing obligations.
   One Why obligation can be split into several Gappa obligations *)

let queue = Queue.create ()

let reset () =
  Queue.clear queue;
  Hashtbl.clear gen_table;
  Hashtbl.clear var_table;
  Hashtbl.clear rnd_table;
  Hashtbl.clear def_table

let add_ctx_vars =
  List.fold_left 
    (fun acc -> function Svar (id,_) -> Idset.add id acc | _ -> acc)

let rec intros ctx = function
  | Forall (_, id, n, t, _, p) ->
      let id' = next_away id (add_ctx_vars (predicate_vars p) ctx) in
      let p' = subst_in_predicate (subst_onev n id') p in
      intros (Svar (id', t) :: ctx) p'
  | Pimplies (_, a, b) -> 
      let h = fresh_hyp () in 
      intros (Spred (h, a) :: ctx) b
  | Pnamed (_, p) ->
      intros ctx p
  | c -> 
      ctx, c

let process_obligation (ctx, concl) =
  let ctx,concl = intros ctx concl in
    let el, pl =
      List.fold_left
        (fun ((el, pl) as acc) h ->
          match h with
            | Svar _ -> acc
            | Spred (_, p) -> 
                let ep, pp = ghyp p in
                let pl =
                  match pp with
                    | None -> pl
                    | Some pp -> pp :: pl
                  in
                ep :: el, pl)
        ([],[]) ctx
	in
  match gpred false concl with
    | None -> (* goal is not a gappa prop *)
	if debug then Format.eprintf "not a gappa prop; skipped@."
    | Some p ->
        let gconcl = List.fold_right (fun p acc -> Gimplies (p, acc)) pl p in
        let el = List.rev (List.flatten el) in
	Queue.add (el, gconcl) queue

let push_decl d =
  let decl = PredDefExpansor.push ~recursive_expand:true d in
  match decl with
  | Logic_decl.Dgoal (_,_,_,s) -> process_obligation s.Env.scheme_type
  | _ -> ()

let get_format = function
  | Single -> "32"
  | Double -> "64"

let get_mode = function
  | RndNE -> "ne"
  | RndZR -> "zr"
  | RndUP -> "up"
  | RndDN -> "dn"
  | RndNA -> "na"

let rec print_term fmt = function
  | Gvar x -> fprintf fmt "%s" x
  | Gfld (Rounded, x) -> fprintf fmt "float_%s" x
  | Gfld (Exact,   x) -> fprintf fmt "exact_%s" x
  | Gfld (Model,   x) -> fprintf fmt "model_%s" x
  | Grnd (f, m, t) -> fprintf fmt "rnd_%s%s(%a)" (get_format f) (get_mode m) print_term t
  | Gcst c -> fprintf fmt "%s" c
  | Gneg t -> fprintf fmt "(-%a)" print_term t
  | Gadd (t1, t2) -> fprintf fmt "(%a + %a)" print_term t1 print_term t2
  | Gsub (t1, t2) -> fprintf fmt "(%a - %a)" print_term t1 print_term t2
  | Gmul (t1, t2) -> fprintf fmt "(%a * %a)" print_term t1 print_term t2
  | Gdiv (t1, t2) -> fprintf fmt "(%a / %a)" print_term t1 print_term t2
  | Gabs t -> fprintf fmt "|%a|" print_term t

let rec print_pred_atom fmt = function
  | Gle (t, r1) ->
      fprintf fmt "%a <= %s" print_term t r1
  | Gge (t, r1) ->
      fprintf fmt "%a >= %s" print_term t r1
  | Gin (t, r1, r2) ->
      fprintf fmt "%a in [%s, %s]" print_term t r1 r2
  | Gnot p ->
      fprintf fmt "not %a" print_pred_atom p
  | _ as p ->
      fprintf fmt "(%a)" print_pred p
and print_pred_left fmt = function
  | Gand (p1, p2) ->
      fprintf fmt "@[%a /\\@ %a@]" print_pred_atom p1 print_pred_atom p2
  | Gor (p1, p2) ->
      fprintf fmt "@[%a \\/@ %a@]" print_pred_atom p1 print_pred_atom p2
  | _ as p ->
      print_pred_atom fmt p
and print_pred fmt = function
  | Gimplies (p1, p2) ->
      fprintf fmt "@[%a ->@ %a@]" print_pred_left p1 print_pred p2
  | _ as p ->
      print_pred_left fmt p

let print_equation fmt (e, x, t) =
  let e =
    match e with
    | Rounded -> "float_"
    | Exact -> "exact_"
    | Model -> "model_" in
  fprintf fmt "@[%s%s = %a;@]" e x print_term t

let print_obligation fmt (eq,p) =
  Hashtbl.iter (fun (f, m) () ->
    let f = get_format f in
    let m = get_mode m in
    fprintf fmt "@@rnd_%s%s = float<ieee_%s, %s>;@\n" f m f m) rnd_table;
  fprintf fmt "@\n%a@\n@\n" (print_list newline print_equation) eq;
  fprintf fmt "{ @[%a@] }@." print_pred p

let output_one_file f =
  let sep = "### DO NOT EDIT ABOVE THIS LINE" in
  let file = out_file (f ^ "_why.gappa") in
  do_not_edit_above ~file
    ~before:(fun fmt -> Queue.iter (print_obligation fmt) queue)
    ~sep
    ~after:(fun fmt -> ())


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
