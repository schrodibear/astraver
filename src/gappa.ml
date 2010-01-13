(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2009                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Guillaume MELQUIOND                                                 *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
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
type float_fmt = Single | Double | Binary80
(* modes of the float model *)
type mode = RndNE | RndZR | RndUP | RndDN | RndNA

type gterm =
  | Gvar of string
  | Gfld of float_field * string
  | Grnd of float_fmt * mode * gterm
  | Gcst of string
  | Gsqrt of gterm
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
  | Grel of gterm * gterm * string
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

let max_single = Ident.create "max_single"
let max_double = Ident.create "max_double"
let round_single = Ident.create "round_single"
let round_double = Ident.create "round_double"
let single_round_error = Ident.create "single_round_error"
let double_round_error = Ident.create "double_round_error"
let round_single_logic = Ident.create "round_single_logic"
let round_double_logic = Ident.create "round_double_logic"
let single_to_double = Ident.create "single_to_double"
let double_to_single = Ident.create "double_to_single"

let single_value = Ident.create "single_value"
let double_value = Ident.create "double_value"
let single_exact = Ident.create "single_exact"
let double_exact = Ident.create "double_exact"
let single_model = Ident.create "single_model"
let double_model = Ident.create "double_model"

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
  | Tapp (id,_,_) when id == max_single -> true
  | Tapp (id,_,_) when id == max_double -> true
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
  | Tapp (id, [Tconst (ConstInt n)], _) when id == real_of_int -> n
  | Tapp (id,_,_) when id == max_single -> "0x1.FFFFFEp127"
  | Tapp (id,_,_) when id == max_double -> "0x1.FFFFFFFFFFFFFp1023"
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
  if s == single_value || s == double_value then Rounded else
  if s == single_exact || s == double_exact then Exact else
  if s == single_model || s == double_model then Model else
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

(* contains the reverted list of aliases from def_table *)
let def_list = ref []

let rec subst_var = function
  | Tvar id as t ->
    begin
      try
        Hashtbl.find var_table id
      with Not_found ->
        t
    end
  | Tnamed (_, t) -> subst_var t
  | Tapp (id, l1, l2) -> Tapp (id, List.map subst_var l1, l2)
  | t -> t

let rec term = function
  | t when is_constant t ->
      Gcst (eval_constant t)
  | Tconst _ ->
      raise NotGappa
  | Tvar id ->
      Gvar (Ident.string id)
  | Tderef id ->
      Gvar (Ident.string id)
  (* int and real ops *)
  | Tapp (id, [t], _) when id == t_neg_real || id = t_neg_int ->
      Gneg (term t)
  | Tapp (id, [t], _) when id == t_abs_real || id == t_abs_int ->
      Gabs (term t)
  | Tapp (id, [t], _) when id == t_sqrt_real ->
      Gsqrt (term t)
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
  | Tapp (id, [Tapp (m, [], _); t], _)
      when id == round_single ->
      let mode =
        if m == rnd_ne then RndNE else
        if m == rnd_zr then RndZR else
        if m == rnd_up then RndUP else
        if m == rnd_dn then RndDN else
        if m == rnd_na then RndNA else
        raise NotGappa in
      Hashtbl.replace rnd_table (Single, mode) ();
      Grnd (Single, mode, term t)
  | Tapp (id, [Tapp (m, [], _); t], _)
      when id == round_double ->
      let mode =
        if m == rnd_ne then RndNE else
        if m == rnd_zr then RndZR else
        if m == rnd_up then RndUP else
        if m == rnd_dn then RndDN else
        if m == rnd_na then RndNA else
        raise NotGappa in
      Hashtbl.replace rnd_table (Double, mode) ();
      Grnd (Double, mode, term t)

  | Tapp (id1, [Tapp (id2, l1, l2)], _)
      when id1 == single_value && id2 == round_single_logic ->
      term (Tapp (round_single, l1, l2))
  | Tapp (id1, [Tapp (id2, l1, l2)], _)
      when id1 == double_value && id2 == round_double_logic ->
      term (Tapp (round_double, l1, l2))

  (* casts *)
  | Tapp (id1, [Tapp (id2,[Tapp (m, [], _); t] , l2)], _)  
      when id1 == single_value && id2 == double_to_single ->
      let mode =
        if m == rnd_ne then RndNE else
        if m == rnd_zr then RndZR else
        if m == rnd_up then RndUP else
        if m == rnd_dn then RndDN else
        if m == rnd_na then RndNA else
        raise NotGappa in
      Hashtbl.replace rnd_table (Single, mode) ();
      Grnd (Single, mode, term (Tapp (double_value,[t],l2)))

  | Tapp (id1, [Tapp (id2,[Tapp (_m, [], _); t] , l2)], _)  
      when id1 == double_value && id2 == single_to_double ->
        term (Tapp (single_value,[t],l2))


  | Tapp (id, [Tvar vx], _)
      when (id == single_value || id == double_value || id == single_exact 
         || id == double_exact || id == single_model || id == double_model) ->
      let v = Ident.string vx in
      let f = field_of_id id in
      let add_def fmt =
        if not (Hashtbl.mem def_table (f, vx)) then begin
          Hashtbl.add def_table (f, vx) ();
          Hashtbl.replace rnd_table (fmt, RndNE) ();
          def_list := (f, v, Grnd (fmt, RndNE, Gvar ("dummy_float_" ^ v))) :: !def_list;
        end in
      if id == single_value then add_def Single else
      if id == double_value then add_def Double;
      Gfld (f, v)

  | Tapp (id, [Tvar vx], _) 
    when id == single_round_error || id == double_round_error ->
    let v = Ident.string vx in
    Gabs (Gsub (Gfld (Rounded, v), Gfld (Exact, v)))

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

let termo t = try Some (term (subst_var t)) with NotGappa -> None

let gando = function
  | Some p1, Some p2 -> Some (Gand (p1, p2))
  | (Some _p as v), None | None, (Some _p as v) -> v
  | None, None -> None

(* recognition of a Gappa predicate *)

let rec gpred def = function
  | Papp (id, [t1; t2], _) when id == t_le_real || id == t_le_int ->
      begin match termo t1, termo t2 with
	| Some (Gcst c1), Some t2 -> Some (Gge (t2, c1))
	| Some t1, Some (Gcst c2) -> Some (Gle (t1, c2))
        | Some t1, Some t2 ->
            begin match t1, t2 with
              | Gabs (Gsub (t1, t2)), Gmul (Gcst c, Gabs t3) when t2 = t3 ->
                  Some (Grel (t1, t2, c))
              | Gabs (Gsub (t2, t1)), Gmul (Gcst c, Gabs t3) when t2 = t3 ->
                  Some (Grel (t1, t2, c))
              | Gabs (Gsub (t1, t2)), Gmul (Gabs t3, Gcst c) when t2 = t3 ->
                  Some (Grel (t1, t2, c))
              | Gabs (Gsub (t2, t1)), Gmul (Gabs t3, Gcst c) when t2 = t3 ->
                  Some (Grel (t1, t2, c))
              | _ -> Some (Gle (Gsub (t1, t2), "0"))
            end
        | _ -> None
      end
  | Papp (id, [t1; t2], _) when id == t_ge_real || id == t_ge_int ->
      begin match termo t1, termo t2 with
	| Some (Gcst c1), Some t2 -> Some (Gle (t2, c1))
	| Some t1, Some (Gcst c2) -> Some (Gge (t1, c2))
        | Some t1, Some t2 -> Some (Gge (Gsub (t1, t2), "0"))
	| _ -> None
      end
  | Papp (id, [t1; t2], _) when id == t_lt_real || id == t_lt_int ->
      begin match termo t1, termo t2 with
        | Some (Gcst c1), Some t2 -> Some (Gnot (Gle (t2, c1)))
        | Some t1, Some (Gcst c2) -> Some (Gnot (Gge (t1, c2)))
        | Some t1, Some t2 -> Some (Gnot (Gge (Gsub (t1, t2), "0")))
        | _ -> None
      end
  | Papp (id, [t1; t2], _) when id == t_gt_real || id == t_gt_int ->
      begin match termo t1, termo t2 with
        | Some (Gcst c1), Some t2 -> Some (Gnot (Gge (t2, c1)))
        | Some t1, Some (Gcst c2) -> Some (Gnot (Gle (t1, c2)))
        | Some t1, Some t2 -> Some (Gnot (Gle (Gsub (t1, t2), "0")))
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
  | Pimplies (_, Papp (id, [Tconst (ConstBool true); Tconst (ConstBool true)], _), p)
      when id == t_eq_bool ->
      gpred def p
  | Pimplies (_, p1, p2) ->
      begin match gpred (not def) p1, gpred def p2 with
        | Some p1, Some p2 -> Some (Gimplies (p1, p2))
        | Some p1, None        when def = false -> Some (Gnot p1)
        | None, (Some _ as p2) when def = false -> p2
        | _ -> None
      end
  | Pnamed (_, p) ->
      gpred def p
  | Plet (_, n, _, t, p) ->
      gpred def (subst_term_in_predicate n t p)
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

(*
let gpred def p =
  Format.printf "gpred %a@." Util.print_predicate p;
  gpred def p
*)

(* extraction of a list of equalities and possibly a Gappa predicate *)

let rec ghyp = function
  | Papp (id, [Tvar x; t], _) when is_eq id ->
    begin
      Hashtbl.replace var_table x (subst_var t);
      None
    end
  | Papp (id, [Tapp (id', [Tvar x], _); t], _) as p
      when is_eq id && 
	(id' == single_value || id' == double_value || id' == single_exact 
       || id' == double_exact || id' == single_model || id' == double_model) ->
    begin
      match termo t with
      | Some t ->
          let f = field_of_id id' in
          if not (Hashtbl.mem def_table (f, x)) then
           (Hashtbl.add def_table (f, x) ();
            def_list := (f, Ident.string x, t) :: !def_list;
            None)
          else
            gpred true p
      | None ->
          gpred true p
    end
  | Pand (_, _, p1, p2) ->
      gando (ghyp p1, ghyp p2)
  | Pnamed (_, p) ->
      ghyp p
  | p ->
      gpred true p

(* Processing obligations.
   One Why obligation can be split into several Gappa obligations *)

let queue = Queue.create ()

let reset () =
  Queue.clear queue;
  Hashtbl.clear gen_table;
  Hashtbl.clear var_table;
  Hashtbl.clear rnd_table;
  Hashtbl.clear def_table;
  def_list := []

let add_ctx_vars =
  List.fold_left 
    (fun acc -> function Svar (id,_) -> Idset.add id acc | _ -> acc)

(* takes a reverted context and returns an augmented reverted context *)
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
  let ctx, concl = intros (List.rev ctx) concl in
  let ctx = List.rev ctx in
  let pl =
    List.fold_left
      (fun pl h ->
        match h with
          | Svar _ -> pl
          | Spred (_, p) -> 
              match ghyp p with
                | None -> pl
                | Some pp -> pp :: pl)
      [] ctx
    in
  let gconcl =
    match gpred false concl with
      | None -> Gle (Gcst "1", "0")
      | Some p -> p
    in
  let gconcl = List.fold_left (fun acc p -> Gimplies (p, acc)) gconcl pl in
  Queue.add (List.rev !def_list, gconcl) queue

let push_decl d =
  let decl = PredDefExpansor.push ~recursive_expand:true d in
  match decl with
  | Logic_decl.Dgoal (_,_,_,s) -> process_obligation s.Env.scheme_type
  | _ -> ()

let get_format = function
  | Single -> "ieee_32"
  | Double -> "ieee_64"
  | Binary80 -> "x86_80"

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
  | Gsqrt t -> fprintf fmt "sqrt(%a)" print_term t

let rec print_pred_atom fmt = function
  | Gle (t, r1) ->
      fprintf fmt "%a <= %s" print_term t r1
  | Gge (t, r1) ->
      fprintf fmt "%a >= %s" print_term t r1
  | Gin (t, r1, r2) ->
      fprintf fmt "%a in [%s, %s]" print_term t r1 r2
  | Grel (t1, t2, r1) ->
      fprintf fmt "|%a -/ %a| <= %s" print_term t1 print_term t2 r1
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
    fprintf fmt "@@rnd_%s%s = float<%s, %s>;@\n" f m f m) rnd_table;
  fprintf fmt "@\n%a@\n@\n" (print_list newline print_equation) eq;
  fprintf fmt "{ @[%a@] }@." print_pred p

let output_one_file f =
  let sep = "### DO NOT EDIT ABOVE THIS LINE" in
  let file = f ^ "_why.gappa" in
  do_not_edit_above ~file
    ~before:(fun fmt -> Queue.iter (print_obligation fmt) queue)
    ~sep
    ~after:(fun _fmt -> ())


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
	 ~after:(fun _fmt -> ()))
    queue
