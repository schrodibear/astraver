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

(*i $Id: cinterp.ml,v 1.4 2002-11-07 12:20:17 filliatr Exp $ i*)

(* Interpretation of C programs *)

open Format
open Misc
open Ident
open Logic
open Types
open Cast
open Ptree

let parse_annot f = option_app (fun (ofs, s) -> f ofs s)

let interp_c_spec v an = 
  let (p,e,q) = match parse_annot Parser.parse_c_spec an with
    | None -> ([], Effect.bottom, None) 
    | Some k -> k
  in
  { pc_result_name = result; pc_result_type = PVpure v;
    pc_effect = e; pc_pre = p; pc_post = q }

let interp_c_pre an = list_of_some (parse_annot Parser.parse_c_pre an)

let interp_c_post = parse_annot Parser.parse_c_post

let mk_ptree l d p q = { pdesc = d ; pre = p; post = q; loc = l }
let mk_expr l d = mk_ptree l d [] None

let mk_seq loc e1 e2 = match e1, e2 with
  | { pdesc=Sseq l1 }, { pdesc=Sseq l2 } -> mk_expr loc (Sseq (l1 @ l2))
  | e1, { pdesc=Sseq l2 } -> mk_expr loc (Sseq (Sstatement e1 :: l2))
  | { pdesc=Sseq l1 }, e2 -> mk_expr loc (Sseq (l1 @ [Sstatement e2]))
  | e1, e2 -> mk_expr loc (Sseq [Sstatement e1; Sstatement e2])

let rec interp_expr = function
  | CEvar (loc, id) -> 
      mk_expr loc (Svar id)
  | CEassign (loc, Lvar (_,id), Aequal, e) -> 
      mk_expr loc (Srefset (id, interp_expr e))
  | CEassign _ -> 
      assert false
  | CEseq (loc, e1, e2) -> 
      mk_seq loc (interp_expr e1) (interp_expr e2)

let interp_statement = function
  | CSexpr (_, e) -> Sstatement (interp_expr e)

let interp_block (l, p, b, q) =
  { pdesc = Sseq (List.map interp_statement b);
    pre = interp_c_pre p; post = interp_c_post q; loc = l }

let interp_binder (pt, id) = (id, BindType (PVpure pt))

let interp_binders = List.map interp_binder

let interp_fun l bl v bs =
  mk_ptree l (Slam (interp_binders bl, interp_block bs)) [] None

let interp_decl = function
  | Ctypedecl (l, CDvar id, v) -> 
      Parameter (l, [id], PVref (PVpure v))
  | Ctypedecl (l, CDfun (id, bl, an), v) -> 
      let k = interp_c_spec v an in
      let bl = List.map (fun (v, id) -> (id, BindType (PVpure v))) bl in
      Parameter (l, [id], PVarrow (bl, k))
  | Ctypedecl _ -> 
      assert false
  | Cfundef (l, id, bl, v, bs) ->
      let bl = if bl = [] then [PTunit, anonymous] else bl in
      Program (id, interp_fun l bl v bs)

let interp = List.map interp_decl

