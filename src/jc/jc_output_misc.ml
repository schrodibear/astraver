(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Lexing
open Format
open Why_pp

open Stdlib
open Output_ast

(*******************************************************************************)
(* Logic types                                                                 *)
(*******************************************************************************)

let logic_type_var s =
  { lt_name = "'" ^ s;
    lt_args = [] }

let is_prop lt = lt.lt_name = "prop"

let rec iter_logic_type f t =
  f t.lt_name;
  List.iter (iter_logic_type f) t.lt_args

(*******************************************************************************)
(* Terms                                                                       *)
(*******************************************************************************)

let const_of_num n = LConst (Prim_int (Num.string_of_num n))

let const_of_int i = LConst (Prim_int (string_of_int i))

let rec iter_term f t =
  match t with
  | LConst _ -> ()
  | LApp (id, l) ->
    f id;
    List.iter (iter_term f) l
  | LVar id
  | LDeref id
  | LDerefAtLabel (id, _) ->
    f id
  | TLabeled (_, t) -> iter_term f t
  | TIf (t1, t2, t3) ->
    iter_term f t1;
    iter_term f t2;
    iter_term f t3
  | TLet (id, t1, t2) ->
    f id;
    iter_term f t1;
    iter_term f t2

let rec match_term acc t1 t2 =
  match t1, t2 with
  | LVar id, _ -> (id, t2) :: acc
  | LApp (id1, l1), LApp (id2, l2) when id1 = id2 ->
    List.fold_left2 match_term acc l1 l2
  | _ -> invalid_arg "match_term : t1 is not a valid context"

let make_var s = LVar s

let positioned f l_pos ?behavior:(l_behavior = "default") ?kind:l_kind =
  f { l_kind; l_behavior; l_pos }

let make_positioned = positioned @@ fun l t -> TLabeled (l, t)

let make_located = make_positioned % Jc_position.of_loc

let make_positioned_lex  = make_positioned % Jc_position.of_pos

(*******************************************************************************)
(* Assertions                                                                  *)
(*******************************************************************************)

let rec unlabel a =
  match a with
  | LLabeled (_, a) -> unlabel a
  | _ -> a

let mk_positioned = positioned @@ fun l a -> LLabeled (l, a)

let mk_located = mk_positioned % Jc_position.of_loc

let mk_positioned_lex = mk_positioned % Jc_position.of_pos

let is_not_true a =
  match unlabel a with
  | LTrue -> false
  | _ -> true

let make_not a1 =
  match unlabel a1 with
  | LTrue -> LFalse
  | LFalse -> LTrue
  | _ -> LNot a1

let make_or a1 a2 =
  match unlabel a1, unlabel a2 with
  | LTrue, _ -> LTrue
  | _, LTrue -> LTrue
  | LFalse, _ -> a2
  | _, LFalse -> a1
  | _, _ -> LOr (a1, a2)

let make_and a1 a2 =
  match unlabel a1, unlabel a2 with
  | LTrue, _ -> a2
  | _, LTrue -> a1
  | LFalse, _ -> LFalse
  | _, LFalse -> LFalse
  | _, _ -> LAnd (a1, a2)

let rec make_and_list l =
  match l with
  | [] -> LTrue
  | f :: r -> make_and f (make_and_list r)

let rec make_or_list l =
  match l with
  | [] -> LFalse
  | f::r -> make_or f (make_or_list r)

let rec make_forall_list l triggers assertion =
  match l with
  | [] -> assertion
  | [s, ty] -> LForall (s, ty, triggers, assertion)
  | (s, ty) :: l -> LForall (s, ty, [], make_forall_list l triggers assertion)

let make_impl a1 a2 =
  match unlabel a1, unlabel a2 with
  | LTrue, _ -> a2
  | _, LTrue -> LTrue
  | LFalse, _ -> LTrue
  | _, LFalse -> LNot a1
  | _, _ -> LImpl (a1, a2)

let rec make_impl_list conclu =
  function
  | [] -> conclu
  | a :: l -> LImpl (a, make_impl_list conclu l)

let make_equiv a1 a2 =
  match unlabel a1, unlabel a2 with
  | LTrue, _ -> a2
  | _, LTrue -> a1
  | LFalse, _ -> make_not a2
  | _, LFalse -> make_not a1
  | _, _ -> LIff (a1, a2)

let rec iter_assertion f a =
  match a with
  | LTrue -> ()
  | LFalse -> ()
  | LAnd (a1, a2) ->
    iter_assertion f a1;
    iter_assertion f a2
  | LOr (a1, a2) ->
    iter_assertion f a1;
    iter_assertion f a2
  | LIff (a1, a2) ->
    iter_assertion f a1;
    iter_assertion f a2
  | LNot a1 -> iter_assertion f a1
  | LImpl (a1, a2) ->
    iter_assertion f a1;
    iter_assertion f a2
  | LIf (t, a1, a2) ->
    iter_term f t;
    iter_assertion f a1;
    iter_assertion f a2
  | LLet (_id, t, a) ->
    iter_term f t;
    iter_assertion f a
  | LForall (_id, t, trigs, a) ->
    iter_logic_type f t;
    iter_triggers f trigs;
    iter_assertion f a
  | LExists (_id, t, trigs, a) ->
    iter_logic_type f t;
    iter_triggers f trigs;
    iter_assertion f a
  | LPred (id, l) ->
    f id;
    List.iter (iter_term f) l
  | LLabeled (_, a) ->
    iter_assertion f a

and iter_triggers f trigs =
  List.iter
    (List.iter @@
      function
      | LPatP a -> iter_assertion f a
      | LPatT t -> iter_term f t)
  trigs

let rec assertion_of_term t =
  match t with
  | LConst (Prim_bool true) -> LTrue
  | LConst (Prim_bool false) -> LFalse
  | LApp ("bool_not", [t1]) -> LNot (assertion_of_term t1)
  | LApp ("bool_and", [t1; t2]) -> LAnd (assertion_of_term t1, assertion_of_term t2)
  | LApp ("bool_or", [t1; t2]) -> LOr (assertion_of_term t1, assertion_of_term t2)
  | LApp ("lt_int_bool", [t1; t2]) -> LPred ("lt_int", [t1; t2])
  | LApp ("le_int_bool", [t1; t2]) -> LPred ("le_int", [t1; t2])
  | LApp ("gt_int_bool", [t1; t2]) -> LPred ("gt_int", [t1; t2])
  | LApp ("ge_int_bool", [t1; t2]) -> LPred ("ge_int", [t1; t2])
  | LApp ("lt_real_bool", [t1; t2]) -> LPred ("lt_real", [t1; t2])
  | LApp ("le_real_bool", [t1; t2]) -> LPred ("le_real", [t1; t2])
  | LApp ("gt_real_bool", [t1; t2]) -> LPred ("gt_real", [t1; t2])
  | LApp ("ge_real_bool", [t1; t2]) -> LPred ("ge_real", [t1; t2])
  (** by default *)
  | _ -> LPred ("eq", [t; LConst (Prim_bool true)])

(*******************************************************************************)
(* Why types                                                                   *)
(*******************************************************************************)

let base_type s = Base_type { lt_name = s; lt_args = [] }
let int_type = base_type "int"
let bool_type = base_type "bool"
let unit_type = base_type "unit"

let rec iter_why_type f t =
  match t with
  | Prod_type (_, t1, t2) ->
    iter_why_type f t1;
    iter_why_type f t2
  | Base_type b -> iter_logic_type f b
  | Ref_type t -> iter_why_type f t
  | Annot_type (pre, t, reads, writes, post, signals) ->
    iter_assertion f pre;
    iter_why_type f t;
    List.iter f reads;
    List.iter f writes;
    iter_assertion f post;
    List.iter (fun (id, a) -> f id; iter_assertion f a) signals

(*******************************************************************************)
(* Expressions                                                                 *)
(*******************************************************************************)

let mk_expr e = { expr_labels = []; expr_node = e }
let mk_var s = mk_expr (Var s)
let void = mk_expr Void

let rec iter_expr f e =
  match e.expr_node with
  | Cte _ -> ()
  | Var id -> f id
  | And (e1, e2) ->
    iter_expr f e1;
    iter_expr f e2
  | Or (e1, e2) ->
    iter_expr f e1;
    iter_expr f e2
  | Not e1 -> iter_expr f e1
  | Void -> ()
  | Deref id -> f id
  | If (e1, e2, e3) ->
    iter_expr f e1;
    iter_expr f e2;
    iter_expr f e3
  | While (e1, inv, var, e2) ->
    iter_expr f e1;
    iter_assertion f inv;
    Option.iter
      ~f:(fun (var, r) ->
         iter_term f var;
         Option.iter f r)
      var;
    List.iter (iter_expr f) e2
  | Block el -> List.iter (iter_expr f) el
  | Assign (id, e) ->
    f id;
    iter_expr f e
  | Let (_id, e1, e2) ->
    iter_expr f e1;
    iter_expr f e2
  | Let_ref (_id, e1, e2) ->
    iter_expr f e1;
    iter_expr f e2
  | App (e1, e2, _) ->
    iter_expr f e1;
    iter_expr f e2
  | Raise (_, None) -> ()
  | Raise (_id, Some e) ->
    iter_expr f e
  | Try (e1, _exc, _id, e2) ->
    iter_expr f e1;
    iter_expr f e2
  | Fun (_params, pre, body, post, _diverges, signals) ->
    iter_assertion f pre;
    iter_expr f body;
    iter_assertion f post;
    List.iter (fun (_, a) -> iter_assertion f a) signals
  | Triple (_, pre, e, post, exceps) ->
    iter_assertion f pre;
    iter_expr f e;
    iter_assertion f post;
    List.iter (fun (_, a) -> iter_assertion f a) exceps
  | Assert (_, p, e) ->
    iter_assertion f p;
    iter_expr f e
  | Labeled (_, e) -> iter_expr f e
  | BlackBox ty -> iter_why_type f ty
  | Absurd -> ()


let make_or_expr a1 a2 =
  match a1.expr_node, a2.expr_node with
  | Cte (Prim_bool true), _ -> a1
  | _, Cte (Prim_bool true) -> a2
  | Cte (Prim_bool false), _ -> a2
  | _, Cte (Prim_bool false) -> a1
  | _, _ -> mk_expr @@ Or (a1, a2)

let make_and_expr a1 a2 =
  match a1.expr_node, a2.expr_node with
  | Cte (Prim_bool true), _ -> a2
  | _, Cte (Prim_bool true)  -> a1
  | Cte (Prim_bool false), _ -> a1
  | _, Cte (Prim_bool false) -> a2
  | _, _ -> mk_expr @@ And (a1, a2)

let make_app_rec ~logic f l =
  let rec make_rec accu =
    function
    | [] -> accu
    | e :: r -> make_rec (mk_expr (App (accu, e, None))) r
  in
  match l with
  | [] when logic -> make_rec f []
  | [] -> make_rec f [void]
  | l -> make_rec f l

let app_add_ty ?ty e =
  match ty, e.expr_node with
  | None, _ -> e
  | Some _, App (e1, e2, None) -> { e with expr_node = App (e1, e2, ty) }
  | Some _, _ ->
    invalid_arg "app_add_ty: type coercion for constant"

let make_app ?ty id =
  app_add_ty ?ty %
    make_app_rec ~logic:false (mk_var id)

let make_logic_app ?ty id =
  app_add_ty ?ty %
    make_app_rec ~logic:true (mk_var id)

let make_app_e ?ty e =
  app_add_ty ?ty %
    make_app_rec ~logic:false e

let make_while cond inv var e =
  let body =
    match e.expr_node with
    | Block l -> l
    | _ -> [e]
  in
  mk_expr @@ While (cond, inv, var, body)

let make_label label e =
  assert (String.length label > 0);
  { e with expr_labels = label :: e.expr_labels }

let make_pre pre e =  mk_expr @@ Triple (false, pre, e, LTrue, [])

let make_positioned_e = positioned @@ fun l e -> mk_expr @@ Labeled (l, e)

let make_located_e = make_positioned_e % Jc_position.of_loc

let make_positioned_lex_e = make_positioned_e % Jc_position.of_pos

let make_block labels l =
  match l with
  | [] -> failwith "make_block: empty label list"
  | [e] -> { e with expr_labels = labels @ e.expr_labels }
  | _ -> { expr_labels = labels; expr_node = Block l }

(** Try hard to keep the labels visible by all the instructions that follow
    but also to remove unneeded block

    The principle is to push e2 inside e1 such that every labels visible for
    the last instruction (not a block) of e1 can be visible for e2

    This function should actually be called PREPEND (or CONS).
*)
let rec append' e1 e2 =
  match e1.expr_node, e2.expr_node with
  | Void, _ ->  [e2]
  | _, Void ->
    assert (e2.expr_labels = []);
    [e1]
  | Block _, Block [] -> [e1]
  | Block l1, _ ->
    [make_block e1.expr_labels @@ concat l1 e2]
  | _, Block l2 ->
    begin match e1.expr_labels, e2.expr_labels with
    | [], [] -> e1 :: l2
    | labels1, [] ->
      [make_block labels1 @@ { e1 with expr_labels = [] } :: l2]
    | labels1, _ ->
      [make_block labels1 @@ { e1 with expr_labels = [] } :: [e2]]
    end
  | _ when e1.expr_labels = [] -> e1 :: [e2]
  | _ ->
    let e1' = { e1 with expr_labels = [] } in
    [make_block e1.expr_labels @@ e1' :: [e2]]

and concat l1 e2 =
  match l1 with
  | [] -> [e2]
  | [a1] -> append' a1 e2
  | a1 :: l1 -> a1 :: concat l1 e2

let append e1 e2 =
  make_block [] @@ append' e1 e2

(*******************************************************************************)
(* Declarations                                                                *)
(*******************************************************************************)

let id_no_loc s = { why_name = s; why_expl = ""; why_pos = Jc_position.dummy }

let get_why_id d =
  match d with
  | Param (_, id, _)
  | Logic (_, id, _, _)
  | Def (id, _)
  | Goal (_, id, _)
  | Predicate (_, id, _, _)
  | Function (_, id, _, _, _)
  | Inductive (_, id, _, _)
  | Type (id, _)
  | Exception (id, _) -> id

let iter_why_decl f d =
  match d with
  | Param (_, _, t) -> iter_why_type f t
  | Def (_id, t) -> iter_expr f t
  | Logic (_, _id, args, t) ->
    List.iter (fun (_, t) -> iter_logic_type f t) args;
    iter_logic_type f t
  | Inductive (_, _id, args, cases) ->
    List.iter (fun (_, t) -> iter_logic_type f t) args;
    List.iter (fun (_, a) -> iter_assertion f a) cases
  | Predicate (_,_id,args,p) ->
    List.iter (fun (_, t) -> iter_logic_type f t) args;
    iter_assertion f p
  | Goal (_, _id, t) -> iter_assertion f t
  | Function (_, _id, args, t, p) ->
    List.iter (fun (_, t) -> iter_logic_type f t) args;
    iter_logic_type f t;
    iter_term f p
  | Type (_t, args) -> List.iter f args
  | Exception (_, t) -> Option.iter (iter_logic_type f) t

type state = [ `TODO | `RUNNING | `DONE ]

type 'a decl = { mutable state : state; decl : 'a }

module StringMap = Map.Make (String)

let rec do_topo decl_map iter_fun output_fun id d =
  match d.state with
  | `DONE -> ()
  | `RUNNING ->
    eprintf "Warning: recursive definition of %s in generated file@." id
  | `TODO ->
    d.state <- `RUNNING;
    iter_fun
      (fun id ->
         try
           do_topo decl_map iter_fun output_fun id @@ StringMap.find id decl_map
         with
         | Not_found -> ())
      d.decl;
    output_fun d.decl;
    d.state <- `DONE

let compare_ids
    { why_name = id1; why_pos = pos1 }
    { why_name = id2; why_pos = pos2 } =
  let c = Jc_position.compare pos1 pos2 in
  if c = 0 then compare id1 id2 else c

let build_map get_id decl_list =
  StringMap.(
    List.fold_left
      (fun acc decl ->
         let id = get_id decl in
         add id.why_name (id, { state = `TODO; decl }) acc)
      empty
      decl_list)
  |> fun m ->
    StringMap.(
      fold
        (fun name (id, d) (m, l) ->
           (add name d m, (id, d) :: l))
        m
        (StringMap.empty, []))
  |> fun (m, l) ->
    m, List.sort (compare_ids %% fst @@ fst) l

let output_decls get_id iter_decl output_decl decls =
  let map, l = build_map get_id decls in
  List.iter
    (fun (id, decl) ->
       do_topo map iter_decl output_decl id.why_name decl)
    l

(*******************************************************************************)
(* Misc. utility functions                                                     *)
(*******************************************************************************)

let abs_fname f =
  if Filename.is_relative f
  then Filename.concat (Unix.getcwd ()) f
  else f

let rec fprintf_comma_string_list fmttr =
  function
  | [] -> ()
  | x :: l ->
    fprintf fmttr ",@ %s" x;
    fprintf_comma_string_list fmttr l

(*******************************************************************************)
(* Why *.loc files (source code positions)                                     *)
(*******************************************************************************)

let why_reg_pos, why_get_pos, why_print_locs =
  let open Hashtbl in
  let why_pos_table :
    (string, (vc_kind option * string option * string option *
             string * int * int * int))
    t
    = create 97
  in
  add why_pos_table,
  find why_pos_table,
  fun fprintf_kind fmttr ->
    let pr fmt = fprintf fmttr fmt in
    iter
      (fun id (kind, name, beh, f, l, fc, lc) ->
         pr "[%s]@\n" id;
         Option.iter (pr "kind = %a@\n" fprintf_kind) kind;
         Option.iter (pr "name = \"%s\"@\n") name;
         Option.iter (pr "behavior = \"%s\"@\n") beh;
         pr "file = \"%s\"@\n" (String.escaped f);
         pr "line = %d@\n" l;
         pr "begin = %d@\n" fc;
         pr "end = %d@\n@\n" lc)
      why_pos_table

(*******************************************************************************)
(* Jessie plugin compatibility ( *.loc files)                                  *)
(*******************************************************************************)

let jc_reg_pos, jc_print_pos =
  let open Hashtbl in
  let jc_pos_table = create 97 in
  let name_counter = ref 0 in
  (fun prefix ?id ?kind ?name ?formula pos ->
    let id =
      match id with
      | None ->
        incr name_counter;
        prefix ^ "_" ^ string_of_int !name_counter
      | Some n -> n
    in
    add jc_pos_table id (kind, name, formula, pos);
    id),
   fun fprintf_kind fmttr ->
     let pr fmt = fprintf fmttr fmt in
     iter
       (fun id (kind, name, formula, (f, l, fc, lc)) ->
          pr "[%s]@\n" id;
          Option.iter (pr "kind = %a@\n" fprintf_kind) kind;
          Option.iter (pr "name = \"%s\"@\n") name;
          Option.iter (pr "formula = \"%s\"@\n") formula;
          pr "file = \"%s\"@\n" (String.escaped (abs_fname f));
          pr "line = %d@\n" l;
          pr "begin = %d@\n" fc;
          pr "end = %d@\n@\n" lc)
       jc_pos_table

(*******************************************************************************)
(* Why/Why3 ML file output                                                     *)
(*******************************************************************************)

let print_to_file ext fprintf_kind fprintf_why_decls ?float_model filename decls =
  print_in_file
    (fun fmt -> fprintf fmt "%a@." (fprintf_why_decls ?float_model) decls) @@
    ext filename;
  (* not used by why3, but useful for debugging traceability *)
  let cout_locs, fmt_locs = open_file_and_formatter @@ Why_lib.file_subdir "." (filename ^ ".loc") in
  why_print_locs fprintf_kind fmt_locs;
  close_file_and_formatter (cout_locs, fmt_locs)

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_why_output_misc.ml"
  End:
*)
