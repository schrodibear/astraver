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

(* Import from Cil *)
open Cil_types
open Cil
open Cil_datatype
open Ast_info

open Visitor

(* Utility functions *)
open Common

module H = Fieldinfo.Hashtbl
module S = Fieldinfo.Set

(*****************************************************************************)
(* Organize structure types in hierarchy.                                    *)
(*****************************************************************************)

(* By default, elements should become representant only if they are
 * "preferred" according to function [prefer]. Otherwise, decided by ranking.
 *)
module Union_find
  (Elem :
    sig type t
      val equal : t -> t -> bool
      val prefer : t -> t -> int
    end)
  (S : Datatype.Set with type elt = Elem.t)
  (H : Datatype.Hashtbl with type key = Elem.t) =
struct

  open Elem

  let table = H.create 73
  let ranks = H.create 73

  let rec repr e =
    try
      let r = repr (H.find table e) in
      H.replace table e r;
      r
    with
    | Not_found -> e

  let rank e =
    try H.find ranks e with Not_found -> 0

  let unify e1 e2 =
    let r1, r2 = map_pair repr (e1, e2) in
    if not @@ equal r1 r2 then
      (* Start with preference as defined by function [prefer]. *)
      let pref = prefer r1 r2 in
      let k1, k2 = map_pair rank (r1, r2) in
      if pref < 0 then begin
        H.replace table r2 r1;
        if k1 <= k2 then H.replace ranks r1 (k2 + 1)
      end else if pref > 0 then begin
        H.replace table r1 r2;
        if k2 <= k1 then H.replace ranks r2 (k1 + 1)
      end else
        (* If no definite preference, resolve to classical ranking. *)
        if k1 < k2 then
          H.replace table r1 r2
        else if k2 < k1 then
          H.replace table r2 r1
        else begin
          H.replace table r1 r2;
          H.replace ranks r2 (k2 + 1)
        end

  (* Does not return singleton classes *)
  let classes () =
    let repr2class = H.create 17 in
    H.iter
      (fun e _ ->
        let r = repr e in
        try
          let c = H.find repr2class r in
          let c = S.add e c in
          H.replace repr2class r c
        with
        | Not_found ->
          H.add repr2class r (S.singleton e))
      table;
    H.fold (fun r c ls -> S.add r c :: ls) repr2class []

  let _one_class e =
    let r = repr e in
    H.fold
      (fun e _ ls -> if equal r (repr e) then e :: ls else ls)
      table
      []

  let _same_class e1 e2 = equal (repr e1) (repr e2)
end

module Field_elem = struct include Fieldinfo let prefer _ _ = 1 end
module FieldUF = Union_find (Field_elem) (S) (H)

let add_field_representant fi1 fi2 = FieldUF.unify fi1 fi2

module Type_elem = struct include Typ let prefer _ _ = 0 end
module TypeUF = Union_find (Type_elem) (Typ.Set) (Typ.Hashtbl)

let add_inheritance_relation ty parentty = TypeUF.unify ty parentty

let same_fields fi1 fi2 =
  let norm = typeRemoveAttributes [embedded_attr_name] in
  fi1.forig_name = fi2.forig_name &&
  Typ.equal (norm fi1.ftype) (norm fi2.ftype)

let struct_fields_exn ty =
  match unrollType ty with
  | TComp (compinfo, _, _) ->
    List.filter (fun fi -> not @@ hasAttribute padding_attr_name fi.fattr) compinfo.cfields |>
    begin function [] when compinfo.cfields <> [] -> [List.hd compinfo.cfields] | fields -> fields end
  | t -> fatal "struct_fields: non-composite type %a" Printer.pp_typ t

let cmp_subtype =
  let cache =
    let module H = Datatype.Pair_with_collections (Typ) (Typ) (struct let module_name = "type_pair" end) in
    let module H = H.Hashtbl in
    let h = H.create 25 in
    fun f ty1 ty2 ->
      try H.find h (ty1, ty2)
      with Not_found ->
        let r = f ty1 ty2 in
        H.replace h (ty1, ty2) r;
        H.replace h (ty2, ty1) (match r with `supertype -> `subtype | `subtype -> `supertype | n -> n);
        r
  in
  cache @@ fun ty1 ty2 ->
  let ty1_fields, ty2_fields = map_pair struct_fields_exn (ty1, ty2) in
  let ty1_length, ty2_length = map_pair List.length (ty1_fields, ty2_fields) in
  let min_length = min ty1_length ty2_length in
  let prefix_length =
    try
      List.fold_left2
        (fun len ch_fi par_fi ->
           if same_fields ch_fi par_fi then len + 1
           else raise Exit)
        0
        (take min_length ty1_fields)
        (take min_length ty2_fields)
    with
    | Exit -> 0
  in
  if ty1_length < ty2_length && prefix_length = ty1_length then
    `supertype
  else if ty2_length < ty1_length && prefix_length = ty2_length then
    `subtype
  else if ty1_length = ty2_length && ty2_length = prefix_length && prefix_length > 0 then
    let ty1_n_embedded_attrs, ty2_n_embedded_attrs =
      map_pair
        List.(length % filterAttributes embedded_attr_name % (fun fi -> fi.fattr) % hd)
        (ty1_fields, ty2_fields)
    in
    if ty1_n_embedded_attrs < ty2_n_embedded_attrs then
      `supertype
    else if ty2_n_embedded_attrs < ty1_n_embedded_attrs then
      `subtype
    else
      `neither
  else
    `neither

class struct_hierarchy_builder =
  let unify_type_hierarchies ty1 ty2 =
    (* Extract info from types *)
    let compinfo_of_ty_exn ty =
      match unrollType (pointed_type ty) with
      | TComp (compinfo, _, _) -> compinfo
      | t -> fatal "unify_type_hierarchies: non-composite type %a" Printer.pp_typ t
    in
    let ty1, ty2 = map_pair (fun ty -> TComp (compinfo_of_ty_exn ty, empty_size_cache (), [])) (ty1, ty2) in
    (* Compare types *)
    match cmp_subtype ty1 ty2 with
    | `supertype ->
      (* [ty2] subtype of [ty1] *)
      add_inheritance_relation ty2 ty1
    | `subtype ->
      (* [ty1] subtype of [ty2] *)
      add_inheritance_relation ty1 ty2
    | `neither -> ()
  in
object (self)

  inherit frama_c_inplace

  method! vexpr e =
    match e.enode with
    | CastE (ty, e) when isPointerType ty ->
      let ety = typeOf (stripCastsAndInfo e) in
      if isPointerType ety then
        unify_type_hierarchies ty ety;
      DoChildren
    | _ -> DoChildren

  method! vterm t =
    match t.term_node with
    | TCastE _ ->
      ignore @@ self#vexpr @@ stripInfo @@ fst @@ force_term_to_exp t;
      DoChildren
    | _ -> DoChildren
end

let parent_type = Typ.Hashtbl.create 17

let add_inheritance_relation ty parentty = Typ.Hashtbl.replace parent_type ty parentty

let create_struct_hierarchy file =
  let compute_hierarchy () =
    let module H = Typ.Hashtbl in
    let classes = TypeUF.classes () in
    List.iter
      (fun clss ->
         let types = Typ.Set.elements clss in
         let q = Queue.create () in
         let root =
           List.(fold_left
                   (fun acc ty ->
                      match cmp_subtype acc ty with
                      | `subtype -> ty
                      | `supertype | `neither -> acc)
                   (hd types)
                   types)
         in
         Queue.add root q;
         let bfs ty =
           List.iter
             (fun ty' ->
                match cmp_subtype ty ty' with
                | `supertype ->
                  add_inheritance_relation ty' ty;
                  let ty_fields, parentty_fields = map_pair struct_fields_exn (ty', ty) in
                  List.iter2 add_field_representant (take (List.length parentty_fields) ty_fields) parentty_fields;
                  Queue.add ty' q
                | _ -> ())
             types
         in
         while not (Queue.is_empty q) do bfs @@ Queue.pop q done)
      classes
  in
  visitFramacFile (new struct_hierarchy_builder) file;
  compute_hierarchy ()

let subtype ty parentty =
  let rec subtype ty parentty =
    Typ.equal ty parentty ||
    try
      subtype (Typ.Hashtbl.find parent_type ty) parentty
    with Not_found -> false
  in
  let ty, parentty = map_pair typeDeepDropAllAttributes (ty, parentty) in
  subtype ty parentty

let parent_type =
  typeDeepDropAllAttributes %>
  Typ.Hashtbl.find parent_type

(*****************************************************************************)
(* Retype the C file for Jessie translation.                                 *)
(*****************************************************************************)

let retype file =
  let apply = Rewrite.apply ~file in
  (* Organize structure types in hierarchy. *)
  apply create_struct_hierarchy "organizing structure types in hierarchy."

(*
Local Variables:
compile-command: "make"
End:
*)
