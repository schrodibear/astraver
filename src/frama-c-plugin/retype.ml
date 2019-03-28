(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2015                                               *)
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
(*  AstraVer fork:                                                        *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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
  let norm = typeRemoveAttributes [Name.Attr.embedded] in
  fi1.forig_name = fi2.forig_name &&
  Typ.equal (norm fi1.ftype) (norm fi2.ftype)

let struct_fields_exn ty =
  match unrollType ty with
  | TComp (compinfo, _, _) ->
    List.filter (fun fi -> not @@ hasAttribute Name.Attr.padding fi.fattr) compinfo.cfields |>
    begin function [] when compinfo.cfields <> [] -> [List.hd compinfo.cfields] | fields -> fields end
  | t -> Console.fatal "struct_fields: non-composite type %a" Printer.pp_typ t

let ty_void, ty_char = Type.Composite.Struct.(lazy (void () :> typ), lazy (char () :> typ))

let cmp_subtype =
  let cache =
    let module H = Datatype.Pair_with_collections (Typ) (Typ) (struct let module_name = "type_pair" end) in
    let module H = H.Hashtbl in
    let h = H.create 25 in
    fun f ty1 ty2 ->
      try H.find h (ty1, ty2)
      with
      | Not_found ->
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
        (List.take min_length ty1_fields)
        (List.take min_length ty2_fields)
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
        List.(length % filterAttributes Name.Attr.embedded % (fun fi -> fi.fattr) % hd)
        (ty1_fields, ty2_fields)
    in
    if ty1_n_embedded_attrs < ty2_n_embedded_attrs then
      `supertype
    else if ty2_n_embedded_attrs < ty1_n_embedded_attrs then
      `subtype
    else
      `neither
  else if Typ.(equal ty1 !!ty_void && not (equal ty2 !!ty_void)) then
    `supertype
  else if Typ.(not (equal ty1 !!ty_void) && equal ty2 !!ty_void) then
    `subtype
  else
    `neither

class struct_hierarchy_builder () =
  let unify_type_hierarchies ty1 ty2 =
    if List.for_all (Type.Composite.Struct.is_struct % pointed_type) [ty1; ty2] then
      (* Extract info from types *)
      let struct_ty_of_ty_exn ty =
        match unrollType (pointed_type ty) with
        | TComp (ci, _, _) when ci.cstruct -> typeDeepDropAllAttributes @@ TComp (ci, empty_size_cache (), [])
        | t -> Console.fatal "unify_type_hierarchies: non-structure type %a" Printer.pp_typ t
      in
      let ty1, ty2 = map_pair struct_ty_of_ty_exn (ty1, ty2) in
      (* Compare types *)
      match cmp_subtype ty1 ty2 with
      | `supertype when not (Typ.equal ty1 !!ty_char) ->
        (* [ty2] subtype of [ty1] *)
        add_inheritance_relation ty2 ty1
      | `subtype when not (Typ.equal ty2 !!ty_char) ->
        (* [ty1] subtype of [ty2] *)
        add_inheritance_relation ty1 ty2
      | `neither | _ ->
        (* no subtyping relation, but in order to allow side-casts we still
           need both types to be in the same hierarchy, therefore unifying both with void *)
        add_inheritance_relation ty1 !!ty_void;
        add_inheritance_relation ty2 !!ty_void
  in
  let is_pointer_type ty =
    match unrollType ty with
    | TPtr _ | TArray _ -> true
    | _ -> false
  in
object (self)

  inherit frama_c_inplace

  method! vexpr e =
    match e.enode with
    | CastE (ty, _, e) when is_pointer_type ty ->
      let ety = typeOf (stripInfo e) in
      if is_pointer_type ety then
        unify_type_hierarchies ty ety;
      DoChildren
    | CastE (_, _, { enode = AddrOf (Mem { enode = CastE (bt, _, z) }, off) })
      when isZero z && is_pointer_type bt && isStructOrUnionType (pointed_type bt) ->
      let rec loop =
        function
        | Field (fi, off) when fi.fcomp.cstruct ->
          unify_type_hierarchies fi.ftype bt;
          loop off
        | Field (_, off) -> loop off
        | NoOffset -> ()
        | Index _ as off -> Console.fatal "struct_hierarchy_builder: impossible index: %a" Printer.pp_offset off
      in
      loop off;
      SkipChildren
    | _ -> DoChildren

  method! vterm t =
    match t.term_node with
    | TCastE _ ->
      ignore @@ self#vexpr @@ stripInfo @@ fst @@ Ast.Term.to_exp_env t;
      DoChildren
    | TOffsetOf fi when is_pointer_type fi.ftype ->
      unify_type_hierarchies fi.ftype (TPtr (TComp (fi.fcomp, empty_size_cache (), []), []));
      SkipChildren
    | _ -> DoChildren

  method! vinst =
    function
    | Call (Some lv, e, _, _) ->
      let lvty = typeOfLval lv in
      begin match unrollType (typeOf e) with
      | TFun (rt, _, _, _) when need_cast rt lvty ->
        if is_pointer_type lvty && is_pointer_type rt then
          unify_type_hierarchies lvty rt
      | _ -> ()
      end;
      DoChildren
    | _ -> DoChildren

  method! vjessie_pragma (JPexpr t) =
    match t.term_node with
    | TCoerce (t, typ) when Logic_utils.isLogicType is_pointer_type t.term_type && is_pointer_type typ ->
      unify_type_hierarchies (Logic_utils.logicCType t.term_type) typ;
      SkipChildren
    | _ -> SkipChildren
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
                let above_child = cmp_subtype ty ty' = `supertype in
                let below_parent =
                  try cmp_subtype ty (Typ.Hashtbl.find parent_type ty') = `subtype with Not_found -> true
                in
                if above_child && below_parent then begin
                   add_inheritance_relation ty' ty;
                   let ty_fields, parentty_fields = map_pair struct_fields_exn (ty', ty) in
                   List.iter2 add_field_representant List.(take (length parentty_fields) ty_fields) parentty_fields;
                   Queue.add ty' q
                end)
             types
         in
         while not (Queue.is_empty q) do bfs @@ Queue.pop q done)
      classes
  in
  visitFramacFile (new struct_hierarchy_builder ()) file;
  Type.Composite.Struct.(TypeUF.unify (char () :> typ) (void () :> typ));
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

let parent_type ty =
  try Some (Typ.Hashtbl.find parent_type @@ typeDeepDropAllAttributes ty)
  with Not_found -> None

(*****************************************************************************)
(* Retype the C file for Jessie translation.                                 *)
(*****************************************************************************)

let retype file =
  let apply = Rewrite.apply ~file in
  (* Organize structure types in hierarchy. *)
  apply create_struct_hierarchy "organizing structure types in hierarchy."
