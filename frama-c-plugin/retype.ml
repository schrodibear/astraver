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
(* Retype int field used as pointer.                                         *)
(*****************************************************************************)

class collect_int_field_visitor (cast_field_to_type : typ H.t) =
object

  inherit frama_c_inplace

  method! vexpr e =
    match e.enode with
    | CastE (ty, e) ->
      if isPointerType ty then
        begin match (stripCastsAndInfo e).enode with
        | Lval (_host, off) ->
          begin match lastOffset off with
          | Field (fi, _) when isIntegralType fi.ftype && bits_sizeof ty = bits_sizeof fi.ftype ->
            H.replace cast_field_to_type fi fi.ftype
          | _ -> ()
          end
        | _ -> ()
        end;
      DoChildren
    | _ -> DoChildren
end

class retype_int_field_visitor (cast_field_to_type : typ H.t) =
  let postaction_expr e =
    match e.enode with
    | Lval (_host, off) ->
      begin match lastOffset off with
      | Field(fi, _) ->
        begin try
          new_exp ~loc:e.eloc @@ CastE (H.find cast_field_to_type fi, e)
        with
        | Not_found -> e
        end
      | _ -> e
      end
    | _ -> e
  in
object

  inherit frama_c_inplace

  method! vglob_aux = function
    | GCompTag (compinfo, _) ->
        let fields = compinfo.cfields in
        let field fi =
          if H.mem cast_field_to_type fi then
            fi.ftype <- TPtr (!Common.struct_type_for_void, [])
        in
        List.iter field fields;
        DoChildren
    | _ -> DoChildren

  method! vterm = do_on_term (None, Some postaction_expr)
end

let retype_int_field file =
  let cast_field_to_type = H.create 17 in
  visitFramacFile (new collect_int_field_visitor cast_field_to_type) file;
  visitFramacFile (new retype_int_field_visitor cast_field_to_type) file


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

let add_field_representant fi1 fi2 =
  FieldUF.unify fi1 fi2

module Type_elem = struct include Typ let prefer _ _ = 0 end
module TypeUF = Union_find (Type_elem) (Typ.Set) (Typ.Hashtbl)

let parent_type = Typ.Hashtbl.create 17

let add_inheritance_relation ty parentty =
  if not @@ Typ.equal ty parentty then begin
    Typ.Hashtbl.replace parent_type ty parentty;
    TypeUF.unify ty parentty
  end

let rec subtype ty parentty =
  Typ.equal ty parentty ||
  try
    subtype (Typ.Hashtbl.find parent_type ty) parentty
  with Not_found -> false

let same_fields fi1 fi2 =
  let norm = typeRemoveAttributes [embedded_attr_name] in
  fi1.forig_name = fi2.forig_name &&
  Typ.equal (norm fi1.ftype) (norm fi2.ftype)

class struct_hierarchy_builder =
  let unify_type_hierarchies ty1 ty2 =
    (* Extract info from types *)
    let compinfo1 = match unrollType (pointed_type ty1) with
      | TComp (compinfo, _, _) -> compinfo
      | t -> fatal "unify_type_hierarchies: non-composite type %a" Printer.pp_typ t
    in
    let sty1 = TComp (compinfo1, empty_size_cache (), []) in
    let fields1 = compinfo1.cfields in
    let compinfo2 = match unrollType (pointed_type ty2) with
      | TComp (compinfo, _ ,_) -> compinfo
      | t -> fatal "unify_type_hierarchies: non-composite type %a" Printer.pp_typ t
    in
    let fields2 = compinfo2.cfields in
    let sty2 = TComp (compinfo2, empty_size_cache (), []) in
    (* Compare types *)
    let minlen = min (List.length fields1) (List.length fields2) in
    let prefix, complete =
      List.fold_left2
        (fun (acc, compl) f1 f2 ->
          if compl && same_fields f1 f2 then f1 :: acc, compl
                                        else acc, false)
        ([], true)
        (take minlen fields1) (take minlen fields2)
    in
    let prefix = List.rev prefix in
    if complete then
      if List.length prefix = List.length fields1 then
        (* [ty2] subtype of [ty1] *)
        add_inheritance_relation sty2 sty1
      else
        (* [ty1] subtype of [ty2] *)
        add_inheritance_relation sty1 sty2
  in
object (self)

  inherit frama_c_inplace

  method! vexpr e =
    match e.enode with
    | CastE (ty,e) when isPointerType ty ->
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

let create_struct_hierarchy file =
  let struct_fields ty =
    match unrollType ty with
    | TComp (compinfo, _, _) -> compinfo.cfields
    | t -> fatal "struct_fields: non-composite type %a" Printer.pp_typ t
  in
  let num_fields ty = List.length (struct_fields ty) in
  let compare_num_fields ty1 ty2 = num_fields ty1 - num_fields ty2 in
  let subtype ty1 ty2 =
    let fields1, fields2 = map_pair struct_fields (ty1, ty2) in
    let len1, len2 = map_pair List.length (fields1, fields2) in
    len1 > len2 &&
    List.fold_left2
      (fun eq fi1 fi2 -> eq && same_fields fi1 fi2)
      true
      (take len2 fields1)
      fields2
  in
  let compute_hierarchy () =
    let module H = Typ.Hashtbl in
    let classes = TypeUF.classes () in
    List.iter
      (fun cls ->
        let types = Typ.Set.elements cls in
        let types = List.sort compare_num_fields types in
        let root, types = List.(fdup2 hd tl types) in
        (* First element is new root *)
        H.remove parent_type root;
        List.iter
          (fun ty ->
            add_inheritance_relation ty root;
            List.iter
              (fun party ->
                if subtype ty party then
                  add_inheritance_relation ty party)
              types)
          types)
      classes;
    H.iter
      (fun ty party ->
        let fields1 = struct_fields ty in
        let fields2 = struct_fields party in
        let num2 = List.length fields2 in
        let subfields1 = take num2 fields1 in
        List.iter2 add_field_representant subfields1 fields2)
      parent_type
  in
  visitFramacFile (new struct_hierarchy_builder) file;
  compute_hierarchy ()

let parent_type = Typ.Hashtbl.find parent_type

(*****************************************************************************)
(* Retype the C file for Jessie translation.                                 *)
(*****************************************************************************)

let retype file =
  let apply = Rewrite.apply ~file in
  (* Retype int field casted to pointer. *)
  apply retype_int_field "retyping int field casted to pointer.";
  (* Organize structure types in hierarchy. *)
  apply create_struct_hierarchy "organizing structure types in hierarchy."

(*
Local Variables:
compile-command: "make"
End:
*)
