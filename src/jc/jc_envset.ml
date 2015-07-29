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



open Stdlib
open Env
open Output_ast

module type OrderedType =
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module type OrderedHashedType =
sig
  include OrderedType
  val hash : t -> int
end

module ChoiceOrd (A : OrderedHashedType) (B : OrderedHashedType) =
struct
  type t = A of A.t | B of B.t
  let equal =
    function
    | A a1, A a2 -> A.equal a1 a2
    | B b1, B b2 -> B.equal b1 b2
    | _ -> false
  let compare =
    function
    | A a1, A a2 -> A.compare a1 a2
    | B b1, B b2 -> B.compare b1 b2
    | A _, _ -> 1
    | B _, _ -> -1
  let hash =
    function
    | A a -> A.hash a
    | B b -> B.hash b
end

module StringSet = Set.Make (String)

module StringMap = Map.Make (String)

(* used names (in order to rename identifiers when necessary) *)
let used_names = Hashtbl.create 97

let mark_as_used x = Hashtbl.add used_names x ()

let () =
  List.iter mark_as_used
    [ (* Why keywords *)
      "absurd"; "and"; "array"; "as"; "assert"; "axiom"; "begin";
      "bool"; "do"; "done"; "else"; "end"; "exception"; "exists";
      "external"; "false"; "for"; "forall"; "fun"; "function"; "goal";
      "if"; "in"; "int"; "invariant"; "label"; "let"; "logic"; "not";
      "of"; "old"; "or"; "parameter"; "predicate"; "prop"; "raise"; "raises";
      "reads"; "real"; "rec"; "ref"; "result"; "returns"; "then"; "true"; "try";
      "type"; "unit"; "variant"; "void"; "while"; "with"; "writes";
      (* Why prelude *)
      "exp" ; "log" ; "sin" ; "cos" ; "tan" ; "sqr_real" ; "atan" ;
      (* jessie generated names *)
      "shift"; "init"; "start"; "valid"
      (* "global" ; "alloc"  *)
    ]

let is_used_name n = Hashtbl.mem used_names n

let use_name ?local_names n =
  if is_used_name n then raise Exit;
  begin match local_names with
  | Some h -> if StringSet.mem n h then raise Exit
  | None -> ()
  end;
  mark_as_used n;
  n

let rec next_name ?local_names n i =
  let n_i = n ^ "_" ^ string_of_int i in
  try use_name ?local_names n_i
  with Exit -> next_name ?local_names n (succ i)

let get_unique_name ?local_names n =
  try use_name ?local_names n
  with Exit -> next_name ?local_names n 0

let is_pointer_type t =
  match t with
  | JCTnull -> true
  | JCTpointer _ -> true
  | _ -> false

let is_nonnull_pointer_type t =
  match t with
  | JCTpointer _ -> true
  | _ -> false

let is_integral_type =
  function
  | JCTnative Tinteger -> true
  | JCTenum _ -> true
  | JCTnative _ | JCTlogic _ | JCTpointer _ | JCTnull | JCTany
  | JCTtype_var _ -> false

let is_embedded_field fi =
  match fi.fi_type with
  | JCTpointer(_, Some _, Some _) -> true
  | _ -> false

module type Tag =
sig
  type t
  val tag_of_val : t -> int
end

module OrderedHashedTypeOfTag (X : Tag) : OrderedHashedType with type t = X.t =
struct
  type t = X.t
  let compare v1 v2 = Pervasives.compare (X.tag_of_val v1) (X.tag_of_val v2)
  let equal v1 v2 = (X.tag_of_val v1) = (X.tag_of_val v2)
  let hash v = Hashtbl.hash (X.tag_of_val v)
end

module VarOrd =
  OrderedHashedTypeOfTag
    (struct
      type t = var_info
      let tag_of_val x = x.vi_tag
     end)

module VarSet = Set.Make (VarOrd)

module VarMap = Map.Make (VarOrd)

module StructOrd =
struct
  type t = struct_info
  let compare st1 st2 = Pervasives.compare st1.si_name st2.si_name
  let equal st1 st2 = st1.si_name = st2.si_name
  let hash st = Hashtbl.hash st.si_name
end

module StructSet = Set.Make (StructOrd)

module StructMap = Map.Make (StructOrd)

module VariantOrd =
struct
  type t = root_info
  let compare v1 v2 = Pervasives.compare v1.ri_name v2.ri_name
  let equal v1 v2 = v1.ri_name = v2.ri_name
  let hash v = Hashtbl.hash v.ri_name
end

module VariantSet = Set.Make (VariantOrd)

module VariantMap = Map.Make (VariantOrd)

module FieldOrd =
  OrderedHashedTypeOfTag
    (struct
      type t = field_info
      let tag_of_val x = x.fi_tag
     end)

module FieldSet = Set.Make (FieldOrd)

module FieldMap = Map.Make (FieldOrd)

module FieldTable = Hashtbl.Make (FieldOrd)

module MemClass =
struct
  type t = mem_class
  let equal fv1 fv2 =
    match fv1, fv2 with
    | JCmem_field a1, JCmem_field a2 -> FieldOrd.equal a1 a2
    | JCmem_plain_union b1, JCmem_plain_union b2 -> VariantOrd.equal b1 b2
    | JCmem_bitvector, JCmem_bitvector -> true
    | _ -> false
  let compare fv1 fv2 =
    match fv1, fv2 with
    | JCmem_field a1, JCmem_field a2 -> FieldOrd.compare a1 a2
    | JCmem_plain_union b1, JCmem_plain_union b2 -> VariantOrd.compare b1 b2
    | JCmem_bitvector, JCmem_bitvector -> 0
    | JCmem_field _, _ -> 1
    | _, JCmem_field _ -> -1
    | JCmem_plain_union _, _ -> 1
    | _, JCmem_plain_union _ -> -1
  let hash =
    function
    | JCmem_field a -> FieldOrd.hash a
    | JCmem_plain_union b -> VariantOrd.hash b
    | JCmem_bitvector -> 0
end

module MemClassSet = Set.Make(MemClass)

module AllocClass =
struct
  type t = alloc_class
  let equal fv1 fv2 =
    match fv1, fv2 with
    | JCalloc_root st1, JCalloc_root st2 -> VariantOrd.equal st1 st2
    | JCalloc_bitvector, JCalloc_bitvector -> true
    | _ -> false
  let compare fv1 fv2 =
    match fv1, fv2 with
    | JCalloc_root a1, JCalloc_root a2 -> VariantOrd.compare a1 a2
    | JCalloc_bitvector, JCalloc_bitvector -> 0
    | JCalloc_root _, _ -> 1
    | _, JCalloc_root _ -> -1
  let hash =
    function
    | JCalloc_root a -> VariantOrd.hash a
    | JCalloc_bitvector -> 0
end

(* TODO: take into account type parameters *)
module PointerClass =
struct
  type t = pointer_class
  let equal fv1 fv2 =
    match fv1, fv2 with
    | JCtag (st1, _), JCtag (st2, _) -> StructOrd.equal st1 st2
    | JCroot vi1, JCroot vi2 -> VariantOrd.equal vi1 vi2
    | _ -> false
  let compare fv1 fv2 = match fv1,fv2 with
    | JCtag (a1, _), JCtag (a2, _) -> StructOrd.compare a1 a2
    | JCroot b1, JCroot b2 -> VariantOrd.compare b1 b2
    | JCtag _, _ -> 1
    | _, JCtag _ -> -1
  let hash =
    function
    | JCtag (a, _) -> StructOrd.hash a
    | JCroot b -> VariantOrd.hash b
end

module ExceptionOrd =
  OrderedHashedTypeOfTag
    (struct
      type t = exception_info
      let tag_of_val x = x.exi_tag
     end)

module ExceptionSet = Set.Make (ExceptionOrd)

module ExceptionMap = Map.Make (ExceptionOrd)

module LogicLabelOrd =
struct
  type t = label
  let compare = (Pervasives.compare : label -> label -> int)
end

module LogicLabelSet = Set.Make (LogicLabelOrd)

module TypeVarOrd =
  OrderedHashedTypeOfTag
    (struct
      type t = type_var_info
      let tag_of_val x = x.tvi_tag
     end)

module TypeVarMap = Map.Make (TypeVarOrd)

let enum =
  let h = Hashtbl.create 10 in
  fun name ->
    try
      Hashtbl.find h name
    with
    | Not_found ->
      let e =
        (module
        struct
          type t
          type _ enum += E : t enum
          let name = name
        end : Enum)
      in
      Hashtbl.add h name e;
      e

(*
Local Variables:
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End:
*)
