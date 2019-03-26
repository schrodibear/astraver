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

open Stdlib
open Env
open Envset
open Region
open Ast

module rec LocationOrd : Map.OrderedType with type t = Effects.logic_info location =
struct
  type t = Effects.logic_info location
  let compare loc1 loc2 =
    match loc1#node, loc2#node with
    | JCLvar v1, JCLvar v2 -> VarOrd.compare v1 v2
    | JCLvar _v, _ -> 1
    | _, JCLvar _v -> -1
    | _, _ -> 0
    (* TODO: complete def of Location *)
end
and Location : Map.OrderedType with type t = Effects.logic_info location * Memory.t = PairOrd (LocationOrd) (Memory)
and LocationSet : Set.S with type elt = Location.t = Set.Make (Location)
and LocationMap : Map.S with type key = Location.t = Map.Make (Location)
and Effects :
sig
  type effect = {
    e_alloc_tables     : LogicLabelSet.t AllocMap.t;
    e_tag_tables       : LogicLabelSet.t TagMap.t;
    e_raw_memories     : LogicLabelSet.t MemoryMap.t;
    e_precise_memories : LogicLabelSet.t LocationMap.t;
    e_memories         : LogicLabelSet.t MemoryMap.t;
    e_globals          : LogicLabelSet.t VarMap.t;
    e_locals           : LogicLabelSet.t VarMap.t;
    e_mutable          : StringSet.t;
    e_committed        : StringSet.t;
  }

  type fun_effect = {
    fe_reads        : effect;
    fe_writes       : effect;
    fe_raises       : ExceptionSet.t;
    fe_reinterpret  : bool;
  }

  type logic_info = {
            li_tag           : int;
            li_name          : string;
    mutable li_final_name    : string;
    mutable li_result_type   : jc_type option;
    mutable li_result_region : region;
    mutable li_poly_args     : type_var_info list;
    mutable li_parameters    : var_info list;
    mutable li_param_regions : region list;
    mutable li_effects       : effect;
    mutable li_calls         : logic_info list;
    mutable li_axiomatic     : string option;
    mutable li_labels        : label list;
  }

  type builtin_treatment =
  | TreatNothing
  | TreatGenFloat of float_format

  type fun_info =  {
            fun_tag               : int;
            fun_name              : string;
    mutable fun_final_name        : string;
    mutable fun_builtin_treatment : builtin_treatment;
            fun_result            : var_info;
            fun_return_region     : region;
    (* If function has a label "return_label", this is a label denoting
       the return statement of the function, to be used by static
       analysis to avoid merging contexts *)
    mutable fun_has_return_label  : bool;
    mutable fun_parameters        : (bool * var_info) list;
    mutable fun_param_regions     : region list;
    mutable fun_calls             : fun_info list;
    mutable fun_component         : int;
    mutable fun_may_diverge       : bool;
    mutable fun_logic_apps        : logic_info list;
    mutable fun_effects           : fun_effect;
  }
end = Effects

include Effects

module Logic_info =
struct
  type t = logic_info
  let compare li1 li2 = compare li1.li_tag li2.li_tag
  let equal li1 li2 = li1.li_tag = li2.li_tag
end

module Fun_info =
struct
  type t = fun_info
  let compare fi1 fi2 = compare fi1.fun_tag fi2.fun_tag
  let equal fi1 fi2 = fi1.fun_tag = fi2.fun_tag
end

type app = logic_info Ast.app
type term_node = logic_info Ast.term_node
type term = logic_info Ast.term
type tag_node = logic_info Ast.tag_node
type tag = logic_info Ast.tag
type location_set_node = logic_info Ast.location_set_node
type location_set = logic_info Ast.location_set
type location_node = logic_info Ast.location_node
type location = logic_info Ast.location
type assertion = logic_info Ast.assertion
type assertion_node = logic_info Ast.assertion_node
type term_or_assertion = logic_info Ast.term_or_assertion
type loop_annot = logic_info Ast.loop_annot
type behavior = logic_info Ast.behavior
type fun_spec = logic_info Ast.fun_spec

type expr_node = (logic_info, fun_info) Ast.expr_node
type expr = (logic_info, fun_info) Ast.expr
type callee = (logic_info, fun_info) Ast.callee
type call = (logic_info, fun_info) Ast.call

(*
  Local Variables:
  compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
  End:
*)
