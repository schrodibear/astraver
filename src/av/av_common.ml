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
open Envset
open Region
open Output_ast
open Ast
open Fenv

open Constructors

open Format
open Num

exception Error of Why_loc.position * string

let error l =
  Format.kfprintf
    (fun _fmt -> raise (Error (l, flush_str_formatter ())))
    str_formatter

let zero = Num.Int 0
let one = Num.Int 1
let two = Num.Int 2
let eight = Num.Int 8

let rec is_power_of_two i =
  if i <=/ zero then
    false
  else
    i =/ one || mod_num i two =/ zero && is_power_of_two (i // two)

let rec log2 i =
  assert (i >/ zero);
  if i =/ one then zero else one +/ log2 (i // two)

let operator_of_format (f : float_format) =
  match f with
    | `Float -> `Float
    | `Double -> `Double
    | `Binary80 -> `Binary80

let operator_of_native t =
  match t with
  | Tunit -> `Unit
  | Tboolean -> `Boolean
  | Tinteger -> `Integer
  | Treal -> `Real
  | Tgenfloat f -> operator_of_format f
  | Tstring -> assert false

let operator_of_type =
  function
  | JCTnative n -> operator_of_native n
  | JCTenum ei -> `Enum ei
  | JCTlogic _ -> `Logic
  | JCTany | JCTtype_var _ -> assert false (* TODO? *)
  | JCTnull | JCTpointer _ -> `Pointer

let eq_operator_of_type =
  function
  | JCTnative n -> operator_of_native n
  | JCTenum _ | JCTlogic _ -> `Logic
  | JCTany | JCTtype_var _ -> assert false (* TODO? *)
  | JCTnull | JCTpointer _ -> `Pointer

let new_label_name =
  let label_name_counter = ref 0 in
  fun () ->
    incr label_name_counter;
    "JC_" ^ string_of_int !label_name_counter

let root_name st =
  st.si_hroot.si_name

let field_root_name fi =
  fi.fi_hroot.si_name

let string_of_format f =
  match f with
  | `Double -> "double"
  | `Float -> "float"
  | `Binary80 -> "binary80"

let string_of_native t =
  match t with
  | Tunit -> "unit"
  | Tinteger -> "integer"
  | Treal -> "real"
  | Tgenfloat f -> string_of_format f
  | Tboolean -> "boolean"
  | Tstring -> "string"

let print_type_var fmt v = fprintf fmt "(var_%s_%d)" v.tvi_name v.tvi_tag

let string_of_some_enum =
  let range  (type a) =
    function
    | (Signed : a repr) -> ""
    | Unsigned -> "u"
  in
  let bit (type a) =
    function
    | (X8 : a bit) -> "8"
    | X16 -> "16"
    | X32 -> "32"
    | X64 -> "64"
  in
  function
  | (Int (r, b) : some_enum) -> range r ^ "int" ^ bit b
  | Enum (module E) -> E.name

let rec print_type fmt t =
  match t with
  | JCTnative n -> fprintf fmt "%s" (string_of_native n)
  | JCTlogic (s,l) -> fprintf fmt "%s%a" s Why_pp.(print_list_delim lchevron rchevron comma print_type) l
  | JCTenum ri -> fprintf fmt "%s" (string_of_some_enum ri.ei_type)
  | JCTpointer(pc, ao, bo) ->
    begin match pc with
    | JCtag({ si_name = name }, [])
    | JCroot { ri_name = name } ->
      fprintf fmt "%s" name
    | JCtag({ si_name = name }, params) ->
      fprintf fmt "%s<%a>" name
        Why_pp.(print_list comma print_type) params
    end;
    begin match ao, bo with
    | None, None ->
      fprintf fmt "[..]"
    | Some a, None ->
      fprintf fmt "[%s..]" (Num.string_of_num a)
    | None, Some b ->
      fprintf fmt "[..%s]" (Num.string_of_num b)
    | Some a, Some b ->
      if Num.eq_num a b then
        fprintf fmt "[%s]" (Num.string_of_num a)
      else
        fprintf fmt "[%s..%s]" (Num.string_of_num a) (Num.string_of_num b)
    end
    | JCTnull -> fprintf fmt "(nulltype)"
    | JCTany -> fprintf fmt "(anytype)"
    | JCTtype_var v -> print_type_var fmt v

let num_of_constant _loc c =
  match c with
  | JCCinteger n -> Num.num_of_string n
  | _ -> invalid_arg "num_of_constant"

let zero = Num.num_of_int 0
let minus_one = Num.num_of_int (-1)

let rec location_set_region locs =
  match locs#node with
  | JCLSvar vi -> vi.vi_region
  | JCLSderef (_, _, _, r) -> r
  | JCLSrange (ls, _, _) -> location_set_region ls
  | JCLSrange_term (t1, _, _) -> t1#region
  | JCLSat (ls, _) -> location_set_region ls

let rec location_set_of_location =
  let zero = Term.mkint ~value:0 () in
  fun loc ->
    let node =
      match loc#node with
      | JCLvar v -> JCLSvar v
      | JCLderef (ls, lab, fi, r) ->
        JCLSderef (ls, lab, fi, r)
      | JCLderef_term (t, fi) ->
        let locs = location_set_with_node t @@ JCLSrange_term (t, Some zero, Some zero) in
        JCLSderef (locs, loc#label |? LabelHere, fi, loc#region)
      | JCLsingleton t ->
        JCLSrange_term (t, Some zero, Some zero)
      | JCLat (ls, lab) -> JCLSat (location_set_of_location ls, lab)
    in
    location_set_with_node loc node

type location =
  | JCLvar of var_info
  | JCLderef of location_set * field_info * region

(* operators *)

let is_relation_binary_op = function
  | `Blt | `Bgt | `Ble | `Bge | `Beq | `Bneq -> true
  | _ -> false

let is_logical_binary_op = function
  | `Bland | `Blor | `Bimplies | `Biff -> true
  | _ -> false

let is_arithmetic_binary_op = function
  | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod -> true
  | _ -> false

let is_bitwise_binary_op = function
  | `Bbw_and | `Bbw_or | `Bbw_xor
  | `Bshift_left | `Blogical_shift_right | `Barith_shift_right -> true
  | _ -> false

let is_logical_unary_op = function
  | `Unot -> true
  | _ -> false

let is_arithmetic_unary_op = function
  | `Uminus -> true
  | _ -> false

let is_bitwise_unary_op = function
  | `Ubw_not -> true
  | _ -> false

(* native types *)

let unit_type = JCTnative Tunit
let boolean_type = JCTnative Tboolean
let integer_type = JCTnative Tinteger
let real_type = JCTnative Treal
let double_type = JCTnative (Tgenfloat `Double)
let float_type = JCTnative (Tgenfloat `Float)
let null_type = JCTnull
let string_type = JCTnative Tstring
let any_type = JCTany

(* temporary variables *)

let tempvar_count = ref 0
(* let reset_tmp_var () = tempvar_count := 0 *)
let tmp_var_name () =
  incr tempvar_count; "_jessie_" ^ string_of_int !tempvar_count

(* variables *)

let var_tag_counter = ref 0

let var ?(unique=true) ?(static=false) ?(formal=false) ?(bound=false) ty id =
  incr var_tag_counter;
  let vi = {
    vi_tag = !var_tag_counter;
    vi_name = id;
    vi_final_name =
      if unique then Envset.get_unique_name id else id;
    vi_region =
      if static then Region.make_const ty id else Region.make_var ty id;
    vi_type = ty;
    vi_formal = formal;
    vi_assigned = false;
    vi_static = static;
    vi_bound = bound
  }
  in vi

let newvar ty = var ty (tmp_var_name())

let newrefvar ty =
  let vi = newvar ty in
    vi.vi_assigned <- true;
    vi

let copyvar vi =
  incr var_tag_counter;
  { vi with
    vi_tag = !var_tag_counter;
    vi_name =
      "__jc_" ^ (string_of_int !var_tag_counter) ^ vi.vi_name;
    vi_final_name =
      "__jc_" ^ (string_of_int !var_tag_counter) ^ vi.vi_final_name;
  }

(* exceptions *)

let exception_tag_counter = ref 0

let exception_info ty id =
  incr exception_tag_counter;
  let ei = {
    exi_tag = !exception_tag_counter;
    exi_name = id;
    exi_type = ty;
  }
  in ei


(* logic functions *)

let empty_effects =
  { e_alloc_tables = AllocMap.empty;
    e_tag_tables = TagMap.empty;
    e_raw_memories = MemoryMap.empty;
    e_precise_memories = LocationMap.empty;
    e_memories = MemoryMap.empty;
    e_globals = VarMap.empty;
    e_locals = VarMap.empty;
    e_mutable = StringSet.empty;
    e_committed = StringSet.empty;
  }

let empty_logic_info =
  {
    li_tag = 0;
    li_name = "";
    li_final_name = "";
    li_result_type = None;
    li_result_region = dummy_region; (* TODO *)
    li_poly_args = [];
    li_parameters = [];
    li_param_regions = [];
    li_effects = empty_effects;
    li_calls = [];
(*
    li_is_recursive = false;
*)
    li_axiomatic = None;
    li_labels = [];
  }

let logic_fun_tag_counter = ref 0

let make_logic_fun name ty =
  incr logic_fun_tag_counter;
  { li_tag = !logic_fun_tag_counter;
    li_name = name;
    li_final_name = Envset.get_unique_name name;
    li_result_type = Some ty;
    li_result_region = Region.make_var ty name;
    li_poly_args = [];
    li_parameters = [];
    li_param_regions = [];
    li_effects = empty_effects;
    li_calls = [];
(*
    li_is_recursive = false;
*)
    li_axiomatic = None;
    li_labels = [];
  }

let any_string = make_logic_fun "any_string" string_type

(*
let () =
  let vi = var ~formal:true integer_type "n" in
  real_of_integer.li_parameters <- [vi]
*)

let full_separated = make_logic_fun "full_separated" null_type

(* logic predicates *)

let make_pred name =
  incr logic_fun_tag_counter;
  { li_tag = !logic_fun_tag_counter;
    li_name = name;
    li_final_name = Envset.get_unique_name name;
    li_result_type = None;
    li_result_region = dummy_region;
    li_poly_args = [];
    li_parameters = [];
    li_param_regions = [];
    li_effects = empty_effects;
    li_calls = [];
(*
    li_is_recursive = false;
*)
    li_labels = [];
    li_axiomatic = None;
  }


(* programs *)

let empty_fun_effect =
  { fe_reads = empty_effects;
    fe_writes = empty_effects;
    fe_raises = ExceptionSet.empty;
    fe_reinterpret = false
  }

let fun_tag_counter = ref 0

let make_fun_info name ty =
  incr fun_tag_counter;
  let vi = var ty "\\result" in
  vi.vi_final_name <- "result";
  { fun_tag = !fun_tag_counter;
    fun_name = name;
    fun_final_name = Envset.get_unique_name name;
    fun_builtin_treatment = TreatNothing;
    fun_parameters = [];
    fun_result = vi;
    fun_return_region = vi.vi_region;
    fun_has_return_label = false;
    fun_param_regions = [];
    fun_calls = [];
    fun_component = -1;
    fun_may_diverge = false;
    fun_logic_apps = [];
    fun_effects = empty_fun_effect;
  }


let option_compare comp opt1 opt2 = match opt1,opt2 with
  | None,None -> 0
  | None,Some _ -> -1
  | Some _,None -> 1
  | Some x,Some y -> comp x y

let rec list_compare comp ls1 ls2 = match ls1,ls2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | x1::r1,x2::r2 ->
      let compx = comp x1 x2 in
      if compx = 0 then list_compare comp r1 r2 else compx



(* terms *)

let rec is_constant_term t =
  match t#node with
    | JCTrange (None, None) (* CORRECT ? *)
    | JCTconst _ -> true
    | JCTvar _ | JCTshift _ | JCTderef _
    | JCTapp _ | JCTold _ | JCTat _ | JCToffset _ | JCTaddress _
    | JCTbase_block _
    | JCTinstanceof _ | JCTdowncast _ | JCTsidecast _ | JCTrange_cast _ | JCTrange_cast_mod _
    | JCTreal_cast _ | JCTif _ | JCTlet _ | JCTmatch _ -> false
    | JCTbinary (t1, _, t2) | JCTrange (Some t1, Some t2) ->
        is_constant_term t1 && is_constant_term t2
    | JCTunary (_, t) | JCTrange (Some t, None) | JCTrange (None, Some t) ->
        is_constant_term t

(* Comparison based only on term structure, not types not locations. *)
module TermOrd = struct
  type t = term

  let term_num t = match t#node with
    | JCTconst _ -> 1
    | JCTvar _ -> 3
    | JCTbinary _ -> 5
    | JCTshift _ -> 7
    | JCTunary _ -> 13
    | JCTderef _ -> 17
    | JCTold _ -> 19
    | JCToffset _ -> 23
    | JCTaddress _ -> 25
    | JCTinstanceof _ -> 31
    | JCTdowncast _ -> 37
    | JCTsidecast _ -> 39
    | JCTrange _ -> 41
    | JCTapp _ -> 43
    | JCTif _ -> 47
    | JCTat _ -> 53
    | JCTmatch _ -> 59
    | JCTrange_cast _ -> 61
    | JCTrange_cast_mod _ -> 62
    | JCTreal_cast _ -> 67
    | JCTbase_block _ -> 71
    | JCTlet _ -> 73

  let rec compare t1 t2 =
    match t1#node, t2#node with
      | JCTconst c1,JCTconst c2 ->
          Pervasives.compare c1 c2
      | JCTvar v1,JCTvar v2 ->
          Pervasives.compare v1.vi_tag v2.vi_tag
      | JCTbinary(t11,op1,t12),JCTbinary(t21,op2,t22) ->
          let compop = Pervasives.compare op1 op2 in
          if compop = 0 then
            let comp1 = compare t11 t21 in
            if comp1 = 0 then compare t12 t22 else comp1
          else compop
      | JCTshift(t11,t12),JCTshift(t21,t22) ->
          let comp1 = compare t11 t21 in
          if comp1 = 0 then compare t12 t22 else comp1
      | JCTunary(op1,t11),JCTunary(op2,t21) ->
          let compop = Pervasives.compare op1 op2 in
          if compop = 0 then compare t11 t21 else compop
      | JCTold t11,JCTold t21 ->
          compare t11 t21
      | JCTaddress(absolute1,t11),JCTaddress(absolute2,t21) ->
          let compabs = Pervasives.compare absolute1 absolute2 in
          if compabs = 0 then
            compare t11 t21
          else compabs
      | JCTderef(t11,_,fi1),JCTderef(t21,_,fi2) ->
          let compfi =
            Pervasives.compare fi1.fi_tag fi2.fi_tag
          in
          if compfi = 0 then compare t11 t21 else compfi
      | JCToffset(ok1,t11,st1),JCToffset(ok2,t21,st2) ->
          let compok = Pervasives.compare ok1 ok2 in
          if compok = 0 then
            let compst =
              Pervasives.compare st1.si_name st2.si_name
            in
            if compst = 0 then compare t11 t21 else compst
          else compok
      | JCTinstanceof (t11, lab1, st1), JCTinstanceof (t21, lab2, st2)
      | JCTdowncast (t11, lab1, st1), JCTdowncast (t21, lab2, st2)
      | JCTsidecast (t11, lab1, st1), JCTsidecast (t21, lab2, st2) ->
          let compst =
            Pervasives.compare st1.si_name st2.si_name
          in
          if compst <> 0 then compst else
            let compst =
              Pervasives.compare lab1 lab2
            in
            if compst <> 0 then compst else
              compare t11 t21
      | JCTreal_cast(t11,conv1),JCTreal_cast(t21,conv2) ->
          let comp =
            Pervasives.compare conv1 conv2
          in
          if comp <> 0 then comp else
            compare t11 t21
      | JCTrange_cast(t11, None), JCTrange_cast(t21, None) -> compare t11 t21
      | JCTrange_cast(_, Some _), JCTrange_cast(_, None) -> 1
      | JCTrange_cast(_, None), JCTrange_cast(_, Some _) -> -1
      | JCTrange_cast(t11, Some ri1),JCTrange_cast(t21, Some ri2) ->
          let comp =
            Pervasives.compare ri1.ei_type ri2.ei_type
          in
          if comp <> 0 then comp else
            compare t11 t21
      | JCTrange(t11opt,t12opt),JCTrange(t21opt,t22opt) ->
          let comp1 = option_compare compare t11opt t21opt in
          if comp1 = 0 then
            option_compare compare t12opt t22opt
          else comp1
      | JCTapp app1,JCTapp app2 ->
          let li1 = app1.app_fun and ts1 = app1.app_args in
          let li2 = app2.app_fun and ts2 = app2.app_args in
          let compli =
            Pervasives.compare li1.li_tag li2.li_tag
          in
          if compli = 0 then
            list_compare compare ts1 ts2
          else compli
      | JCTif(t11,t12,t13),JCTif(t21,t22,t23) ->
          let comp1 = compare t11 t21 in
          if comp1 = 0 then
            let comp2 = compare t12 t22 in
            if comp2 = 0 then compare t13 t23 else comp2
          else comp1
      |JCTat(t11,lab1),JCTat(t21,lab2) ->
         let compst =
           Pervasives.compare lab1 lab2
         in
         if compst <> 0 then compst else
           compare t11 t21
      | JCTmatch _, JCTmatch _ -> assert false (* TODO *)
      | JCTbase_block t11, JCTbase_block t21 ->
          compare t11 t21
      | _ ->
          (* Terms should have different constructors *)
          assert (term_num t1 <> term_num t2);
          term_num t2 - term_num t1

  let equal t1 t2 = compare t1 t2 = 0

  let rec hash t =
    let h = match t#node with
      | JCTconst c1 ->
          Hashtbl.hash c1
      | JCTvar v1 ->
          Hashtbl.hash v1.vi_tag
      | JCTbinary(t11,op1,t12) ->
          Hashtbl.hash op1 * hash t11 * hash t12
      | JCTshift(t11,t12) ->
          hash t11 * hash t12
      | JCTunary(op1,t11) ->
          Hashtbl.hash op1 * hash t11
      | JCTold t11 ->
          hash t11
      | JCTaddress(absolute1,t11) ->
          Hashtbl.hash absolute1 * hash t11
      | JCTderef(t11,_,fi1) ->
          Hashtbl.hash fi1.fi_tag * hash t11
      | JCToffset(ok1,t11,st1) ->
          Hashtbl.hash ok1 * hash t11
          * Hashtbl.hash st1.si_name
      | JCTinstanceof (t11, _, _)
      | JCTdowncast (t11, _, _)
      | JCTsidecast (t11, _, _)
      | JCTbase_block(t11)
      | JCTreal_cast(t11,_)
      | JCTrange_cast(t11,_)
      | JCTrange_cast_mod (t11, _)
      | JCTat(t11,_) ->
          hash t11
      | JCTrange (t11opt, t12opt) ->
        let opt_hash = Option.map_default ~default:1 ~f:hash in
        opt_hash t11opt * opt_hash t12opt
      | JCTapp app1 ->
          let li1 = app1.app_fun and ts1 = app1.app_args in
          List.fold_left
            (fun h arg -> h * hash arg)
            (Hashtbl.hash li1.li_tag) ts1
      | JCTif(t11,t12,t13) ->
          hash t11 * hash t12 * hash t13
      | JCTmatch (_, _) -> assert false (* TODO *)
      | JCTlet(_,t1,t2) -> hash t1 * hash t2
    in
    Hashtbl.hash (term_num t) * h

end

module TermTable = Hashtbl.Make(TermOrd)
module TermSet = Set.Make(TermOrd)
module TermMap = Map.Make(TermOrd)


let tag_num tag = match tag#node with
  | JCTtag _ -> 1
  | JCTbottom -> 3
  | JCTtypeof _ -> 5

let raw_tag_compare tag1 tag2 =
  match tag1#node,tag2#node with
    | JCTtag st1,JCTtag st2 ->
        Pervasives.compare st1.si_name st2.si_name
    | JCTbottom,JCTbottom -> 0
    | JCTtypeof(t1,st1),JCTtypeof(t2,st2) ->
        let compst =
          Pervasives.compare st1.si_name st2.si_name
        in
        if compst = 0 then TermOrd.compare t1 t2 else compst
  | _ -> tag_num tag2 - tag_num tag1

(* Special comparison for enum_infos (contains Num i.e. an external data type!) *)

module Enum_info = struct
    let equal ?(by_name=true) ei1 ei2 =
      Pervasives.compare ei1.ei_type ei2.ei_type = 0 &&
      (by_name ||
        ei1.ei_min =/ ei2.ei_min &&
        ei1.ei_max =/ ei2.ei_max)
    let (=) = equal ~by_name:true
end

(* Comparison based only on assertion structure, not locations. *)
module AssertionOrd = struct
  type t = assertion

  let assertion_num a = match a#node with
        (* are these supposed to be prime numbers ? *)
    | JCAtrue -> 1
    | JCAfalse -> 3
    | JCArelation _ -> 5
    | JCAand _ -> 7
    | JCAor _ -> 11
    | JCAimplies _ -> 13
    | JCAiff _ -> 17
    | JCAnot _ -> 19
    | JCAapp _ -> 23
    | JCAquantifier _ -> 31
    | JCAold _ -> 37
    | JCAinstanceof  _ -> 41
    | JCAbool_term _ -> 43
    | JCAif _ -> 47
    | JCAmutable _ -> 53
    | JCAeqtype _ -> 59
    | JCAat _ -> 61
    | JCAlet _ -> 67
    | JCAmatch _ -> 71
    | JCAsubtype _ -> 73
    | JCAfresh _ -> 79
    | JCAfreeable _ -> 83
    | JCAallocable _ -> 89

  let rec compare a1 a2 =
    match a1#node, a2#node with
      | JCAtrue,JCAtrue | JCAfalse,JCAfalse -> 0
      | JCArelation(t11,op1,t12),JCArelation(t21,op2,t22) ->
          let compop = Pervasives.compare op1 op2 in
          if compop = 0 then
            let comp1 = TermOrd.compare t11 t21 in
            if comp1 = 0 then TermOrd.compare t12 t22 else comp1
          else compop
      | JCAand als1,JCAand als2 | JCAor als1,JCAor als2 ->
          list_compare compare als1 als2
      | JCAimplies(a11,a12),JCAimplies(a21,a22)
      | JCAiff(a11,a12),JCAiff(a21,a22) ->
          let comp1 = compare a11 a21 in
          if comp1 = 0 then compare a12 a22 else comp1
      | JCAnot a1,JCAnot a2 | JCAold a1,JCAold a2 ->
          compare a1 a2
      | JCAapp app1, JCAapp app2 ->
          let li1 = app1.app_fun in
          let li2 = app2.app_fun in
          let compli =
            Pervasives.compare li1.li_tag li2.li_tag
          in
          if compli = 0 then
            let tls1 = app1.app_args in
            let tls2 = app2.app_args in
              list_compare TermOrd.compare tls1 tls2
          else compli
      | JCAquantifier(q1,vi1,trigs1,a1),JCAquantifier(q2,vi2,trigs2,a2) ->
          let compq = Pervasives.compare q1 q2 in
          if compq = 0 then
            let compvi = Pervasives.compare vi1 vi2 in
            if compvi = 0 then
              let comptrigs = list_compare (list_compare compare_pat)
                trigs1 trigs2 in
              if comptrigs = 0 then compare a1 a2
              else comptrigs
            else compvi
          else compq
      | JCAinstanceof(t1,_,st1),JCAinstanceof(t2,_,st2) ->
          let compst =
            Pervasives.compare st1.si_name st2.si_name
          in
          if compst = 0 then TermOrd.compare t1 t2 else compst
      | JCAbool_term t1,JCAbool_term t2 ->
          TermOrd.compare t1 t2
      | JCAif(t1,a11,a12),JCAif(t2,a21,a22) ->
          let comp0 = TermOrd.compare t1 t2 in
          if comp0 = 0 then
            let comp1 = compare a11 a21 in
            if comp1 = 0 then compare a12 a22 else comp1
          else comp0
      | JCAmutable(t1,st1,tag1),JCAmutable(t2,st2,tag2) ->
          let compst =
            Pervasives.compare st1.si_name st2.si_name
          in
          if compst = 0 then
            let comptag = raw_tag_compare tag1 tag2 in
            if comptag = 0 then TermOrd.compare t1 t2 else comptag
          else compst
      | JCAeqtype(tag11,tag12,so1),JCAeqtype(tag21,tag22,so2) ->
          let compso = option_compare Pervasives.compare so1 so2 in
          if compso = 0 then
            let comptag = raw_tag_compare tag11 tag21 in
            if comptag = 0 then raw_tag_compare tag12 tag22 else comptag
          else compso
      | _ ->
          (* Assertions should have different constructors *)
          assert (assertion_num a1 <> assertion_num a2);
          assertion_num a1 - assertion_num a2
  and compare_pat pat1 pat2 =
    match pat1,pat2 with
      | JCAPatT t1,JCAPatT t2 -> TermOrd.compare t1 t2
      | JCAPatT _, _ -> 1
      | _,JCAPatT _ -> -1
      | JCAPatP p1, JCAPatP p2 -> compare p1 p2
  let equal a1 a2 = compare a1 a2 = 0
end

let rec is_numeric_term t =
  match t#node with
    | JCTconst _ -> true
    | JCTvar _ | JCTshift _ | JCTderef _
    | JCToffset _ | JCTaddress _ | JCTinstanceof _ | JCTrange _ -> false
    | JCTbinary (t1, _, t2) -> is_numeric_term t1 && is_numeric_term t2
    | JCTunary (_, t) | JCTold t | JCTat(t,_) | JCTdowncast (t, _, _) | JCTsidecast (t, _, _)
    | JCTbase_block t
    | JCTrange_cast (t, _) | JCTrange_cast_mod (t, _) | JCTreal_cast (t, _) -> is_numeric_term t
    | JCTapp _ -> false (* TODO ? *)
    | JCTif _ | JCTlet _ | JCTmatch _ -> false (* TODO ? *)


(* assertions *)

let rec is_constant_assertion a =
  match a#node with
    | JCAtrue | JCAfalse -> true
    | JCArelation (t1, _, t2) ->
        is_constant_term t1 && is_constant_term t2
    | JCAand al | JCAor al ->
        List.for_all is_constant_assertion al
    | JCAimplies (a1, a2) | JCAiff (a1, a2) ->
        is_constant_assertion a1 && is_constant_assertion a2
    | JCAnot a | JCAquantifier (_, _, _, a) | JCAold a | JCAat(a,_)
        -> is_constant_assertion a
    | JCAapp _ | JCAinstanceof _ | JCAmutable _ | JCAeqtype _
    | JCAsubtype _ | JCAfresh _ | JCAfreeable _ | JCAallocable _
        -> false
    | JCAbool_term t -> is_constant_term t
    | JCAif (t, a1, a2) ->
        is_constant_term t &&
          is_constant_assertion a1 &&
          is_constant_assertion a2
    | JCAlet(_vi,t, p) ->
        is_constant_term t && is_constant_assertion p
    | JCAmatch (t, pal) ->
        is_constant_term t &&
          (List.fold_left (fun acc (_, a) -> acc && is_constant_assertion a)
             true pal)

(* fun specs *)

let default_behavior = {
  b_throws = None;
  b_assumes = None;
  b_assigns = None;
  b_allocates = None;
  b_ensures = new assertion JCAtrue;
  b_free_ensures = new assertion JCAtrue;
}

let contains_normal_behavior fs =
  List.exists
    (fun (_, _, b) -> b.b_throws = None)
    (fs.fs_default_behavior :: fs.fs_behavior)

let contains_exceptional_behavior fs =
  List.exists
    (fun (_, _, b) -> b.b_throws <> None)
    (fs.fs_default_behavior :: fs.fs_behavior)

let is_purely_exceptional_fun fs =
  not (contains_normal_behavior fs) &&
    contains_exceptional_behavior fs


let rec skip_shifts e = match e#node with
  | JCEshift(e,_) -> skip_shifts e
  | _ -> e

let rec skip_term_shifts t = match t#node with
  | JCTshift(t,_) -> skip_term_shifts t
  | _ -> t

let rec skip_tloc_range locs = match locs#node with
  | JCLSrange(t,_,_) -> skip_tloc_range t
  | _ -> locs

(* option *)

let select_option opt default = match opt with Some v -> v | None -> default

(*
let direct_embedded_struct_fields st =
  List.fold_left
    (fun acc fi ->
      match fi.fi_type with
        | JCTpointer(JCtag st', Some _, Some _) ->
            assert (st.si_name <> st'.si_name);
            fi :: acc
        | JCTpointer(JCvariant st', Some _, Some _) ->
            assert false (* TODO *)
        | _ -> acc
    ) [] st.si_fields

let embedded_struct_fields st =
  let rec collect forbidden_set st =
    let forbidden_set = StringSet.add st.si_name forbidden_set in
    let fields = direct_embedded_struct_fields st in
    let fstructs =
      List.fold_left
        (fun acc fi -> match fi.fi_type with
          | JCTpointer (JCtag st', Some _, Some _) ->
              assert
                (not (StringSet.mem st'.si_name forbidden_set));
              st' :: acc
           | JCTpointer (JCvariant vi, Some _, Some _) ->
               assert false (* TODO *)
           | _ -> assert false (* bug ? pas acc plutot ? *)
               (* en plus c'est un pattern-matching fragile *)
        ) [] fields
    in
    fields @ List.flatten (List.map (collect forbidden_set) fstructs)
  in
  let fields = collect (StringSet.singleton st.si_name) st in
  let fields =
    List.fold_left (fun acc fi -> FieldSet.add fi acc) FieldSet.empty fields
  in
  FieldSet.elements fields
*)
let field_sinfo fi =
  match fi.fi_type with
    | JCTpointer(JCtag(st, _), _, _) -> st
    | _ -> assert false

let field_bounds fi =
  match fi.fi_type with
    | JCTpointer(_,Some a,Some b) -> a,b | _ -> assert false

let pointer_struct = function
  | JCTpointer(JCtag(st, []), _, _) -> st
  | ty ->
      Format.printf "%a@." print_type ty;
      assert false

let pointer_class = function
  | JCTpointer(pc, _, _) -> pc
  | ty ->
      Format.printf "%a@." print_type ty;
      assert false

let map_elements map =
  StringMap.fold (fun _ i acc -> i::acc) map []

(*
let embedded_struct_roots st =
  let fields = embedded_struct_fields st in
  let structs =
    List.fold_left (fun acc fi -> StructSet.add (field_sinfo fi) acc)
      StructSet.empty fields
  in
  let structs = StructSet.elements structs in
  let roots =
    List.fold_left
      (fun acc st -> StringSet.add (root_name st) acc)
      StringSet.empty structs
  in
  StringSet.elements roots
*)
let struct_root st =
  match st.si_hroot.si_root with
    | Some vi -> vi
    | None ->
        raise (Invalid_argument
                 ("struct_root in jc_pervasives.ml ("
                  ^st.si_name^", "
                  ^st.si_hroot.si_name^")"))
        (* don't use struct_root before checking that every tag is used
         * in a type *)

let pointer_class_root = function
  | JCtag(st, _) -> struct_root st
  | JCroot vi -> vi

let rec pattern_vars acc pat =
  match pat#node with
    | JCPstruct(_, fpl) ->
        List.fold_left
          (fun acc (_, pat) -> pattern_vars acc pat)
          acc fpl
    | JCPvar vi ->
        StringMap.add vi.vi_name vi acc
    | JCPor(pat, _) ->
        pattern_vars acc pat
    | JCPas(pat, vi) ->
        pattern_vars (StringMap.add vi.vi_name vi acc) pat
    | JCPany | JCPconst _ ->
        acc

let root_is_plain_union rt = rt.ri_kind = RplainUnion
let root_is_discr_union rt = rt.ri_kind = RdiscrUnion
let root_is_union rt = root_is_plain_union rt || root_is_discr_union rt

let struct_of_plain_union st =
  let vi = struct_root st in vi.ri_kind = RplainUnion

let struct_of_discr_union st =
  let vi = struct_root st in vi.ri_kind = RdiscrUnion

let struct_of_union st =
  let vi = struct_root st in root_is_union vi

let union_of_field fi =
  let st = fi.fi_struct in
  let vi = struct_root st in
  assert (root_is_union vi);
  vi

let integral_union vi =
  assert (root_is_union vi);
  List.fold_left (fun acc st -> acc &&
                    match st.si_fields with
                      | [fi] -> is_integral_type fi.fi_type
                      | _ -> false
                 ) true vi.ri_hroots

(* These are only used by error messages, so feel free to change the strings. *)
let string_of_op = function
  | `Blt -> "<"
  | `Bgt -> ">"
  | `Ble -> "<="
  | `Bge -> ">="
  | `Beq -> "=="
  | `Bneq -> "!="
  | `Badd -> "+"
  | `Badd_mod -> "+%"
  | `Bsub -> "-"
  | `Bsub_mod -> "-%"
  | `Bmul -> "*"
  | `Bmul_mod -> "*%"
  | `Bdiv -> "/"
  | `Bdiv_mod -> "/%"
  | `Bmod -> "%"
  | `Bmod_mod -> "%%"
  | `Bland -> "&&"
  | `Blor -> "||"
  | `Bimplies -> "==>"
  | `Biff -> "<=>"
  | `Bbw_and -> "&"
  | `Bbw_or -> "|"
  | `Bbw_xor -> "xor"
  | `Bshift_left -> "shift_left"
  | `Bshift_left_mod -> "shift_left_mod"
  | `Blogical_shift_right -> "logical_shift_right"
  | `Barith_shift_right -> "arith_shift_right"
  | `Uminus -> "unary -"
  | `Uminus_mod -> "unary -%"
  | `Unot -> "not"
  | `Ubw_not -> "bw not"
  | `Bconcat -> "strcat"

let string_of_op_type = function
  | `Integer -> "integer"
  | `Enum ei -> string_of_some_enum ei.ei_type
  | `Unit -> "unit"
  | `Real -> "real"
  | `Double -> "double"
  | `Float -> "single"
  | `Binary80 -> "binary80"
  | `Boolean -> "boolean"
  | `Pointer -> "pointer"
  | `Logic -> "<some logic type>"

let sign = JCTlogic ("sign",[])
let float_format = JCTlogic ("float_format",[])
let rounding_mode = JCTlogic ("rounding_mode",[])

(* Note: jessie does not support overloading. The right practice is
   to add suffixes to make precise the type of arguments

   TODO: rename integer_max to max_integer, real_abs to abs_real, etc.

*)

let builtin_enum_symbols =
  let (~+) = Num.num_of_string in
  [
    "int8",   { ei_min = ~+ "-128";                 ei_max = ~+ "127";                  ei_type = Int (Signed, X8) };
    "uint8",  { ei_min = ~+ "0";                    ei_max = ~+ "255";                  ei_type = Int (Unsigned, X8) };
    "int16",  { ei_min = ~+ "-32768";               ei_max = ~+ "32767";                ei_type = Int (Signed, X16) };
    "uint16", { ei_min = ~+ "0";                    ei_max = ~+ "65535";                ei_type = Int (Unsigned, X16) };
    "int32",  { ei_min = ~+ "-2147483648";          ei_max = ~+ "2147483647";           ei_type = Int (Signed, X32) };
    "uint32", { ei_min = ~+ "0";                    ei_max = ~+ "4294967295";           ei_type = Int (Unsigned, X32) };
    "int64",  { ei_min = ~+ "-9223372036854775808"; ei_max = ~+ "9223372036854775807";  ei_type = Int (Signed, X64) };
    "uint64", { ei_min = ~+ "0";                    ei_max = ~+ "18446744073709551615"; ei_type = Int (Unsigned, X64) };
  ]

let reinterpretation_predicates =
  let module M = struct type some_repr = Repr : _ repr -> some_repr type some_bit = Bit : _ bit -> some_bit end in
  let open M in
  let rec reinterpretation_predicates ?(acc=[]) =
    let predicates bitsizes =
      let size1, size2 =
        Pair.map
          (function
            | Bit X8 -> 1
            | Bit X16 -> 2
            | Bit X32 -> 4
            | Bit X64 -> 8)
          bitsizes
      in
      let rec predicates =
        fun ?(acc=[]) ->
          function
          | [] -> acc
          | reprs :: reprz ->
            let enum1, enum2 =
              Pair.map
                (fun (Repr r, Bit b) -> (Int (r, b) : some_enum))
                ((fst reprs, fst bitsizes), (snd reprs, snd bitsizes))
            in
            let name1, name2 = Pair.map string_of_some_enum (enum1, enum2) in
            let enum1, enum2 =
              (if size1 < size2 || size1 = size2 && reprs = (Repr Unsigned, Repr Signed)
               then enum1, enum2 else enum2, enum1) |>
              Pair.map ~f:(fun e -> List.assoc (string_of_some_enum e) builtin_enum_symbols)
            in
            predicates
              ~acc:((Some (JCTnative Tboolean),
                     "\\" ^ name1 ^ "_as_" ^ name2,
                     "bit_" ^ name1 ^ "_as_bit_" ^ name2,
                     JCTenum enum2 :: Array.(to_list @@ make (max size1 size2 / min size1 size2) @@ JCTenum enum1)) ::
                    acc)
              reprz
      in
      predicates
    in
    function
    | [] -> acc
    | bitsizes :: bitsizez ->
      reinterpretation_predicates
        ~acc:(acc @ predicates bitsizes @@ List.all_ordered_pairs [Repr Signed; Repr Unsigned])
        bitsizez
  in
  reinterpretation_predicates @@ List.all_ordered_pairs [Bit X8; Bit X16; Bit X32; Bit X64]

let builtin_logic_symbols =
  (* return type, jessie name, why name, parameter types *)
  [ Some real_type, "\\real_of_integer", "real_of_int", [integer_type] ;
    Some integer_type, "\\integer_max", "int_max", [integer_type; integer_type] ;
    Some integer_type, "\\integer_min", "int_min", [integer_type; integer_type] ;
    Some real_type, "\\real_max", "real_max", [real_type; real_type] ;
    Some real_type, "\\real_min", "real_min", [real_type; real_type] ;

    Some integer_type, "\\integer_abs", "abs_int", [integer_type] ;
    Some real_type, "\\real_abs", "abs_real", [real_type] ;
    Some integer_type, "\\truncate_real_to_int", "truncate_real_to_int", [real_type] ;

    Some integer_type, "\\int_pow", "pow_int", [integer_type; integer_type];

    Some real_type, "\\real_sqrt", "sqrt_real", [real_type];
    Some real_type, "\\real_pow", "pow_real", [real_type; real_type];
    Some real_type, "\\real_int_pow", "pow_real_int", [real_type; integer_type];

    Some real_type, "\\single_exact", "single_exact", [float_type];
    Some real_type, "\\double_exact", "double_exact", [double_type];
    Some real_type, "\\single_model", "single_model", [float_type];
    Some real_type, "\\double_model", "double_model", [double_type];



    Some real_type, "\\single_round_error", "single_round_error", [float_type];
    Some real_type, "\\double_round_error", "double_round_error", [double_type];
    Some real_type, "\\double_total_error", "double_total_error", [double_type];
    Some real_type, "\\single_total_error", "single_total_error", [float_type];
(*  Some real_type, "\\double_relative_error", "gen_relative_error", [double_type];
    Some real_type, "\\single_relative_error", "gen_relative_error", [float_type]; *)
    Some sign, "\\single_sign", "single_sign", [float_type];
    Some sign, "\\double_sign", "double_sign", [double_type];

    Some (JCTnative Tboolean), "\\single_is_finite", "single_is_finite", [float_type];
    Some (JCTnative Tboolean), "\\double_is_finite", "double_is_finite", [double_type];

    Some (JCTnative Tboolean), "\\single_is_infinite", "single_is_infinite", [float_type];
    Some (JCTnative Tboolean), "\\double_is_infinite", "double_is_infinite", [double_type];

    Some (JCTnative Tboolean), "\\single_is_NaN", "single_is_NaN", [float_type];
    Some (JCTnative Tboolean), "\\double_is_NaN", "double_is_NaN", [double_type];

    Some (JCTnative Tboolean), "\\single_is_minus_infinity", "single_is_minus_infinity", [float_type];
    Some (JCTnative Tboolean), "\\double_is_minus_infinity", "double_is_minus_infinity", [double_type];

    Some (JCTnative Tboolean), "\\single_is_plus_infinity", "single_is_plus_infinity", [float_type];
    Some (JCTnative Tboolean), "\\double_is_plus_infinity", "double_is_plus_infinity", [double_type];

    Some real_type, "\\exp", "exp", [real_type] ;
    Some real_type, "\\log", "log", [real_type] ;
    Some real_type, "\\log10", "log10", [real_type] ;

    Some real_type, "\\cos", "cos", [real_type] ;
    Some real_type, "\\sin", "sin", [real_type] ;
    Some real_type, "\\tan", "tan", [real_type] ;
    Some real_type, "\\pi", "pi", [] ;
    Some real_type, "\\cosh", "cosh", [real_type] ;
    Some real_type, "\\sinh", "sinh", [real_type] ;
    Some real_type, "\\tanh", "tanh", [real_type] ;
    Some real_type, "\\acos", "acos", [real_type] ;
    Some real_type, "\\asin", "asin", [real_type] ;
    Some real_type, "\\atan", "atan", [real_type] ;
    Some real_type, "\\atan2", "atan2", [real_type; real_type] ;
    Some real_type, "\\hypot", "hypot", [real_type; real_type] ;
    Some real_type, "\\round_float", "round_float", [float_format; rounding_mode; real_type];
    None, "\\no_overflow_single", "no_overflow_single", [rounding_mode; real_type];
    None, "\\no_overflow_double", "no_overflow_double", [rounding_mode; real_type];

    Some real_type, "\\round_single", "round_single", [rounding_mode; real_type];
    Some real_type, "\\round_double", "round_double", [rounding_mode; real_type];

    Some float_format, "\\Single", "Single", [];
    Some float_format, "\\Double", "Double", [];
    Some float_format, "\\Quad", "Quad", [];

    Some rounding_mode, "\\Down", "down", [];
    Some rounding_mode, "\\Up", "up", [];
    Some rounding_mode, "\\ToZero", "to_zero", [];
    Some rounding_mode, "\\NearestEven", "nearest_even", [];
    Some rounding_mode, "\\NearestAway", "nearest_away", [];

    Some sign, "\\Positive", "Positive", [];
    Some sign, "\\Negative", "Negative", [];

    Some (JCTnative Tboolean), "\\le_float", "le_single_full", [float_type;float_type];
    Some (JCTnative Tboolean), "\\le_double", "le_double_full", [double_type;double_type];

    Some (JCTnative Tboolean), "\\lt_float", "lt_single_full", [float_type;float_type];
    Some (JCTnative Tboolean), "\\lt_double", "lt_double_full", [double_type;double_type];

    Some (JCTnative Tboolean), "\\ge_float", "ge_single_full", [float_type;float_type];
    Some (JCTnative Tboolean), "\\ge_double", "ge_double_full", [double_type;double_type];

    Some (JCTnative Tboolean), "\\gt_float", "gt_single_full", [float_type;float_type];
    Some (JCTnative Tboolean), "\\gt_double", "gt_double_full", [double_type;double_type];

    Some (JCTnative Tboolean), "\\eq_float", "eq_single_full", [float_type;float_type];
    Some (JCTnative Tboolean), "\\eq_double", "eq_double_full", [double_type;double_type];

    Some (JCTnative Tboolean), "\\ne_float", "ne_single_full", [float_type;float_type];
    Some (JCTnative Tboolean), "\\ne_double", "ne_double_full", [double_type;double_type];
  ] @
  reinterpretation_predicates

let is_reinterpretation_predicate li =
  List.exists (fun (_, name, _, _) -> name = li.li_name) reinterpretation_predicates

let treatdouble = TreatGenFloat (`Double :> float_format)

let treatfloat = TreatGenFloat (`Float :> float_format)

let builtin_function_symbols =
  (* return type, jessie name, why name, parameter types, special treatment *)
  [
    real_type, "\\real_of_integer", "real_of_int", [integer_type], TreatNothing ;
    double_type, "\\double_sqrt", "sqrt_double", [double_type], treatdouble ;
    float_type, "\\float_sqrt", "sqrt_single", [float_type], treatfloat ;
    double_type, "\\double_abs", "abs_double", [double_type], treatdouble ;
    float_type, "\\float_abs", "abs_single", [float_type], treatfloat ;
    double_type, "\\neg_double", "neg_double", [double_type], treatdouble ;
    float_type, "\\neg_float", "neg_single", [float_type], treatfloat ;
  ]

module StringSet = Set.Make(String)

module IntSet = Set.Make(struct type t = int let compare = compare end)

module StringHashtblIter =
struct
  type 'a t = (string, 'a) Hashtbl.t * StringSet.t ref
  let create x = (Hashtbl.create x, ref StringSet.empty)
  let add (tbl, keys) x infos =
    Hashtbl.add tbl x infos;
    keys:=StringSet.add x !keys
  let replace (tbl, keys) x infos =
    Hashtbl.replace tbl x infos;
    keys:=StringSet.add x !keys
  let find (tbl,_) x = Hashtbl.find tbl x
  let fold f (tbl,keys) init =
    let apply s acc =
      try
        let infos = Hashtbl.find tbl s in f s infos acc
      with Not_found -> assert false
    in StringSet.fold apply !keys init
  let iter f t = fold (fun s i () -> f s i) t ()
end

module IntHashtblIter =
struct
  type 'a t = (int, 'a) Hashtbl.t * IntSet.t ref
  let create x = (Hashtbl.create x, ref IntSet.empty)
  let add (tbl, keys) x infos =
    Hashtbl.add tbl x infos;
    keys:=IntSet.add x !keys
  let replace (tbl, keys) x infos =
    Hashtbl.replace tbl x infos;
    keys:=IntSet.add x !keys
  let find (tbl,_) x = Hashtbl.find tbl x
  let mem (tbl, _) x = Hashtbl.mem tbl x
  let fold f (tbl,keys) init =
    let apply s acc =
      try
        let infos = Hashtbl.find tbl s in f s infos acc
      with Not_found -> assert false
    in IntSet.fold apply !keys init
  let iter f t = fold (fun n i () -> f n i) t ()
end


(*
Local Variables:
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End:
*)

