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


open Jc_env
open Jc_envset
open Jc_region
open Jc_ast
open Jc_fenv

open Jc_name
open Jc_constructors
open Jc_pervasives
open Jc_separation
open Jc_struct_tools
open Jc_effect
open Jc_interp_misc
open Jc_invariants
open Jc_pattern

open Output
open Format
open Num
open Pp

let unsupported = Jc_typing.typing_error

(******************************************************************************)
(*                            source positioning                              *)
(******************************************************************************)

let abs_fname f =
  if Filename.is_relative f then
    Filename.concat (Unix.getcwd ()) f
  else f

type source_ref = {
  in_mark: string;
  pos: Loc.position
}

type gui_elem = {
  out_mark: string;
  kind: kind option;
  name: string option;
  beh: string option
}

let reg_pos sce gui =
  if gui.out_mark <> "" && false (* Jc_stdlib.StdHashtbl.mem Output.my_pos_table gui.out_mark *) then begin
    (* If GUI element already refered to in output table, do not
     * reference it twice. This is the case in particular for generated
     * annotations. *)
    gui.out_mark
  end else
    (* Generate a new mark if not fixed in GUI element *)
    let mark =
      if gui.out_mark = ""
      then new_label_name ()
      else gui.out_mark
    in
    let n, f, l, b, e, k =
      if sce.in_mark <> "" && Jc_stdlib.Hashtbl.mem Jc_options.pos_table sce.in_mark then
	(* If source location present in input table, copy information to
	 * output table. *)
	let f, l, b, e, k, o = Jc_stdlib.Hashtbl.find Jc_options.pos_table sce.in_mark in
	let n =
	  try match List.assoc "name" o with
            | Rc.RCident s | Rc.RCstring s -> Some s
            | _ -> raise Not_found
	  with Not_found -> gui.name
	in
	n, f, l, b, e, k
      else
        begin
	  (* By default, refer to the Jessie source file *)
	  let b,e = sce.pos in
	  let f = abs_fname b.Lexing.pos_fname in
	  let l = b.Lexing.pos_lnum in
	  let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
	  let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
	  (gui.name, f, l, fc, lc, None)
        end
    in
    (* If present, always prefer new kind *)
    let k = match gui.kind with None -> k | Some k -> Some k in
    my_add_pos mark (k, n, gui.beh, f, l, b, e);
    mark

let reg_check ?mark ?kind pos =
  let sce = { in_mark = Option_misc.map_default id "" mark; pos = pos; } in
  let gui = { out_mark = ""; kind = kind; name = None; beh = None; } in
  reg_pos sce gui

let reg_decl ~in_mark ~out_mark ~name ~beh pos =
  let sce = { in_mark = in_mark; pos = pos; } in
  let gui = { out_mark = out_mark; kind = None; name = Some name; beh = Some beh; } in
  ignore (reg_pos sce gui)

let make_check ?mark ?kind pos e' =
  let mark = reg_check ?mark ?kind pos in
  make_label mark e'

let make_guarded_app ~mark kind pos f args =
  make_check ~mark ~kind pos (make_app f args)

(******************************************************************************)
(*                                 Operators                                  *)
(******************************************************************************)

let native_operator_type op =
  match snd op with
  | `Unit -> Jc_pervasives.unit_type
  | `Boolean -> Jc_pervasives.boolean_type
  | `Integer -> Jc_pervasives.integer_type
  | `Real -> Jc_pervasives.real_type
  | `Double -> Jc_pervasives.double_type
  | `Float -> Jc_pervasives.float_type
  | `Binary80 -> JCTnative (Tgenfloat `Binary80)

let unary_op: expr_unary_op -> string =
  function
  | `Uminus, `Integer -> "neg_int"
  | `Uminus, `Real -> "neg_real"
  | `Unot, `Boolean -> "not"
  | `Ubw_not, `Integer -> "bw_compl"
  | _ -> invalid_arg "unary_op: not a proper type"

let term_unary_op: expr_unary_op -> string =
  function
  | `Uminus, `Integer -> "neg_int"
  | `Uminus, `Real -> "neg_real"
  | `Unot, `Boolean -> "bool_not"
  | `Ubw_not, `Integer -> "bw_compl"
  | _ -> invalid_arg "term_unary_op: not a proper type"

let float_model_has_safe_functions () =
  match !Jc_options.float_model with
  | FMdefensive | FMmultirounding -> true
  | FMmath | FMfull -> false


let float_format f =
  match f with
  | `Double -> "double"
  | `Float -> "single"
  | `Binary80 -> "binary80"

let float_operator f t =
  let s =
    match f with
    | `Badd -> "add_"
    | `Bsub -> "sub_"
    | `Bmul -> "mul_"
    | `Bdiv -> "div_"
    | `Uminus -> "neg_"
    | `Bmod -> invalid_arg "float_operator: modulo operation"
  in
  if float_model_has_safe_functions () && not @@ safety_checking ()
  then s ^ float_format t ^ "_safe" else s ^ float_format t



let logic_current_rounding_mode () =
  match !Jc_options.current_rounding_mode with
  | FRMNearestEven -> LVar "nearest_even"
  | FRMDown -> LVar "down"
  | FRMUp -> LVar "up"
  | FRMToZero -> LVar "to_zero"
  | FRMNearestAway -> LVar "nearest_away"

let current_rounding_mode () =
  match !Jc_options.current_rounding_mode with
  | FRMNearestEven -> mk_var "nearest_even"
  | FRMDown -> mk_var "down"
  | FRMUp -> mk_var "up"
  | FRMToZero -> mk_var "to_zero"
  | FRMNearestAway -> mk_var "nearest_away"

let bin_op: expr_bin_op -> string =
  function
    (* integer *)
  | `Bgt, `Integer -> "gt_int_"
  | `Blt, `Integer -> "lt_int_"
  | `Bge, `Integer -> "ge_int_"
  | `Ble, `Integer -> "le_int_"
  | `Beq, `Integer -> "eq_int_"
  | `Bneq, `Integer -> "neq_int_"
  | `Badd, `Integer -> "add_int"
  | `Bsub, `Integer -> "sub_int"
  | `Bmul, `Integer -> "mul_int"
  | `Bdiv, `Integer
    when safety_checking () -> "computer_div_"
  | `Bdiv, `Integer         -> "computer_div"
  | `Bmod, `Integer
    when safety_checking () -> "computer_mod_"
  | `Bmod, `Integer         -> "computer_mod"
      (* pointer *)
  | `Beq, `Pointer
    when safety_checking () -> "eq_pointer"
  | `Beq, `Pointer          -> "safe_eq_pointer"
  | `Bneq, `Pointer
    when safety_checking () -> "neq_pointer"
  | `Bneq, `Pointer         -> "safe_neq_pointer"
  | `Bsub, `Pointer
    when safety_checking () -> "sub_pointer_"
  | `Bsub, `Pointer         -> "safe_sub_pointer_"
      (* real *)
  | `Bgt, `Real -> "gt_real_"
  | `Blt, `Real -> "lt_real_"
  | `Bge, `Real -> "ge_real_"
  | `Ble, `Real -> "le_real_"
  | `Beq, `Real -> "eq_real_"
  | `Bneq, `Real -> "neq_real_"
  | `Bgt, `Float -> "gt_single_"
  | `Blt, `Float -> "lt_single_"
  | `Bge, `Float -> "ge_single_"
  | `Ble, `Float -> "le_single_"
  | `Beq, `Float -> "eq_single_"
  | `Bneq,`Float -> "ne_single_"
  | `Bgt, `Double -> "gt_double_"
  | `Blt, `Double -> "lt_double_"
  | `Bge, `Double -> "ge_double_"
  | `Ble, `Double -> "le_double_"
  | `Beq, `Double -> "eq_double_"
  | `Bneq, `Double -> "ne_double_"
  | `Badd, `Real -> "add_real"
  | `Bsub, `Real -> "sub_real"
  | `Bmul, `Real -> "mul_real"
  | `Bdiv, `Real
    when safety_checking () -> "div_real_"
  | `Bdiv, `Real            -> "div_real"
      (* bool *)
  | `Beq, `Boolean -> "eq_bool_"
  | `Bneq, `Boolean -> "neq_bool_"
      (* bitwise *)
  | `Bbw_and, `Integer -> "bw_and"
  | `Bbw_or, `Integer -> "bw_or"
  | `Bbw_xor, `Integer -> "bw_xor"
  | `Bbw_and, `Boolean -> "bool_and"
  | `Bbw_or, `Boolean -> "bool_or"
  | `Bbw_xor, `Boolean -> "bool_xor"
      (* shift *)
  | `Bshift_left, `Integer -> "lsl"
  | `Blogical_shift_right, `Integer -> "lsr"
  | `Barith_shift_right, `Integer -> "asr"
  | `Bland, _ -> invalid_arg "bin_op: unnormalized `Bland"
  | `Blor, _ -> invalid_arg "bin_op: unnormalized `Blor"
  | `Bconcat, _ -> "string_concat"
  | op, opty ->
    unsupported
      Loc.dummy_position
      "Can't use operator %s with type %s in expressions"
      (string_of_op op) (string_of_op_type opty)

let term_bin_op: term_bin_op -> string =
  function
    (* integer *)
  | `Bgt, `Integer -> "gt_int_bool"
  | `Blt, `Integer -> "lt_int_bool"
  | `Bge, `Integer -> "ge_int_bool"
  | `Ble, `Integer -> "le_int_bool"
  | `Beq, `Integer -> "eq_int_bool"
  | `Bneq, `Integer -> "neq_int_bool"
  | `Badd, `Integer -> "add_int"
  | `Bsub, `Integer -> "sub_int"
  | `Bmul, `Integer -> "mul_int"
  | `Bdiv, `Integer -> "computer_div"
  | `Bmod, `Integer -> "computer_mod"
      (* pointer *)
  | `Beq, `Pointer -> "eq_pointer_bool"
  | `Bneq, `Pointer -> "neq_pointer_bool"
  | `Bsub, `Pointer -> "sub_pointer"
      (* logic *)
  | `Beq, `Logic -> "eq"
  | `Bneq, `Logic -> "neq"
      (* real *)
  | `Bgt, `Real -> "gt_real_bool"
  | `Blt, `Real -> "lt_real_bool"
  | `Bge, `Real -> "ge_real_bool"
  | `Ble, `Real -> "le_real_bool"
  | `Beq, `Real -> "eq_real_bool"
  | `Bneq, `Real -> "neq_real_bool"
  | `Badd, `Real -> "add_real"
  | `Bsub, `Real -> "sub_real"
  | `Bmul, `Real -> "mul_real"
  | `Bdiv, `Real -> "div_real"
      (* bool *)
(*
  | `Beq_bool, `Boolean -> "eq_bool"
  | `Bneq_bool, `Boolean -> "neq_bool"
*)
      (* bitwise *)
  | `Bbw_and, `Integer -> "bw_and"
  | `Bbw_or, `Integer -> "bw_or"
  | `Bbw_xor, `Integer -> "bw_xor"
  | `Bshift_left, `Integer -> "lsl"
  | `Blogical_shift_right, `Integer -> "lsr"
  | `Barith_shift_right, `Integer -> "asr"
      (* logical *)
  | `Blor, `Boolean -> "bool_or"
  | `Bland, `Boolean ->  "bool_and"
  | `Biff, _ | `Bimplies, _ -> invalid_arg "term_bin_op: unimplemented: `Biff, `Bimplies" (* TODO *)
  | op, opty ->
    unsupported
      Loc.dummy_position
      "Can't use operator %s with type %s in terms"
      (string_of_op op) (string_of_op_type opty)

let pred_bin_op: pred_bin_op -> string =
  function
    (* integer *)
  | `Bgt, `Integer -> "gt_int"
  | `Blt, `Integer -> "lt_int"
  | `Bge, `Integer -> "ge_int"
  | `Ble, `Integer -> "le_int"
  | `Beq, `Integer -> "eq"
  | `Bneq, `Integer -> "neq"
      (* pointer *)
  | `Beq, (`Pointer | `Logic) -> "eq"
  | `Bneq, (`Pointer | `Logic) -> "neq"
      (* real *)
  | `Beq, `Real -> "eq"
  | `Bneq, `Real -> "neq"
  | `Bgt, `Real -> "gt_real"
  | `Blt, `Real -> "lt_real"
  | `Bge, `Real -> "ge_real"
  | `Ble, `Real -> "le_real"
      (* logical *)
  | `Blor, `Boolean -> "bor"
  | `Bland, `Boolean -> "band"
  | `Biff, `Boolean
  | `Bimplies, `Boolean -> invalid_arg "pred_bin_op: unimplemented: `Biff, `Bimplies" (* TODO *)
      (* boolean *)
  | `Beq, `Boolean -> "eq"
  | `Bneq, `Boolean -> "neq"
  | op, opty ->
    unsupported
      Loc.dummy_position
      "Can't use operator %s with type %s in assertions"
      (string_of_op op)
      (string_of_op_type opty)


(******************************************************************************)
(*                                   types                                    *)
(******************************************************************************)

let has_equality_op =
  function
  | JCTnative Tunit -> false
  | JCTnative Tboolean -> true
  | JCTnative Tinteger -> true
  | JCTnative Treal -> true
  | JCTnative (Tgenfloat _) -> true
  | JCTnative Tstring -> true
  | JCTlogic _s -> (* TODO *) false
  | JCTenum _ei -> true
  | JCTpointer _
  | JCTnull ->  true
  | JCTany -> false
  | JCTtype_var _ -> false (* TODO ? *)

let equality_op_for_type =
  function
  | JCTnative Tunit -> invalid_arg "equality_op_for_type: equality op for unit type requested"
  | JCTnative Tboolean -> "eq_bool"
  | JCTnative Tinteger -> "eq_int"
  | JCTnative Treal -> "eq_real"
  | JCTnative (Tgenfloat f) -> "eq_" ^ float_format f
  | JCTnative Tstring -> "eq"
  | JCTlogic _s -> invalid_arg "equality_op_for_type: unimplemented: equality for logic types" (* TODO *)
  | JCTenum ei -> eq_of_enum ei
  | JCTpointer _
  | JCTnull ->  "eq"
  | JCTany -> invalid_arg "equality_op_for_type: equality op for `any' type requested"
  | JCTtype_var _ -> invalid_arg "equality_op_for_type: unimplemented: equality for type variables" (* TODO ? *)


(******************************************************************************)
(*                                 Structures                                 *)
(******************************************************************************)

let tr_struct st acc =
  let tagid_type = tag_id_type (struct_root st) in
  (* Declarations of field memories. *)
  let acc =
    if !Jc_options.separation_sem = SepRegions ||
       struct_of_plain_union st
    then acc
    else
      List.fold_left
        (fun acc fi ->
          let mem = memory_type (JCmem_field fi) in
            Param (false,
                   id_no_loc (field_memory_name fi),
                   Ref_type (Base_type mem))
            :: acc)
        acc st.si_fields
  in
  (* declaration of the tag_id *)
  let acc = Logic (false, id_no_loc (tag_name st), [], tagid_type) :: acc in
  let acc =
    if struct_of_union st then acc
    else
      let pc = JCtag(st, []) in
      let ac = alloc_class_of_pointer_class pc in
      let in_param = false in
        (* Validity parameters *)
        [ make_valid_pred ~in_param ~equal:true ac pc;
          make_valid_pred ~in_param ~equal:false ac pc;
          make_valid_pred ~in_param ~equal:false ~right:false ac pc;
          make_valid_pred ~in_param ~equal:false ~left:false ac pc;

          make_fresh_pred ac pc;
          make_instanceof_pred ~arg:Range_l_r ac pc;
          make_instanceof_pred ~arg:Singleton ac pc;
          make_alloc_pred ac pc;

          (* Allocation parameters *)
          make_alloc_param ~arg:Singleton ac pc;
          make_alloc_param ~arg:Range_0_n ~check_size:true ac pc;
          make_alloc_param ~arg:Range_0_n ~check_size:false ac pc] @
        (if Region.exists_bitwise () then make_conversion_params pc else []) @
        acc
  in

  match st.si_parent with
  | None ->
    (* axiom for parenttag *)
    let name = st.si_name ^ "_parenttag_bottom" in
    let p = LPred("parenttag", [ LVar (tag_name st); LVar "bottom_tag" ]) in
    Goal (KAxiom, id_no_loc name, p) :: acc
  | Some (p, _) ->
    (* axiom for parenttag *)
    let name = st.si_name ^ "_parenttag_" ^ p.si_name in
    let p = LPred ("parenttag", [LVar (tag_name st); LVar (tag_name p)]) in
    Goal (KAxiom, id_no_loc name, p) :: acc


(******************************************************************************)
(*                                 Coercions                                  *)
(******************************************************************************)

let float_of_real f x =
  (* TODO: Mpfr.settofr etc *)
  if Str.string_match (Str.regexp "\\([0-9]+\\)\\.0*$") x 0 then
    let s = Str.matched_group 1 x in
    match f with
    | `Float ->
      if String.length s <= 7 (* x < 10^7 < 2^24 *) then x
      else raise Not_found
    | `Double ->
       if String.length s <= 15 (* x < 10^15 < 2^53 *) then x
       else raise Not_found
    | `Binary80 -> raise Not_found
  else
    match f, x with
    | _ , "0.5" -> x
    | `Float, "0.1" -> "0x1.99999ap-4"
    | `Double, "0.1" -> "0x1.999999999999ap-4"
    | _ -> raise Not_found

let rec term_coerce ~type_safe ~global_assertion lab ?(cast=false) pos  ty_dst ty_src e e' =
  let rec aux a b =
    match a, b with
    | JCTlogic (t, tl), JCTlogic (u, ul) when t = u -> List.for_all2 aux tl ul
    | JCTtype_var _, JCTtype_var _ -> true (*jc_typing take care of that*)
    | (JCTtype_var _, _) | (_, JCTtype_var _) -> true
    | JCTpointer (JCroot rt1, _, _), JCTpointer (JCroot rt2, _, _) -> rt1 == rt2
    | _ -> false
  in
  match ty_dst, ty_src with
  (* identity *)
  | JCTnative t, JCTnative u when t = u -> e'
  | (JCTlogic _ | JCTtype_var _), (JCTlogic _ | JCTtype_var _) when aux ty_dst ty_src -> e'
  | (JCTtype_var _, JCTpointer _) -> e'
  | JCTpointer _, JCTpointer _ when aux ty_dst ty_src -> e'
  | JCTany, JCTany -> e'
    (* between integer/enum and real *)
  | JCTnative Treal, JCTnative Tinteger ->
    begin match e' with
    | LConst(Prim_int n) ->
      LConst(Prim_real(n ^ ".0"))
    | _ ->
      LApp("real_of_int",[ e' ])
    end
  | JCTnative Treal, JCTenum ri ->
    begin match e' with
    | LConst(Prim_int n) ->
      LConst(Prim_real(n ^ ".0"))
    | _ ->
      let e' = LApp(logic_int_of_enum ri,[ e' ]) in
      LApp("real_of_int",[ e' ])
    end
  | JCTnative Treal, JCTnative (Tgenfloat f) ->
    begin match e' with
    | LApp (f,[LConst (Prim_real _) as c])
      when f = "single_of_real_exact" || f = "single_of_real_exact" -> c
    | _ -> LApp((float_format f)^"_value",[ e' ])
    end
  | JCTnative (Tgenfloat f), JCTnative Treal ->
    begin try
      match e' with
      | LConst (Prim_real x) ->
	LApp (float_format f ^ "_of_real_exact",
              [LConst (Prim_real (float_of_real f x))])
      | _ -> raise Not_found
    with
    | Not_found ->
      LApp ("round_" ^ float_format f ^ "_logic",
	    [logic_current_rounding_mode () ; e' ])
    end
  | JCTnative (Tgenfloat _f), (JCTnative Tinteger | JCTenum _) ->
    term_coerce ~type_safe ~global_assertion lab pos ty_dst (JCTnative Treal) e
      (term_coerce ~type_safe ~global_assertion lab pos (JCTnative Treal) ty_src e e')
  | JCTnative Tinteger, JCTnative Treal ->
    (* LApp("int_of_real",[ e' ]) *)
    unsupported pos "unsupported convertion from integer to real in logic"
    (* between enums and integer *)
  | JCTenum ri1, JCTenum ri2
    when ri1.ei_name = ri2.ei_name -> e'
  | JCTenum ri1, JCTenum ri2 ->
     assert cast; (* Typing should have inserted an explicit cast *)
     let e' = LApp(logic_int_of_enum ri2,[ e' ]) in
     LApp(logic_enum_of_int ri1,[ e' ])
  | JCTnative Tinteger, JCTenum ri ->
    LApp(logic_int_of_enum ri,[ e' ])
  | JCTenum ri, JCTnative Tinteger ->
    LApp(logic_enum_of_int ri,[ e' ])
      (* between pointers and null *)
  | JCTpointer _ , JCTnull -> e'
  | JCTpointer(pc1, _, _), JCTpointer (JCtag (st2, _), _, _)
    when Jc_typing.substruct st2 pc1 -> e'
  | JCTpointer (JCtag (st1, _), _, _), JCTpointer _ ->
    LApp ("downcast", [e'; LVar (tag_name st1)])
  |  _ ->
     unsupported
       pos
       "can't (term_)coerce type %a to type %a"
       print_type ty_src print_type ty_dst

let eval_integral_const e =
  let rec eval e =
    match e#node with
    | JCEconst(JCCinteger s) -> Numconst.integer s
    | JCErange_cast(e,_ri2) -> eval e
    | JCEunary(op,e) ->
      let v = eval e in
      begin match op with
      | `Uminus, `Integer -> minus_num v
      | `Uminus, (`Real | `Binary80 | `Double | `Float | `Boolean | `Unit)
      | `Unot, _
      | `Ubw_not, _ -> raise Exit
      end
    | JCEbinary(e1,op,e2) ->
      let v1 = eval e1 in
      let v2 = eval e2 in
      begin match op with
      | `Badd, `Integer -> v1 +/ v2
      | `Bsub, `Integer -> v1 -/ v2
      | `Bmul, `Integer -> v1 */ v2
      | `Bdiv, `Integer ->
        if eq_num (mod_num v1 v2) Numconst.zero then quo_num v1 v2 else raise Exit
      | `Bmod, `Integer -> mod_num v1 v2
      | (`Badd | `Barith_shift_right | `Bbw_and | `Bbw_or | `Bbw_xor
        | `Bdiv | `Beq | `Bge | `Bgt | `Ble | `Blogical_shift_right
        | `Blt | `Bmod | `Bmul | `Bneq | `Bshift_left | `Bsub), _ -> raise Exit
      | `Bconcat, _ -> raise Exit
      | `Bland, _ -> raise Exit
      | `Blor, _ -> raise Exit
      end
    | JCEif(_e1,_e2,_e3) ->
      (* TODO: write [eval_boolean_const] *)
      raise Exit
    | JCEconst _ | JCEvar _ | JCEshift _ | JCEderef _
    | JCEinstanceof _ | JCEcast _ | JCEbitwise_cast _ | JCEreal_cast _
    | JCEoffset _ | JCEbase_block _
    | JCEaddress _
    | JCEalloc _ | JCEfree _ | JCEreinterpret _ | JCEmatch _ |JCEunpack _ |JCEpack _
    | JCEthrow _ | JCEtry _ | JCEreturn _ | JCEloop _ | JCEblock _
    | JCEcontract _ | JCEassert _ | JCEfresh _
    | JCElet _ | JCEassign_heap _ | JCEassign_var _ | JCEapp _
    | JCEreturn_void -> raise Exit
  in
  try Some (eval e) with Exit | Division_by_zero -> None

let fits_in_enum ri e =
  match eval_integral_const e with
  | Some c -> ri.ei_min <=/ c && c <=/ ri.ei_max
  | None -> false

let rec coerce ~check_int_overflow mark pos ty_dst ty_src e e' =
  match ty_dst, ty_src with
    (* identity *)
  | JCTnative t, JCTnative u when t = u -> e'
  | JCTlogic t, JCTlogic u when t = u -> e'
  | JCTany, JCTany -> e'
    (* between integer/enum and real *)
  | JCTnative Treal, JCTnative Tinteger ->
    begin match e'.expr_node with
    | Cte(Prim_int n) ->
      { e' with expr_node = Cte (Prim_real (n ^ ".0")) }
    | _ -> make_app "real_of_int" [e']
    end
  | JCTnative Treal, JCTenum ri ->
    begin match e'.expr_node with
    | Cte(Prim_int n) ->
      { e' with expr_node = Cte (Prim_real (n ^ ".0")) }
    | _ -> make_app "real_of_int" [make_app (logic_int_of_enum ri) [e']]
    end
  | JCTnative Tinteger, JCTnative Treal ->
    (* make_app "int_of_real" [ e' ] *)
    unsupported pos "coerce: unsupported cast from integer to real"
  | JCTnative (Tgenfloat _), (JCTnative Tinteger | JCTenum _) ->
    coerce ~check_int_overflow mark pos ty_dst (JCTnative Treal) e
      (coerce ~check_int_overflow mark pos (JCTnative Treal) ty_src e e')
  | JCTnative (Tgenfloat f1), JCTnative (Tgenfloat f2) ->
    let enlarge =
      match f2, f1 with
      | `Float, _ -> true
      | _, `Float -> false
      | `Double, _ -> true
      | _, _ -> false in
    let name = float_format f1 ^ "_of_" ^ float_format f2 in
    if enlarge then
      make_app name [e']
    else if check_int_overflow then
      make_guarded_app ~mark FPoverflow pos name [current_rounding_mode (); e']
    else
      make_app (name ^ "_safe") [current_rounding_mode (); e']
  | JCTnative (Tgenfloat f), JCTnative Treal ->
    begin try
      match e'.expr_node with
      | Cte (Prim_real x) ->
        let s = float_of_real f x in
	make_app (float_format f  ^ "_of_real_exact")  [{ e' with expr_node = Cte (Prim_real s) }]
      | _ -> raise Not_found
      with
      | Not_found ->
	if check_int_overflow then
          make_guarded_app ~mark FPoverflow pos  (float_format f ^ "_of_real") [current_rounding_mode (); e']
        else
          make_app (float_format f ^ "_of_real_safe") [current_rounding_mode (); e']
    end
  | JCTnative Treal, JCTnative (Tgenfloat f) -> make_app (float_format f ^ "_value") [e']
    (* between enums and integer *)
  | JCTenum ri1, JCTenum ri2
    when ri1.ei_name = ri2.ei_name -> e'
  | JCTenum ri1, JCTenum ri2 ->
    let e' = make_app (logic_int_of_enum ri2) [e'] in
    if not check_int_overflow || fits_in_enum ri1 e then
      make_app (safe_fun_enum_of_int ri1) [e']
    else
      make_guarded_app ~mark ArithOverflow pos (fun_enum_of_int ri1) [e']
  | JCTnative Tinteger, JCTenum ri ->
    make_app (logic_int_of_enum ri) [ e' ]
  | JCTenum ri, JCTnative Tinteger ->
    if not check_int_overflow || fits_in_enum ri e then
      make_app (safe_fun_enum_of_int ri) [e']
    else
      make_guarded_app ~mark ArithOverflow pos (fun_enum_of_int ri) [ e' ]
    (* between pointers and null *)
  | JCTpointer _ , JCTnull -> e'
  | JCTpointer(pc1, _, _), JCTpointer(JCtag(st2, _), _, _)
    when Jc_typing.substruct st2 pc1 -> e'
  | JCTpointer (JCtag (st1, _), _, _), JCTpointer _  ->
    let downcast_fun =
      if safety_checking () then "downcast_" else "safe_downcast_"
    in
    make_app downcast_fun [e'; mk_var (tag_name st1)]
  | _ ->
    unsupported
      pos
      "can't coerce type %a to type %a"
      print_type ty_src print_type ty_dst


(******************************************************************************)
(*                                   terms                                    *)
(******************************************************************************)

(* [pattern_lets] is a list of (id, value), which should be binded
 * at the assertion level. *)
let pattern_lets = ref []
let concat_pattern_lets lets = pattern_lets := lets @ !pattern_lets
let bind_pattern_lets body =
  let binds =
    List.fold_left
      (fun body bind ->
	 match bind with
	   | JCforall(id, ty) -> LForall(id, ty, [], body)
	   | JClet(id, value) -> LLet(id, value, body))
      body (List.rev !pattern_lets)
  in
  pattern_lets := [];
  binds

let is_base_block t = match t#node with
  | JCTbase_block _ -> true
  | _ -> false

let rec term ?(subst=VarMap.empty) ~type_safe ~global_assertion ~relocate lab oldlab t =
  let ft = term ~subst ~type_safe ~global_assertion ~relocate lab oldlab in
  let term_coerce = term_coerce ~type_safe ~global_assertion lab in
  let t' = match t#node with
    | JCTconst JCCnull -> LVar "null"
    | JCTvar v ->
        begin
          try VarMap.find v subst
          with Not_found -> tvar ~label_in_name:global_assertion lab v
        end
    | JCTconst c -> LConst(const c)
    | JCTunary(op,t1) ->
        let t1'= ft t1 in
        LApp(term_unary_op op,
	     [ term_coerce t#pos (native_operator_type op) t1#typ t1 t1' ])
    | JCTbinary(t1,(_,(`Pointer | `Logic) as op),t2) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        LApp(term_bin_op op, [ t1'; t2' ])
    | JCTbinary(t1,(_, #native_operator_type as op),t2) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        let ty = native_operator_type op in
        LApp(term_bin_op op,
             [ term_coerce t1#pos ty t1#typ t1 t1';
               term_coerce t2#pos ty t2#typ t2 t2' ])
    | JCTshift(t1,t2) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        LApp("shift",[ t1'; term_coerce t2#pos integer_type t2#typ t2 t2' ])
    | JCTif(t1,t2,t3) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        let t3' = ft t3 in
        TIf(t1',
            (** type of t2 and t3 are equal or one is the subtype of
                the other *)
            term_coerce t2#pos t#typ t2#typ t2 t2',
            term_coerce t3#pos t#typ t3#typ t3 t3')
    | JCTlet(vi,t1,t2) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        TLet(vi.vi_final_name, t1', t2')
    | JCToffset(k,t1,st) ->
	let ac = tderef_alloc_class ~type_safe t1 in
        let _,alloc =
	  talloc_table_var ~label_in_name:global_assertion lab (ac,t1#region)
	in
	begin match ac with
	  | JCalloc_root _ ->
              let f = match k with
		| Offset_min -> "offset_min"
		| Offset_max -> "offset_max"
              in
              let t1' = ft t1 in
              LApp(f,[alloc; t1' ])
	  | JCalloc_bitvector ->
              let f = match k with
		| Offset_min -> "offset_min_bytes"
		| Offset_max -> "offset_max_bytes"
              in
              let t1' = ft t1 in
	      let s = string_of_int (struct_size_in_bytes st) in
              LApp(f,[ alloc; t1'; LConst(Prim_int s) ])
	end
    | JCTaddress(Addr_absolute,t1) ->
        LApp("absolute_address",[ ft t1 ])
    | JCTaddress(Addr_pointer,t1) ->
        LApp("address",[ ft t1 ])
    | JCTbase_block(t1) ->
        LApp("base_block",[ ft t1 ])
    | JCTinstanceof (t1, _, st) ->
      let t1' = ft t1 in
      LApp ("instanceof", [t1'; LVar (tag_name st)])
    | JCTcast (t1, _, st) ->
      if struct_of_union st
      then ft t1
      else LApp ("downcast", [ft t1; LVar (tag_name st)])
    | JCTbitwise_cast(t1,_lab,_st) ->
	ft t1
    | JCTrange_cast(t1, ri) ->
        let t1' = ft t1 in
        let to_type = Option_misc.map_default (fun e -> JCTenum e) (JCTnative Tinteger) ri in
        term_coerce ~cast:true t1#pos to_type t1#typ t1 t1'
    | JCTreal_cast(t1,rc) ->
        let t1' = ft t1 in
        begin match rc with
          | Integer_to_real ->
              term_coerce t1#pos real_type t1#typ t1 t1'
          | Double_to_real ->
              term_coerce t1#pos real_type t1#typ t1 t1'
	  | Float_to_real ->
	      term_coerce t1#pos real_type t1#typ t1 t1'
	  | Round(f,_rm) ->
              term_coerce t1#pos (JCTnative (Tgenfloat f)) t1#typ t1 t1'
	end
    | JCTderef(t1,lab',fi) ->
	let lab = if relocate && lab' = LabelHere then lab else lab' in
	let mc,_ufi_opt = tderef_mem_class ~type_safe t1 fi in
	begin match mc with
	  | JCmem_field fi' ->
	      assert (fi.fi_tag = fi'.fi_tag);
              let t1' = ft t1 in
              let mem =
		tmemory_var ~label_in_name:global_assertion lab
		  (JCmem_field fi,t1#region)
	      in
              LApp("select",[ mem; t1' ])
	  | JCmem_plain_union vi ->
	      let t1,off = tdestruct_union_access t1 (Some fi) in
	      (* Retrieve bitvector *)
              let t1' = ft t1 in
              let mem =
		tmemory_var ~label_in_name:global_assertion lab
		  (JCmem_plain_union vi,t1#region)
	      in
              let e' = LApp("select",[ mem; t1' ]) in
	      (* Retrieve subpart of bitvector for specific subfield *)
	      let off = match off with
		| Int_offset s -> s
		| _ -> assert false (* TODO *)
	      in
	      let size =
		match fi.fi_bitsize with
		  | Some x -> x / 8
		  | None -> assert false
	      in
	      let off = string_of_int off and size = string_of_int size in
	      let e' =
		LApp("extract_bytes",
		     [ e'; LConst(Prim_int off); LConst(Prim_int size) ])
	      in
	      (* Convert bitvector into appropriate type *)
	      begin match fi.fi_type with
		| JCTenum ri -> LApp(logic_enum_of_bitvector ri,[e'])
		| JCTnative Tinteger -> LApp(logic_integer_of_bitvector,[e'])
                | JCTnative _ -> assert false (* TODO ? *)
                | JCTtype_var _ -> assert false (* TODO ? *)
                | JCTpointer (_, _, _) -> assert false (* TODO ? *)
                | JCTlogic _ -> assert false (* TODO ? *)
                | JCTany -> assert false (* TODO ? *)
                | JCTnull -> assert false (* TODO ? *)
	      end
	  | JCmem_bitvector ->
	      (* Retrieve bitvector *)
              let t1' = ft t1 in
	      let mem =
		tmemory_var ~label_in_name:global_assertion lab
		  (JCmem_bitvector,t1#region)
	      in
	      let off =
		match field_offset_in_bytes fi with
		  | Some x -> x
		  | None -> assert false
	      in
	      let size =
		match fi.fi_bitsize with
		  | Some x -> x / 8
		  | None -> assert false
	      in
	      let off = string_of_int off and size = string_of_int size in
	      let e' =
		LApp("select_bytes",
		     [ mem; t1'; LConst(Prim_int off); LConst(Prim_int size) ])
	      in
	      (* Convert bitvector into appropriate type *)
	      begin match fi.fi_type with
		| JCTenum ri -> LApp(logic_enum_of_bitvector ri,[e'])
		| _ty -> assert false (* TODO *)
	      end
	end
    | JCTapp app ->
        let f = app.app_fun in
        let args =
	  List.fold_right (fun arg acc -> (ft arg) :: acc) app.app_args []
        in
        let args =
          try List.map2 (fun e e' -> (e,e')) app.app_args args
          with Invalid_argument _ -> assert false
        in
        let args =
          try
            List.map2
              (fun v (t,t') -> term_coerce t#pos v.vi_type t#typ t t')
              f.li_parameters args
          with Invalid_argument _ ->
            eprintf "fun = %s, len pars = %d, len args' = %d@."
              f.li_name
              (List.length f.li_parameters)
              (List.length args);
            assert false
        in
	let relab (lab1,lab2) =
	  (lab1, if lab2 = LabelHere then lab else lab2)
	in
	let label_assoc =
	  if relocate then
	    (LabelHere,lab) :: List.map relab app.app_label_assoc
	  else app.app_label_assoc
	in
        make_logic_fun_call ~label_in_name:global_assertion
	  ~region_assoc:app.app_region_assoc
	  ~label_assoc:label_assoc
	  f args
    | JCTold t1 ->
	let lab = if relocate && oldlab = LabelHere then lab else oldlab in
	term ~type_safe ~global_assertion ~relocate lab oldlab t1
    | JCTat(t1,lab') ->
	let lab = if relocate && lab' = LabelHere then lab else lab' in
	term ~type_safe ~global_assertion ~relocate lab oldlab t1
    | JCTrange(_t1,_t2) -> Jc_typing.typing_error t#pos "Unsupported range in term, sorry" (* TODO ? *)
    | JCTmatch(t, ptl) ->
        let t' = ft t in
        (* TODO: use a temporary variable for t' *)
        (* if the pattern-matching is incomplete, default value is true *)
        let ptl',lets =
          pattern_list_term ft t' t#typ ptl (LConst(Prim_bool true)) in
	concat_pattern_lets lets;
        ptl'
  in
  (if t#mark <> "" then
     Tnamed(reg_check ~mark:t#mark t#pos,t')
   else
     t')

let () = ref_term := term

let named_term ~type_safe ~global_assertion ~relocate lab oldlab t =
  let t' = term ~type_safe ~global_assertion ~relocate lab oldlab t in
  match t' with
    | Tnamed _ -> t'
    | _ ->
        let n = reg_check ~mark:t#mark t#pos in
        Tnamed(n,t')


(******************************************************************************)
(*                                assertions                                  *)
(******************************************************************************)

let tag ~type_safe ~global_assertion ~relocate lab oldlab tag=
  match tag#node with
    | JCTtag st -> LVar (tag_name st)
    | JCTbottom -> LVar "bottom_tag"
    | JCTtypeof (t, _) ->
	let t' = term ~type_safe ~global_assertion ~relocate lab oldlab t in
	make_typeof t'

let rec assertion ~type_safe ~global_assertion ~relocate lab oldlab a =
  let fa = assertion ~type_safe ~global_assertion ~relocate lab oldlab in
  let ft = term ~type_safe ~global_assertion ~relocate lab oldlab in
  let ftag = tag ~type_safe ~global_assertion ~relocate lab oldlab in
  let term_coerce = term_coerce ~type_safe ~global_assertion lab in
  let a' = match a#node with
    | JCAtrue -> LTrue
    | JCAfalse -> LFalse
    | JCAif(t1,a2,a3) ->
        let t1' = ft t1 in
	let a2' = fa a2 in
	let a3' = fa a3 in
        LIf(t1',a2',a3')
    | JCAand al -> make_and_list (List.map fa al)
    | JCAor al -> make_or_list (List.map fa al)
    | JCAimplies(a1,a2) ->
	let a1' = fa a1 in
	let a2' = fa a2 in
	make_impl a1' a2'
    | JCAiff(a1,a2) ->
	let a1' = fa a1 in
	let a2' = fa a2 in
	make_equiv a1' a2'
    | JCAnot a1 ->
	let a1' = fa a1 in
	LNot a1'
    | JCArelation(t1,((`Beq | `Bneq as op),_),t2)
	when is_base_block t1 && is_base_block t2 ->
	let t1 =
	  match t1#node with JCTbase_block t1' -> t1' | _ -> assert false
	in
	let t2 =
	  match t2#node with JCTbase_block t2' -> t2' | _ -> assert false
	in
        let t1' = ft t1 in
        let t2' = ft t2 in
        let p = LPred("same_block", [ t1'; t2' ]) in
	begin match op with
	  | `Beq -> p
	  | `Bneq -> LNot p
	  | _ -> assert false
	end
    | JCArelation(t1,(_,(`Pointer | `Logic) as op),t2) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        LPred (pred_bin_op (op :> pred_bin_op),[ t1'; t2' ])
    | JCArelation(t1,(_, #native_operator_type as op),t2) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        let ty = native_operator_type op in
        LPred(pred_bin_op (op :> pred_bin_op),
              [ term_coerce t1#pos ty t1#typ t1 t1';
                term_coerce t2#pos ty t2#typ t2 t2' ])
    | JCAapp app ->
        let f = app.app_fun in
        let args =
	  List.fold_right (fun arg acc -> (ft arg) :: acc) app.app_args []
        in
        let args =
          try List.map2 (fun e e' -> (e,e')) app.app_args args
          with Invalid_argument _ -> assert false
        in
        let args =
          try
            List.map2
              (fun v (t,t') -> term_coerce t#pos v.vi_type t#typ t t')
              f.li_parameters args
          with Invalid_argument _ ->
            eprintf "fun = %s, len pars = %d, len args' = %d@."
              f.li_name
              (List.length f.li_parameters)
              (List.length args);
            assert false
        in
	let label_assoc =
	  if relocate then
	    let relab (lab1,lab2) =
	      (lab1, if lab2 = LabelHere then lab else lab2)
	    in
	    (LabelHere,lab) :: List.map relab app.app_label_assoc
	  else app.app_label_assoc
	in
        make_logic_pred_call
	  ~label_in_name:global_assertion
	  ~region_assoc:app.app_region_assoc
	  ~label_assoc:label_assoc
	  f args
    | JCAquantifier(Forall,v,trigs,a1) ->
        LForall(v.vi_final_name,
                tr_var_base_type v,
                triggers fa ft trigs,
                fa a1)
    | JCAquantifier(Exists,v,trigs, a1) ->
        LExists(v.vi_final_name,
                tr_var_base_type v,
                triggers fa ft trigs,
                fa a1)
    | JCAold a1 ->
	let lab = if relocate && oldlab = LabelHere then lab else oldlab in
	assertion ~type_safe ~global_assertion ~relocate lab oldlab a1
    | JCAat(a1,lab') ->
	let lab = if relocate && lab' = LabelHere then lab else lab' in
	assertion ~type_safe ~global_assertion ~relocate lab oldlab a1
    | JCAfresh t1 ->
	let ac = tderef_alloc_class ~type_safe t1 in
	let lab = if relocate && oldlab = LabelHere then lab else oldlab in
	let _,alloc =
	  talloc_table_var ~label_in_name:global_assertion lab (ac,t1#region)
	in
        let valid =
	  begin match ac with
	    | JCalloc_root _ ->
              let f = "valid" in
              let t1' = ft t1 in
              LPred(f,[alloc; t1' ])
	    | JCalloc_bitvector ->
              let f = "valid_bytes" in
              let t1' = ft t1 in
              LPred(f,[ alloc; t1'])
	  end
        in
        LNot valid
    | JCAbool_term t1 ->
        let t1' = ft t1 in
        LPred("eq",[ t1'; LConst(Prim_bool true) ])
    | JCAinstanceof (t1, _, st) ->
      let t1' = ft t1 in
      LPred ("instanceof", [t1'; LVar (tag_name st)])
    | JCAmutable(te, st, ta) ->
        let te' = ft te in
        let tag = ftag ta in
        let mutable_field = LVar (mutable_name (JCtag(st, []))) in
        LPred("eq", [ LApp("select", [ mutable_field; te' ]); tag ])
    | JCAeqtype(tag1,tag2,_st_opt) ->
        let tag1' = ftag tag1 in
        let tag2' = ftag tag2 in
        LPred("eq", [ tag1'; tag2' ])
    | JCAsubtype(tag1,tag2,_st_opt) ->
        let tag1' = ftag tag1 in
        let tag2' = ftag tag2 in
        LPred("subtag", [ tag1'; tag2' ])
    | JCAlet(vi,t,p) ->
	LLet(vi.vi_final_name,ft t, fa p)
    | JCAmatch(arg, pal) ->
        let arg' = ft arg in
        (* TODO: use a temporary variable for arg' *)
        let pal', _ = pattern_list_assertion fa arg' arg#typ
          pal LTrue in
        pal'
  in
  let a' = bind_pattern_lets a' in
  if a#mark = "" then a' else LNamed(reg_check ~mark:a#mark a#pos, a')

and triggers fa ft trigs =
  let pat = function
    | JCAPatT t -> LPatT (ft t)
    | JCAPatP a -> LPatP (fa a) in
  List.map (List.map pat) trigs

let mark_assertion pos a' =
  match a' with
    | LNamed _ -> a'
    | _ -> LNamed(reg_check pos, a')

let named_assertion ~type_safe ~global_assertion ~relocate lab oldlab a =
  let a' =
    assertion ~type_safe ~global_assertion ~relocate lab oldlab a
  in
  mark_assertion a#pos a'


(******************************************************************************)
(*                                  Locations                                 *)
(******************************************************************************)

let rec pset ~type_safe ~global_assertion before loc =
  let fpset = pset ~type_safe ~global_assertion before in
  let ft = term ~type_safe ~global_assertion ~relocate:false before before in
  let term_coerce = term_coerce ~type_safe ~global_assertion before in
  match loc#node with
    | JCLSderef(locs, lab, fi, _r) ->
      let m = tmemory_var ~label_in_name:global_assertion lab (JCmem_field fi, locs#region) in
      LApp ("pset_deref", [m; fpset locs])
    | JCLSvar vi ->
        let m = tvar ~label_in_name:global_assertion before vi in
        LApp("pset_singleton", [m])
    | JCLSrange(ls,None,None) ->
        let ls = fpset ls in
        LApp("pset_all", [ls])
    | JCLSrange(ls,None,Some b) ->
        let ls = fpset ls in
        let b' = ft b in
        LApp("pset_range_left",
             [ls;
              term_coerce b#pos integer_type b#typ b b'])
    | JCLSrange(ls,Some a,None) ->
        let ls = fpset ls in
        let a' = ft a in
        LApp("pset_range_right",
             [ls;
              term_coerce a#pos integer_type a#typ a a'])
    | JCLSrange(ls,Some a,Some b) ->
        let ls = fpset ls in
        let a' = ft a in
        let b' = ft b in
        LApp("pset_range",
             [ls;
              term_coerce a#pos integer_type a#typ a a';
              term_coerce b#pos integer_type b#typ b b'])
    | JCLSrange_term(ls,None,None) ->
        let ls = LApp("pset_singleton",[ ft ls ]) in
        LApp("pset_all", [ls])
    | JCLSrange_term(ls,None,Some b) ->
        let ls = LApp("pset_singleton",[ ft ls ]) in
        let b' = ft b in
        LApp("pset_range_left",
             [ls;
              term_coerce b#pos integer_type b#typ b b'])
    | JCLSrange_term(ls,Some a,None) ->
        let ls = LApp("pset_singleton",[ ft ls ]) in
        let a' = ft a in
        LApp("pset_range_right",
             [ls;
              term_coerce a#pos integer_type a#typ a a'])
    | JCLSrange_term(ls,Some a,Some b) ->
        let ls = LApp("pset_singleton",[ ft ls ]) in
        let a' = ft a in
        let b' = ft b in
        LApp("pset_range",
             [ls;
              term_coerce a#pos integer_type a#typ a a';
              term_coerce b#pos integer_type b#typ b b'])
    | JCLSat(locs,_) -> fpset locs

let rec collect_locations ~type_safe ~global_assertion ~in_clause before (refs, mems) loc =
  let ft = term ~type_safe ~global_assertion ~relocate:false before before in
  let ef = Jc_effect.location ~in_clause empty_fun_effect loc in
  match loc#node with
    | JCLderef (e, lab, fi, _fr) ->
        let iloc = pset ~type_safe ~global_assertion lab e in
        (* ...?  if field_of_union fi then FVvariant (union_of_field fi) else *)
        let mcr = JCmem_field fi, location_set_region e in
        refs, MemoryMap.add_merge (@) mcr [iloc, ef] mems
    | JCLderef_term (t1, fi) ->
        let iloc = LApp ("pset_singleton", [ft t1]) in
        let mcr = JCmem_field fi, t1#region in
        refs, MemoryMap.add_merge (@) mcr [iloc, ef] mems
    | JCLvar vi ->
        let var = vi.vi_final_name in
        (StringMap.add var true refs,mems)
    | JCLat (loc, _lab) ->
        collect_locations ~type_safe ~global_assertion ~in_clause before (refs, mems) loc

let rec collect_pset_locations ~type_safe ~global_assertion loc =
  let ft = term ~type_safe ~global_assertion ~relocate:false in
  match loc#node with
    | JCLderef (e, lab, _fi, _fr) ->
        pset ~type_safe ~global_assertion lab e
    | JCLderef_term (t1, _fi) ->
	let lab = match t1#label with Some l -> l | None -> assert false in
	LApp ("pset_singleton",[ ft lab lab t1 ])
    | JCLvar _vi ->
	LVar "pset_empty"
    | JCLat (loc, _lab) ->
        collect_pset_locations ~type_safe ~global_assertion loc

let location_set_all_of_location loc =
  location_set_with_node loc @@ JCLSrange_term (term_of_location loc, None, None)

let tr_assigns ~type_safe ?region_list before ef ?(allocates=None) locs loc =
  match locs with
  | None -> LTrue
  | Some locs ->
    let refs =
      VarMap.fold
        (fun v _labs m -> StringMap.add v.vi_final_name false m)
        ef.fe_writes.e_globals
        StringMap.empty
    in
    let mems =
      MemoryMap.(
        fold
         (fun (fi, r) _labs acc ->
           (* TODO: bug some assigns \nothing clauses are not translated e.g. in Purse.java *)
           (* (perhaps when no region is used). The first test resolve the problem but may hide another bug:*)
           (*  What must be region_list when --no-region is used? *)

           (* More exact apprixmation (at least fixes both previously encountered bugs): *)
           (* generate not_assigns for parameters and constant (i.e. global) memories. *)
           (* Also generate not_assigns always when in SepNone sparation mode. *)
           if !Jc_options.separation_sem = SepNone || (* no regions used at all *)
              not (Region.polymorphic r) || (* constant memory, not passed as argument, but counted as effect (global) *)
              Option_misc.map_default (RegionList.mem r) true region_list (* passed as argument and counted as effect *)
           then
             add (fi, r) [] acc
           else (* if not counted as effect, then it's automatically immutable in the function scope *)
             acc)
         ef.fe_writes.e_memories
         empty)
    in
    let allocates =
      (* Add assigns translated from allocates clause: one pset_all for each possible downcast *)
      Option_misc.map_default
        List.(flatten % map
          (fun l ->
             MemoryMap.fold
              (fun (mc, r) _ acc ->
                let ls = location_set_all_of_location l in
                match mc with
                | JCmem_field fi when Region.equal (location_set_region ls) r ->
                  let node =
                    match l#node with
                    | JCLvar ({ vi_type = JCTpointer (JCtag (si, []), _, _) } as v)
                      when StructOrd.equal si.si_hroot fi.fi_hroot ->
                      let st = fi.fi_struct in
                      let typ = JCTpointer (JCtag (st, []), None, None) in
                      JCLderef (
                        location_set_with_node ls @@
                          JCLSrange_term (
                            new term ~pos:l#pos ~typ ~label:LabelHere ~region:r @@
                              JCTcast (Term.mkvar v (), LabelHere, st),
                            None,
                            None),
                        LabelHere,
                        fi,
                        r)
                    | _ -> JCLderef (ls, LabelHere, fi, r)
                  in
                  location_with_node ~typ:fi.fi_type ~region:r l node :: acc
                | _ -> acc)
              ef.fe_writes.e_memories
              []))
        []
        (Option_misc.map snd allocates)
    in
    let refs, mems =
      let tr_locations = collect_locations ~type_safe ~in_clause:Assigns in
      let fold f l init = ListLabels.fold_left l ~init ~f in
         (refs, mems)
      |> fold (tr_locations ~global_assertion:false before) locs
      |> fold (tr_locations ~global_assertion:true LabelHere) allocates
    in
    let a =
      StringMap.fold
        (fun v p acc ->
           if p then acc else
             let at = lvar ~constant:false (* <<- CHANGE THIS *) ~label_in_name:false in
             make_and acc (LPred("eq", [at LabelPost v; at before v])))
        refs LTrue
    in
    MemoryMap.fold
      (fun (mc, r) pes acc ->
         let v = memory_name (mc, r) in
         let ac = alloc_class_of_mem_class mc in
         let _, alloc = talloc_table_var ~label_in_name:false before (ac, r) in
         let ps, efs = List.split pes in
         let ef =
           fef_filter_by_region (fun r ->    not (Region.polymorphic r)
                                             || Option_misc.map_default (RegionList.mem r) true region_list)
             ef
         in
         let ef = fef_diff (List.fold_left fef_union empty_fun_effect efs) ef in
         let wrap_in_foralls =
           List.fold_right (fun (n, _, ty) a -> LForall (n, ty, [], a)) @@
           tmodel_parameters ~label_in_name:false ef.fe_reads
         in
         make_and acc @@
         let a = LPred("not_assigns",
                       [alloc;
                        lvar ~constant:false (* <<- CHANGE THIS *) ~label_in_name:false before v;
                        LDeref v;
                        location_list' ps])
         in
         LNamed (reg_check loc, wrap_in_foralls a))
      mems a

let reads ~type_safe ~global_assertion locs (mc,r) =
  let _refs, mems =
    List.fold_left (collect_locations ~type_safe ~global_assertion ~in_clause:Reads LabelOld)
                   (StringMap.empty, MemoryMap.empty)
                   locs
  in
  let ps, _efs = List.split @@ MemoryMap.find_or_default (mc, r) [] mems in
  location_list' ps


(******************************************************************************)
(*                                Expressions                                 *)
(******************************************************************************)

let bounded lb rb s =
  let n = Num.num_of_int s in Num.le_num lb n && Num.le_num n rb

let lbounded lb s =
  let n = Num.num_of_int s in Num.le_num lb n

let rbounded rb s =
  let n = Num.num_of_int s in Num.le_num n rb

let rec const_int_term t =
  match t # node with
    | JCTconst (JCCinteger s) -> Some (Numconst.integer s)
    | JCTvar vi ->
	begin
	  try
	    let _, init =
	      Jc_stdlib.Hashtbl.find
		Jc_typing.logic_constants_table
		vi.vi_tag
	    in
	      const_int_term init
	  with Not_found -> None
	end
    | JCTapp app ->
	begin
	  try
	    let _, init =
	      Jc_stdlib.Hashtbl.find
		Jc_typing.logic_constants_table
		app.app_fun.li_tag
	    in
	      const_int_term init
	  with Not_found -> None
	end
    | JCTunary (uop, t) ->
	let no = const_int_term t in
	  Option_misc.fold
	    (fun n _ -> match uop with
	       | `Uminus, `Integer -> Some (Num.minus_num n)
	       | _ -> None)
	    no None
    | JCTbinary (t1, bop, t2) ->
	let no1 = const_int_term t1 in
	let no2 = const_int_term t2 in
	  begin match no1, no2 with
	    | Some n1, Some n2 ->
		begin match bop with
		  | `Badd, `Integer -> Some (n1 +/ n2)
		  | `Bsub, `Integer -> Some (n1 -/ n2)
		  | `Bmul, `Integer -> Some (n1 */ n2)
		  | `Bdiv, `Integer ->
		      let n = n1 // n2 in
			if Num.is_integer_num n then
			  Some n
			else
			  None
		  | `Bmod, `Integer -> Some (Num.mod_num n1 n2)
		  | _ -> None
		end
	    | _ -> None
	  end
    | JCTrange_cast (t, _) -> const_int_term t
    | JCTconst _ | JCTshift _ | JCTderef _
    | JCTold _ | JCTat _
    | JCToffset _ | JCTaddress _ | JCTinstanceof _ | JCTbase_block _
    | JCTreal_cast _ | JCTif _ | JCTrange _
    | JCTcast _ | JCTmatch _ | JCTlet _ | JCTbitwise_cast _ ->
	assert false

let rec const_int_expr e =
  match e # node with
    | JCEconst (JCCinteger s) -> Some (Numconst.integer s)
    | JCEvar vi ->
	begin
	  try
	    let _, init =
	      Jc_stdlib.Hashtbl.find
		Jc_typing.logic_constants_table
		vi.vi_tag
	    in
	      const_int_term init
	  with Not_found -> None
	end
    | JCEapp call ->
	begin match call.call_fun with
	  | JClogic_fun li ->
	      begin
		try
		  let _, init =
		    Jc_stdlib.Hashtbl.find
		      Jc_typing.logic_constants_table
		      li.li_tag
		  in
		    const_int_term init
		with Not_found -> None
	      end
	  | JCfun _ -> None
	end
    | JCErange_cast (e, _) -> const_int_expr e
    | JCEunary (uop, e) ->
	let no = const_int_expr e in
	  Option_misc.fold
	    (fun n _ -> match uop with
	       | `Uminus, `Integer -> Some (Num.minus_num n)
	       | _ -> None)
	    no None
    | JCEbinary (e1, bop, e2) ->
	let no1 = const_int_expr e1 in
	let no2 = const_int_expr e2 in
	  begin match no1, no2 with
	    | Some n1, Some n2 ->
		begin match bop with
		  | `Badd, `Integer -> Some (n1 +/ n2)
		  | `Bsub, `Integer -> Some (n1 -/ n2)
		  | `Bmul, `Integer -> Some (n1 */ n2)
		  | `Bdiv, `Integer ->
		      let n = n1 // n2 in
			if Num.is_integer_num n then
			  Some n
			else
			  None
		  | `Bmod, `Integer -> Some (Num.mod_num n1 n2)
		  | _ -> None
		end
	    | _ -> None
	  end
    | JCEderef _ | JCEoffset _ | JCEbase_block _
    | JCEaddress _ | JCElet _ | JCEassign_var _
    | JCEassign_heap _ ->
	None
    | JCEif _ ->
	None (* TODO *)
    | JCEconst _ | JCEinstanceof _ | JCEreal_cast _
    | JCEalloc _ | JCEfree _ | JCEreinterpret _ | JCEassert _
    | JCEcontract _ | JCEblock _ | JCEloop _
    | JCEreturn_void | JCEreturn _ | JCEtry _
    | JCEthrow _ | JCEpack _ | JCEunpack _
    | JCEcast _ | JCEmatch _ | JCEshift _
    | JCEbitwise_cast _ | JCEfresh _ ->
	assert false

let destruct_pointer e =
  let ptre, off = match e # node with
    | JCEshift (e1, e2) ->
	e1,
	(match const_int_expr e2 with
	   | Some n -> Int_offset (Num.int_of_num n)
           | None -> Expr_offset e2)
    | _ -> e, Int_offset 0
  in
    match ptre # typ with
      | JCTpointer (_, lb, rb) -> ptre, off, lb, rb
      | _ -> assert false

let rec make_lets l e =
  match l with
    | [] -> e
    | (tmp,a)::l -> mk_expr (Let(tmp,a,make_lets l e))

let old_to_pre = function
  | LabelOld -> LabelPre
  | lab -> lab

let old_to_pre_term =
  Jc_iterators.map_term
    (fun t -> match t#node with
       | JCTold t'
       | JCTat(t',LabelOld) ->
	   new term_with
	     ~node:(JCTat(t',LabelPre)) t
       | JCTderef(t',LabelOld,fi) ->
	   new term_with
	     ~node:(JCTderef(t',LabelPre,fi)) t
       | _ -> t)

let rec old_to_pre_lset lset =
  match lset#node with
    | JCLSvar _ -> lset
    | JCLSderef(lset,lab,fi,_region) ->
	new location_set_with
          ~typ:lset#typ
	  ~node:(JCLSderef(old_to_pre_lset lset, old_to_pre lab, fi, lset#region))
	  lset
    | JCLSrange(lset,t1,t2) ->
	new location_set_with
          ~typ:lset#typ
	  ~node:(JCLSrange(old_to_pre_lset lset,
			   Option_misc.map old_to_pre_term t1,
			   Option_misc.map old_to_pre_term t2))
	  lset
    | JCLSrange_term(lset,t1,t2) ->
	new location_set_with
          ~typ:lset#typ
	  ~node:(JCLSrange_term(old_to_pre_term lset,
				Option_misc.map old_to_pre_term t1,
				Option_misc.map old_to_pre_term t2))
	  lset
    | JCLSat(lset,lab) ->
	new location_set_with
          ~typ:lset#typ
	  ~node:(JCLSat(old_to_pre_lset lset,old_to_pre lab))
	  lset

let rec old_to_pre_loc loc =
  match loc#node with
    | JCLvar _ -> loc
    | JCLat(l,lab) ->
	new location_with
          ~typ:loc#typ
	  ~node:(JCLat(old_to_pre_loc l, old_to_pre lab))
	  loc
    | JCLderef(lset,lab,fi,_region) ->
	new location_with
          ~typ:loc#typ
	  ~node:(JCLderef(old_to_pre_lset lset,old_to_pre lab, fi, lset#region))
	  loc
    | JCLderef_term(t1,fi) ->
	new location_with
          ~typ:loc#typ
	  ~node:(JCLderef_term(old_to_pre_term t1,fi))
	  loc

let assumption al a' =
  let ef = List.fold_left Jc_effect.assertion empty_effects al in
  let read_effects =
    local_read_effects ~callee_reads:ef ~callee_writes:empty_effects
  in
  mk_expr (BlackBox(Annot_type(LTrue, unit_type, read_effects, [], a', [])))

let check al a' =
  let ef = List.fold_left Jc_effect.assertion empty_effects al in
  let read_effects =
    local_read_effects ~callee_reads:ef ~callee_writes:empty_effects
  in
  mk_expr (BlackBox(Annot_type(a', unit_type, read_effects, [], LTrue, [])))

(* decreases clauses: stored in global table for later use at each call sites *)

let decreases_clause_table = Hashtbl.create 17

let term_zero = new term ~typ:integer_type (JCTconst(JCCinteger "0"))

let dummy_measure = (term_zero, None)

let get_measure_for f =
  match !Jc_options.termination_policy with
    | TPalways ->
        (try
          Hashtbl.find decreases_clause_table (f.fun_tag)
        with Not_found ->
          Hashtbl.add decreases_clause_table (f.fun_tag) dummy_measure;
          eprintf
            "Warning: generating dummy decrease variant for recursive \
             function %s. Please provide a real variant or set \
             termination policy to user or never\n%!" f.fun_name;
          dummy_measure)
    | TPuser ->
        (try
          Hashtbl.find decreases_clause_table (f.fun_tag)
         with Not_found -> raise Exit)
    | TPnever -> raise Exit

(* Translate the heap update `e1.fi = tmp2'

   essentially we want

   let tmp1 = [e1] in
   fi := upd(fi, tmp1, tmp2)

   special cases are considered to avoid statically known safety properties:
   if e1 has the form p + i then we build

   let tmpp = p in
   let tmpi = i in
   let tmp1 = shift(tmpp, tmpi) in
    // depending on type of p and value of i
   ...
*)

let rec make_upd_simple mark pos e1 fi tmp2 =
  (* Temporary variables to avoid duplicating code *)
  let tmpp = tmp_var_name () in
  let tmpi = tmp_var_name () in
  let tmp1 = tmp_var_name () in
  (* Define memory and allocation table *)
  let mc, _ufi_opt = deref_mem_class ~type_safe:false e1 fi in
  let mem = memory_name (mc, e1#region) in
  let ac = alloc_class_of_mem_class mc in
  let alloc = alloc_table_var (ac, e1#region) in
  let p, off, _, _ = destruct_pointer e1 in
  let p' = expr p in
  let i' = offset off in
  let letspi = [tmpp, p'; tmpi, i'; tmp1, make_app "shift" [mk_var tmpp; mk_var tmpi]] in
  tmp1, letspi,
   if safety_checking () then
     make_guarded_app ~mark PointerDeref pos "offset_upd_" [alloc; mk_var mem; mk_var tmpp; mk_var tmpi; mk_var tmp2]
   else
     make_app "safe_upd_" [mk_var mem; mk_var tmp1; mk_var tmp2]

and make_upd_union mark pos off e1 fi tmp2 =
  let e1' = expr e1 in
  (* Convert value assigned into bitvector *)
  let e2' = match fi.fi_type with
    | JCTenum ri -> make_app (logic_bitvector_of_enum ri) [mk_var tmp2]
    | JCTnative Tinteger -> make_app logic_bitvector_of_integer [mk_var tmp2]
    | JCTnative _ -> assert false (* TODO ? *)
    | JCTtype_var _ -> assert false (* TODO ? *)
    | JCTpointer (_, _, _) -> assert false (* TODO ? *)
    | JCTlogic _ -> assert false (* TODO ? *)
    | JCTany -> assert false (* TODO ? *)
    | JCTnull -> assert false (* TODO ? *)
  in
  (* Temporary variables to avoid duplicating code *)
  let tmp1 = tmp_var_name () in
  let tmp2 = tmp_var_name () in
  let v1 = Jc_pervasives.var e1#typ tmp1 in
  let e1 = new expr_with ~node:(JCEvar v1) e1 in
  let size =
    match fi.fi_bitsize with
      | Some x -> x / 8
      | None -> assert false
  in
  let union_size =
    (union_type e1#typ).ri_union_size_in_bytes
  in
  let e2' =
    if size = union_size then
      (* TODO: deal with offset which should be null *)
      e2'
    else
      (* Retrieve bitvector for access to union *)
      let deref = make_deref_simple mark pos e1 fi in
      (* Replace subpart of bitvector for specific subfield *)
      let off = match off with
	| Int_offset s -> s
	| _ -> assert false (* TODO *)
      in
      let off = string_of_int off and size = string_of_int size in
      make_app "replace_bytes"
	[ deref; mk_expr (Cte(Prim_int off)); mk_expr (Cte(Prim_int size)); e2' ]
  in
  let lets = [ (tmp1,e1'); (tmp2,e2') ] in
  let tmp1, lets', e' = make_upd_simple mark pos e1 fi tmp2 in
  tmp1, lets @ lets', e'

and make_upd_bytes mark pos e1 fi tmp2 =
  let e1' = expr e1 in
  (* Convert value assigned into bitvector *)
  let e2' = match fi.fi_type with
    | JCTenum ri -> make_app (logic_bitvector_of_enum ri) [mk_var tmp2]
    | _ty -> assert false (* TODO *)
  in
  (* Temporary variables to avoid duplicating code *)
  let tmp1 = tmp_var_name () in
  let v1 = Jc_pervasives.var e1#typ tmp1 in
  let e1 = new expr_with ~node:(JCEvar v1) e1 in
  (* Define memory and allocation table *)
  let mem = plain_memory_var (JCmem_bitvector,e1#region) in
  let alloc = alloc_table_var (JCalloc_bitvector,e1#region) in
  (* Store bitvector *)
  let off =
    match field_offset_in_bytes fi with
      | Some x -> x
      | None -> assert false
  in
  let size =
    match fi.fi_bitsize with
      | Some x ->  x / 8
      | None -> assert false
  in
  let off = string_of_int off and size = string_of_int size in
  let e' =
    if safety_checking () then
      make_guarded_app ~mark PointerDeref pos "upd_bytes_"
        [ alloc; mem; mk_var tmp1;
          mk_expr (Cte(Prim_int off)); mk_expr (Cte(Prim_int size));
	  mk_var tmp2 ]
    else
      make_app "safe_upd_bytes_"
	[ mem; mk_var tmp1; mk_expr (Cte(Prim_int off));
          mk_expr (Cte(Prim_int size)); mk_var tmp2 ]
  in
  let lets = [ (tmp1,e1'); (tmp2,e2') ] in
  tmp1, lets, e'

and make_upd mark pos e1 fi e2 =
  (* Value assigned stored in temporary at that point *)
  let v2 = match e2#node with JCEvar v2 -> v2 | _ -> assert false in
  let tmp2 = v2.vi_name in
  (* Dispatch depending on kind of memory *)
  let mc,ufi_opt = deref_mem_class ~type_safe:false e1 fi in
  match mc,ufi_opt with
    | JCmem_field fi', None ->
	assert (fi.fi_tag = fi'.fi_tag);
	make_upd_simple mark pos e1 fi tmp2
    | JCmem_field fi', Some ufi ->
	assert (fi.fi_tag = fi'.fi_tag);
        let tmp1, lets, e1' = make_upd_simple mark pos e1 fi tmp2 in
	let mems = overlapping_union_memories ufi in
	let ef =
	  List.fold_left
	    (fun ef mc -> add_memory_effect LabelHere ef (mc,e1#region))
	    empty_effects mems
	in
	let write_effects =
	  local_write_effects ~callee_reads:empty_effects ~callee_writes:ef
	in
	let e2' =
	  mk_expr(BlackBox(Annot_type(LTrue, unit_type, [], write_effects, LTrue, [])) )
	in
	tmp1, lets, append e1' e2'
    | JCmem_plain_union _vi, _ ->
	let e1,off = destruct_union_access e1 (Some fi) in
	make_upd_union mark pos off e1 fi tmp2
    | JCmem_bitvector, _ ->
	make_upd_bytes mark pos e1 fi tmp2

(* Translate the heap access `e.fi'

   special cases are considered to avoid statically known safety properties:
   if e1 has the form p + i then we build an access that depends on the
   type of p and the value of i
*)
and make_deref_simple mark pos e fi =
  (* Define memory and allocation table *)
  let mc,_ufi_opt = deref_mem_class ~type_safe:false e fi in
  let mem = memory_var (mc,e#region) in
  let ac = alloc_class_of_mem_class mc in
  let alloc = alloc_table_var (ac,e#region) in
  let e' =
    if safety_checking() then
      match destruct_pointer e with
	| _, Int_offset s, Some lb, Some rb when bounded lb rb s ->
            make_app "safe_acc_"
              [ mem ; expr e ]
	| p, (Int_offset s as off), Some lb, _ when lbounded lb s ->
            make_guarded_app ~mark IndexBounds pos "lsafe_lbound_acc_"
              [ alloc; mem; expr p; offset off ]
	| p, (Int_offset s as off), _, Some rb when rbounded rb s ->
            make_guarded_app ~mark IndexBounds pos "rsafe_rbound_acc_"
              [ alloc; mem; expr p; offset off ]
	| p, Int_offset s, None, None when s = 0 ->
            make_guarded_app ~mark PointerDeref pos "acc_"
              [ alloc; mem ; expr p ]
	| p, off, _, _ ->
            make_guarded_app ~mark PointerDeref pos "offset_acc_"
              [ alloc; mem ; expr p; offset off ]
    else
      make_app "safe_acc_" [ mem; expr e ]
  in e'

and make_deref_union mark pos off e fi =
  (* Retrieve bitvector *)
  let e' = make_deref_simple mark pos e fi in
  (* Retrieve subpart of bitvector for specific subfield *)
  let off = match off with
    | Int_offset s -> s
    | _ -> assert false (* TODO *)
  in
  let size =
    match fi.fi_bitsize with
      | Some x -> x / 8
      | None -> assert false
  in
  let off = string_of_int off and size = string_of_int size in
  let e' =
    make_app "extract_bytes" [ e'; mk_expr (Cte(Prim_int off)); mk_expr(Cte(Prim_int size)) ]
  in
  (* Convert bitvector into appropriate type *)
  match fi.fi_type with
    | JCTenum ri -> make_app (logic_enum_of_bitvector ri) [e']
    | _ty -> assert false (* TODO *)

and make_deref_bytes mark pos e fi =
  (* Define memory and allocation table *)
  let mem = memory_var (JCmem_bitvector,e#region) in
  let alloc = alloc_table_var (JCalloc_bitvector,e#region) in
  (* Retrieve bitvector *)
  let off =
    match field_offset_in_bytes fi with
      | Some x -> x
      | None -> assert false
  in
  let size =
    match fi.fi_bitsize with
      | Some x ->  x / 8
      | None -> assert false
  in
  let off = string_of_int off and size = string_of_int size in
  let e' =
    if safety_checking () then
      make_guarded_app ~mark PointerDeref pos "acc_bytes_"
        [ alloc; mem; expr e; mk_expr (Cte(Prim_int off));
          mk_expr (Cte(Prim_int size)) ]
    else
      make_app "safe_acc_bytes_"
	[ mem; expr e; mk_expr (Cte(Prim_int off));
          mk_expr (Cte(Prim_int size)) ]
  in
  (* Convert bitvector into appropriate type *)
  match fi.fi_type with
    | JCTenum ri -> make_app (logic_enum_of_bitvector ri) [e']
    | JCTnative t ->
	begin
	  match t with
	    | Treal  ->
		unsupported pos "bit-dependent cast over real numbers"
	    | Tgenfloat _ ->
		unsupported pos "bit-dependent cast over floating-point values"
	    | Tstring ->
		unsupported pos "bit-dependent cast over strings"
	    | Tinteger ->
		unsupported pos "bit-dependent cast over integers"
	    | Tboolean ->
		unsupported pos "bit-dependent cast over booleans"
	    | Tunit  ->
		unsupported pos "bit-dependent cast over type unit"
	end
    | JCTtype_var _ -> assert false (* TODO *)
    | JCTpointer (_, _, _) -> assert false (* TODO *)
    | JCTlogic _ -> assert false (* TODO *)
    | JCTany -> assert false (* TODO *)
    | JCTnull -> assert false (* TODO *)

(*
    | ty ->
	Format.eprintf "%a@." print_type ty;
	assert false (* TODO *)
*)

and make_deref mark pos e1 fi =
  (* Dispatch depending on kind of memory *)
  let mc,_uif_opt = deref_mem_class ~type_safe:false e1 fi in
  match mc with
    | JCmem_field _ ->
	make_deref_simple mark pos e1 fi
    | JCmem_plain_union _vi ->
	let e1,off = destruct_union_access e1 (Some fi) in
	make_deref_union mark pos off e1 fi
    | JCmem_bitvector ->
	make_deref_bytes mark pos e1 fi

and offset = function
  | Int_offset s -> mk_expr (Cte (Prim_int (string_of_int s)))
  | Expr_offset e ->
      coerce ~check_int_overflow:(safety_checking())
        e#mark e#pos integer_type e#typ e
        (expr e)
  | Term_offset _ -> assert false

and type_assert tmp ty e =
  let offset k e1 ty tmp =
    let ac = deref_alloc_class ~type_safe:false e1 in
    let _,alloc =
      talloc_table_var ~label_in_name:false LabelHere (ac,e1#region)
    in
    match ac with
      | JCalloc_root _ ->
          let f = match k with
	    | Offset_min -> "offset_min"
	    | Offset_max -> "offset_max"
          in
	  LApp(f,[alloc; LVar tmp])
      | JCalloc_bitvector ->
	  let st = pointer_struct ty in
          let f = match k with
	    | Offset_min -> "offset_min_bytes"
	    | Offset_max -> "offset_max_bytes"
          in
	  let s = string_of_int (struct_size_in_bytes st) in
	  LApp(f,[alloc; LVar tmp; LConst(Prim_int s)])
  in
  let a = match ty with
    | JCTpointer(_pc,n1o,n2o) ->
	let offset_mina n =
	  LPred ("le_int",
		 [offset Offset_min e ty tmp;
		  LConst (Prim_int (Num.string_of_num n))])
	in
	let offset_maxa n =
	  LPred ("ge_int",
		 [offset Offset_max e ty tmp;
		  LConst (Prim_int (Num.string_of_num n))])
	in
	begin match e#typ with
	  | JCTpointer (_si', n1o', n2o') ->
	      begin match n1o, n2o with
		| None, None -> LTrue
		| Some n, None ->
		    begin match n1o' with
		      | Some n' when Num.le_num n' n
                          && not Jc_options.verify_all_offsets
                          -> LTrue
		      | _ -> offset_mina n
		    end
		| None, Some n ->
		    begin match n2o' with
		      | Some n' when Num.ge_num n' n
                          && not Jc_options.verify_all_offsets
                          -> LTrue
		      | _ -> offset_maxa n
		    end
		| Some n1, Some n2 ->
		    begin match n1o', n2o' with
		      | None, None -> make_and (offset_mina n1) (offset_maxa n2)
		      | Some n1', None ->
			  if Num.le_num n1' n1 && not Jc_options.verify_all_offsets then
			    offset_maxa n2
			  else
			    make_and (offset_mina n1) (offset_maxa n2)
		      | None, Some n2' ->
			  if Num.ge_num n2' n2 && not Jc_options.verify_all_offsets then
			    offset_mina n1
			  else
			    make_and (offset_mina n1) (offset_maxa n2)
		      | Some n1', Some n2' ->
			  if Jc_options.verify_all_offsets then
			    make_and (offset_mina n1) (offset_maxa n2)
			  else
			    if Num.le_num n1' n1 then
			      if Num.ge_num n2' n2 then LTrue
                              else
				offset_maxa n2
			    else
			      if Num.ge_num n2' n2 then
				offset_mina n1
                              else
				make_and (offset_mina n1) (offset_maxa n2)
		    end
	      end
	  | JCTnull ->
	      begin match n1o, n2o with
		| None, None -> LTrue
		| Some n, None -> offset_mina n
		| None, Some n -> offset_maxa n
		| Some n1, Some n2 -> make_and (offset_mina n1) (offset_maxa n2)
	      end
	  | _ -> LTrue
	end
    | _ -> LTrue
  in
  (coerce ~check_int_overflow:(safety_checking())
    e#mark e#pos ty
    e#typ e (expr e),
   a)

and list_type_assert vi e (lets, params) =
  let ty = vi.vi_type in
  let tmp = tmp_var_name() (* vi.vi_name *) in
  let e,a = type_assert tmp ty e in
  (tmp, e, a) :: lets , (mk_var tmp) :: params

and value_assigned mark pos ty e =
    let tmp = tmp_var_name () in
    let e,a = type_assert tmp ty e in
    if a <> LTrue && safety_checking() then
      mk_expr (Let(tmp,e,make_check ~mark ~kind:IndexBounds pos
            (mk_expr (Assert(`ASSERT,a,mk_var tmp)))))
    else e

and make_reinterpret e st =
  let get_fi st =
    match st.si_fields with
    | [fi] -> fi
    | _ -> unsupported e#pos "reinterpretation for structure with several fields"
  in
  let s_from, fi_from = (* src. subtag & field info *)
    match e#typ with
    | JCTpointer (JCtag (st, _), _, _) -> tag_name st, get_fi st
    | _ -> unsupported e#pos "reinterpretation for a root pointer or a non-pointer"
  in
  let s_to, fi_to = tag_name st, get_fi st in (* dest. subtag & field_info *)
  let ac = deref_alloc_class ~type_safe:false e in
  let mc_from, mc_to = map_pair (fst % deref_mem_class ~type_safe:false e) (fi_from, fi_to) in
  let before = fresh_reinterpret_label () in

  (* call to [safe]_reinterpret_parameter *)
  let call_parameter =
    let alloc = plain_alloc_table_var (ac, e#region) in
    let mem_to = plain_memory_var (mc_to, e#region) in
    make_label before.lab_final_name @@
      match !Jc_options.inv_sem with
      | InvOwnership -> unsupported e#pos "reinterpret .. as construct is not supported when inv_sem = InvOwnership"
      | InvNone | InvArguments ->
        make_app (reinterpret_parameter_name ~safety_checking) [alloc; mk_var s_from; mk_var s_to; mem_to; expr e]
  in

  (* Let's now switch to terms and assume predicates instead of calling params... *)
  let before = LabelName before in
  let alloc = alloc_table_name (ac, e#region) in
  let at = lvar ~constant:false ~label_in_name:false in
  (* reinterpretation kind (operation):
     merging (e.g. char -> int) / splitting (e.g. int -> char) / plain (e.g. int -> long) *)
  let op =
    let from_bitsize, to_bitsize =
      map_pair
        (function
         | { fi_bitsize = Some s } -> s
         | _ -> unsupported e#pos "reinterpretation for field with no bitsize specified")
        (fi_from, fi_to)
    in
    match compare from_bitsize to_bitsize with
    | 0 -> `Retain
    | v when v > 0 -> `Split (from_bitsize / to_bitsize)
    | _ -> `Merge (to_bitsize / from_bitsize)
  in
  let e' =
    term
      ~type_safe:(safety_checking ())
      ~global_assertion:false
      ~relocate:false
      LabelHere
      before @@
        match term_of_expr e with
        | Some e -> e
        | None ->
          unsupported e#pos "the argument for reinterpret .. as should be an expression without side effects"
  in

  let alloc_assumption =
    let app l = LPred (reinterpret_cast_name op, [at before alloc; at LabelHere alloc; e'; LVar s_to] @ l) in
    match op with
    | `Retain -> app []
    | `Merge c | `Split c -> app [const_of_int c]
  in

  (* Assume reinterpretation predicates for all corresponingly shifted pointers *)
  let memory_assumption =
    let p, ps = "p", "ps" in
    let lp, lps = LVar p, LVar ps in
    let omin_omax =
      let app f =
        function
        | `Old -> LApp (f, [at before alloc; lp])
        | `New -> LApp (f, [at LabelHere alloc; lps])
      in
      (uncurry fdup2) @@ map_pair app ("offset_min", "offset_max")
    in
    let deref (where, p) ?boff offs =
      let mem =
        let old_mem, new_mem = map_pair (fun mc -> memory_name (mc, e#region)) (mc_from, mc_to) in
        function
        | `Old -> at before old_mem
        | `New -> at LabelHere new_mem
      in
      let shift t o1 o2 =
        match o1, o2 with
        | None, None -> t
        | Some o, None
        | None, Some o -> LApp ("shift", [t; o])
        | Some o1, Some o2 -> LApp ("shift", [t; LApp ("add_int", [o1; o2])])
      in
      LApp ("select", [mem where; shift p boff @@ match offs with 0 -> None | o -> Some (const_of_int o)])
    in
    let pred_names =
      let enum_name =
        function
        | { fi_type = JCTenum { ei_name = name } } -> name
        | _ -> unsupported e#pos "reinterpretation for structure with a non-enum field"
      in
      let from_name, to_name = map_pair enum_name (fi_from, fi_to) in
      [from_name ^ "_as_" ^ to_name; to_name ^ "_as_" ^ from_name]
    in
    let assumptions =
      let (dwhole, dpart), (omin, omax), c =
        let ret ((w, _), _ as w_p) c = map_pair deref w_p, omin_omax w, c in
        let merge, split = fdup2 ret (ret % swap) ((`New, lps), (`Old, lp)) in
        match op with
        | `Merge c -> merge c
        | `Retain when (List.hd pred_names).[0] = 'u' -> merge 1
        | `Retain -> split 1
        | `Split c -> split c
      in
      let dparts boff = List.map (dpart ?boff) (range 0 `To (c - 1)) in
      ListLabels.map pred_names
        ~f:(fun pred_name ->
          make_and
            (LPred (pred_name, dwhole 0 :: dparts None)) @@
            let i = "i" in
            let li = LVar i in
            LForall (i, why_integer_type, [],
                      let pred_app =
                        let imul = if c > 1 then LApp ("mul_int", [li; const_of_int c]) else li in
                        LPred (pred_name, dwhole ~boff:li 0 :: dparts (Some imul))
                      in
                      if false (* change to enbale the antecedent (both ways are correct) *) then
                        LImpl (make_and (LPred ("le_int", [omin; li])) @@ LPred ("le_int", [li; omax]),  pred_app)
                      else
                        pred_app))
    in
    LLet (p, e', LLet (ps, LApp ("downcast", [e'; LVar s_to]), make_and_list assumptions))
  in

  let cast_factor_assumption =
    let c =
      match op with
      | `Split c -> c
      | `Merge c -> -c
      | `Retain -> 1
    in
    LPred ("eq_int", [LApp (cast_factor_name, [LVar s_from; LVar s_to]); const_of_int c])
  in

  let assumption =
    mk_expr @@ Assert (`ASSUME, alloc_assumption,
      mk_expr @@ Assert (`ASSUME, memory_assumption,
        mk_expr @@ Assert (`ASSUME, cast_factor_assumption, void)))
  in
  append call_parameter assumption

and expr e =
  let infunction = get_current_function () in
  let e' = match e#node with
    | JCEconst JCCnull -> mk_var "null"
    | JCEconst c -> mk_expr (Cte(const c))
    | JCEvar v -> var v
    | JCEunary((`Uminus,(`Double|`Float as format)),e2) ->
        let e2' = expr e2 in
        if !Jc_options.float_model <> FMmultirounding then
          make_guarded_app
            ~mark:e#mark FPoverflow e#pos
            ("neg_" ^ float_format format)
            [ e2' ]
        else
          make_guarded_app
            ~mark:e#mark FPoverflow e#pos
 	    (float_operator `Uminus format)
 	    [current_rounding_mode () ; e2' ]

    | JCEunary(op,e1) ->
        let e1' = expr e1 in
        make_app (unary_op op)
          [ coerce ~check_int_overflow:(safety_checking())
              e#mark e#pos (native_operator_type op) e1#typ e1 e1' ]
(*     | JCEbinary(e1,(`Bsub,`Pointer),e2) -> *)
(*         let e1' = make_app "address" [ expr e1 ] in *)
(*         let e2' = make_app "address" [ expr e2 ] in *)
(* 	let st = pointer_struct e1#typ in *)
(* 	let s = string_of_int (struct_size_in_bytes st) in *)
(*         make_app *)
(* 	  (bin_op (`Bdiv,`Integer)) *)
(* 	  [ make_app (bin_op (`Bsub,`Integer)) [ e1'; e2' ]; *)
(* 	    Cte(Prim_int s) ] *)
    | JCEbinary(e1,(_,(`Pointer | `Logic) as op),e2) ->
        let e1' = expr e1 in
        let e2' = expr e2 in
        make_app (bin_op op) [e1'; e2']
    | JCEbinary(e1,(`Bland,_),e2) ->
        let e1' = expr e1 in
        let e2' = expr e2 in
        (* lazy conjunction *)
        mk_expr
          (And (make_check ~mark:e1#mark e1#pos e1', make_check ~mark:e2#mark e2#pos e2'))
    | JCEbinary(e1,(`Blor,_),e2) ->
        let e1' = expr e1 in
        let e2' = expr e2 in
        (* lazy disjunction *)
        mk_expr
          (Or (make_check ~mark:e1#mark e1#pos e1', make_check ~mark:e2#mark e2#pos e2'))
    | JCEbinary(e1,(#arithmetic_op as op,(`Double|`Float|`Binary80 as format)),e2) ->
	let e1' = expr e1 in
        let e2' = expr e2 in
        make_guarded_app
	  ~mark:e#mark FPoverflow e#pos
	  (float_operator op format)
	  [current_rounding_mode () ; e1' ; e2' ]
    | JCEbinary(e1,(_,#native_operator_type as op),e2) ->
        let e1' = expr e1 in
        let e2' = expr e2 in
        let ty = native_operator_type op in
        let mk = match fst op with
          | `Bdiv | `Bmod -> make_guarded_app ~mark:e#mark DivByZero e#pos
          | _ -> make_app ?ty:None
	in
        mk (bin_op op)
          [coerce ~check_int_overflow:(safety_checking())
             e1#mark e1#pos ty e1#typ e1 e1';
           coerce ~check_int_overflow:(safety_checking())
             e2#mark e2#pos ty e2#typ e2 e2']
    | JCEshift(e1,e2) ->
	(* TODO: bitwise !!!!!!!!!!!!!!!!!!!!! *)
        let e1' = expr e1 in
        let e2' = expr e2 in
        make_app "shift"
          [e1';
	   coerce ~check_int_overflow:(safety_checking())
             e2#mark e2#pos integer_type e2#typ e2 e2']
    | JCEif(e1,e2,e3) ->
        let e1' = expr e1 in
        let e2' = expr e2 in
        let e3' = expr e3 in
        mk_expr (If(make_check ~mark:e1#mark e1#pos e1',e2',e3'))
    | JCEoffset(k,e1,st) ->
	let ac = deref_alloc_class ~type_safe:false e1 in
        let alloc = alloc_table_var (ac,e1#region) in
	begin match ac with
	  | JCalloc_root _ ->
              let f = match k with
		| Offset_min -> "offset_min"
		| Offset_max -> "offset_max"
              in
	      make_app f [alloc; expr e1]
	  | JCalloc_bitvector ->
              let f = match k with
		| Offset_min -> "offset_min_bytes"
		| Offset_max -> "offset_max_bytes"
              in
	      let s = string_of_int (struct_size_in_bytes st) in
	      make_app f [alloc; expr e1; mk_expr (Cte(Prim_int s))]
	end
    | JCEaddress(Addr_absolute,e1) ->
        make_app "absolute_address" [ expr e1 ]
    | JCEaddress(Addr_pointer,e1) ->
        make_app "address" [ expr e1 ]
    | JCEbase_block(e1) ->
        make_app "base_block" [ expr e1 ]
    | JCEfresh _ -> assert false
    | JCEinstanceof (e1, st) ->
      let e1' = expr e1 in
      (* always safe *)
      make_app "instanceof_" [e1'; mk_var (tag_name st)]
    | JCEcast (e1, st) ->
      if struct_of_union st
      then expr e1
      else
        let e1' = expr e1 in
        make_app "downcast_" [e1'; mk_var (tag_name st)]
    | JCEbitwise_cast(e1,_st) ->
	expr e1
    | JCErange_cast(e1, ri) ->
        let e1' = expr e1 in
        let to_type = Option_misc.map_default (fun e -> JCTenum e) (JCTnative Tinteger) ri in
        coerce ~check_int_overflow:(safety_checking())
          e#mark e#pos to_type e1#typ e1 e1'
    | JCEreal_cast(e1,rc) ->
        let e1' = expr e1 in
        begin match rc with
          | Integer_to_real ->
              coerce ~check_int_overflow:(safety_checking())
                e#mark e#pos real_type e1#typ e1 e1'
          | Double_to_real ->
              coerce ~check_int_overflow:(safety_checking())
                e#mark e#pos real_type e1#typ e1 e1'
	  | Float_to_real ->
              coerce ~check_int_overflow:(safety_checking())
                e#mark e#pos real_type e1#typ e1 e1'
          | Round(f,_rm) ->
              coerce ~check_int_overflow:(safety_checking()
					    (* no safe version in the full model*)
	      || not (float_model_has_safe_functions ()))
                e#mark e#pos (JCTnative (Tgenfloat f)) e1#typ e1 e1'
        end
    | JCEderef(e1,fi) ->
  	make_deref e#mark e#pos e1 fi
    | JCEalloc(e1,st) ->
        let e1' = expr e1 in
        let ac = deref_alloc_class ~type_safe:false e in
        let alloc = plain_alloc_table_var (ac, e#region) in
        let pc = JCtag(st,[]) in
        if !Jc_options.inv_sem = InvOwnership then
          let tag = plain_tag_table_var (struct_root st, e#region) in
          let mut = mutable_name pc in
          let com = committed_name pc in
          make_app "alloc_parameter_ownership"
            [alloc; mk_var mut; mk_var com; tag; mk_var (tag_name st);
             coerce ~check_int_overflow:(safety_checking())
               e1#mark e1#pos integer_type
               e1#typ e1 e1']
        else
          let args = alloc_arguments (ac, e#region) pc in
          (match e1#node with
           | JCEconst JCCinteger s
             when (try let n = int_of_string s in n == 1 with Failure "int_of_string" -> false) ->
             make_app (alloc_param_name ~arg:Singleton ac pc) args
           | _ ->
             make_guarded_app e#mark
               AllocSize e#pos
               (alloc_param_name ~arg:Range_0_n ~check_size:(safety_checking()) ac pc)
               (coerce ~check_int_overflow:(safety_checking())
                 e1#mark e1#pos integer_type
                 e1#typ e1 e1'
               :: args))

    | JCEfree e1 ->
	let e1' = expr e1 in
	let ac = deref_alloc_class ~type_safe:false e1 in
        let alloc = plain_alloc_table_var (ac,e1#region) in
        if !Jc_options.inv_sem = InvOwnership then
	  let pc = pointer_class e1#typ in
	  let com = committed_name pc in
	  make_app "free_parameter_ownership"
	    [alloc; mk_var com; e1']
        else
	  let free_fun =
	    if safety_checking () then "free_parameter"
	    else "safe_free_parameter"
	  in
	  make_app free_fun [alloc; e1']

    | JCEreinterpret (e, st) -> make_reinterpret e st

    | JCEapp call ->
	begin match call.call_fun with
          | JClogic_fun f ->
              let arg_types_asserts, args =
		try match f.li_parameters with
		  | [] -> [], []
		  | params ->
(*
		      let param_types =
			List.map (fun v -> v.vi_type) params
		      in
*)
		      List.fold_right2 list_type_assert
			params call.call_args ([],[])
		with Invalid_argument _ -> assert false
              in
	      let param_assoc =
		List.map2 (fun param arg -> param,arg)
		  f.li_parameters call.call_args
	      in
	      let with_body =
		try
                  let _f,body =
		    IntHashtblIter.find 
                      Jc_typing.logic_functions_table
		      f.li_tag
		  in
		  match body with
		    | JCTerm _ -> true
		    | JCNone | JCReads _ -> false
		    | JCAssertion _ | JCInductive _ -> assert false
                with Not_found -> false
	      in
	      let pre, fname, locals, prolog, epilog, args =
		make_arguments
                  ~callee_reads: f.li_effects
                  ~callee_writes: empty_effects
                  ~region_assoc: call.call_region_assoc
		  ~param_assoc ~with_globals:true ~with_body
		  f.li_final_name args
	      in
	      assert (pre = LTrue);
	      assert (fname = f.li_final_name);
              let call = make_logic_app fname args in
              let new_arg_types_assert =
		List.fold_right
		  (fun opt acc ->
		     match opt with
                       | (_tmp,_e,a) -> make_and a acc)
		  arg_types_asserts LTrue
              in
              let call =
		if new_arg_types_assert = LTrue || not (safety_checking()) then
		  call
		else
		  mk_expr (Assert(`ASSERT,new_arg_types_assert,call))
              in
              let call =
		List.fold_right
		  (fun opt c ->
		     match opt with
                       | (tmp,e,_ass) -> mk_expr (Let(tmp,e,c)))
		  arg_types_asserts call
              in
	      let call = append prolog call in
	      let call =
		if epilog.expr_node = Void then call else
		  let tmp = tmp_var_name () in
		  mk_expr (Let(tmp,call,append epilog (mk_var tmp)))
	      in
              define_locals ~writes:locals call

          | JCfun f ->

              let arg_types_asserts, args =
		try match f.fun_parameters with
		  | [] -> [], []
		  | params ->
		      let params =
			List.map (fun (_,v) -> v) params
		      in
		      List.fold_right2 list_type_assert
			params call.call_args ([],[])
		with Invalid_argument _ -> assert false
              in
	      let args =
		List.fold_right2
		  (fun e e' acc ->
		     let e' =
		       if is_pointer_type e#typ && Region.bitwise e#region then
			 let st = pointer_struct e#typ in
			 let vi = struct_root st in
			 make_app (of_pointer_address_name vi) [ e' ]
		       else e'
		     in
		     e' :: acc
		  ) call.call_args args []
	      in
	      let param_assoc =
		List.map2 (fun (_,param) arg -> param,arg)
		  f.fun_parameters call.call_args
	      in
	      let fname =
		if safety_checking () then
		  f.fun_final_name ^ "_requires"
		else f.fun_final_name
	      in
	      let with_body =
		try
		  let _f,_loc,_s,body =
                    IntHashtblIter.find 
                      Jc_typing.functions_table f.fun_tag
		  in
		  body <> None
                with Not_found ->
                  (*
                    eprintf "Fatal error: tag for %s not found@." f.fun_name;
                    assert false
                  *)
                  false
	      in
	      let args =
		match f.fun_builtin_treatment with
		  | TreatNothing -> args
		  | TreatGenFloat format ->
		      (mk_var (float_format format))::(current_rounding_mode ())::args
	      in
	      let pre, fname, locals, prolog, epilog, new_args =
		make_arguments
                  ~callee_reads: f.fun_effects.fe_reads
                  ~callee_writes: f.fun_effects.fe_writes
                  ~region_assoc: call.call_region_assoc
		  ~param_assoc ~with_globals:false ~with_body
		  fname args
	      in
	      let call = make_guarded_app e#mark UserCall e#pos fname new_args in
	      let call =
		if is_pointer_type e#typ && Region.bitwise e#region then
		  make_app "pointer_address" [ call ]
		else call
	      in
	      (* decreases *)

	      let this_comp = f.fun_component in
	      let current_comp = (get_current_function()).fun_component in
	      let call =
		if safety_checking() && this_comp = current_comp then
                  try
		  let cur_measure,cur_r = get_measure_for (get_current_function()) in
                  let cur_measure_why =
                    term ~type_safe:true ~global_assertion:true
                      ~relocate:false LabelPre LabelPre cur_measure
                  in
		  let this_measure,this_r = get_measure_for f in
                  let subst =
                    List.fold_left2
                      (fun acc (_,vi) (tmp,_,_) ->
(*
                         Format.eprintf "subst: %s -> %s@."
                           vi.vi_name tmp;
*)
                         VarMap.add vi (LVar tmp) acc)
                      VarMap.empty f.fun_parameters arg_types_asserts
                  in
                  let this_measure_why =
                    term ~subst ~type_safe:true ~global_assertion:true
                      ~relocate:false LabelHere LabelHere this_measure
                  in
		  let r,ty =
		    assert (this_r = cur_r);
		    match this_r with
		      | None -> "zwf_zero", integer_type
		      | Some li ->
                          match li.li_parameters with
                              v1::_ -> li.li_name,v1.vi_type
                            | _ -> assert false
		  in
                  let this_measure_why =
                    term_coerce
                      ~type_safe:false ~global_assertion:false
                      LabelHere this_measure#pos ty this_measure#typ this_measure this_measure_why
                  in
                  let cur_measure_why =
                    term_coerce
                      ~type_safe:false ~global_assertion:false
                      LabelHere cur_measure#pos ty cur_measure#typ cur_measure cur_measure_why
                  in
		  let pre =
		    LPred(r,[this_measure_why;cur_measure_why])
		  in
		  make_check ~mark:e#mark ~kind:VarDecr e#pos
                    (* Francois mardi 29 juin 2010 : `ASSERT -> `CHECK
                       if this_measure_why = 0 and cur_measure_why = 0 then this assert is not
                       false (0>0) so all the remaining goal are trivial. *)
                    (mk_expr (Assert(`CHECK,pre,call)))
                  with Exit -> call
		else call
	      in
	      (* separation assertions *)
	      let call =
		if pre = LTrue || not (safety_checking()) then
		  call
		else
		  make_check ~mark:e#mark (* ~kind:Separation *) e#pos
		    (mk_expr (Assert(`ASSERT,pre,call)))
	      in
              let arg_types_assert =
		List.fold_right
		  (fun opt acc ->
		     match opt with
                       | (_tmp,_e,a) -> make_and a acc)
		  arg_types_asserts LTrue
              in
              let call =
		if arg_types_assert = LTrue || not (safety_checking()) then
		  call
		else
		  make_check ~mark:e#mark ~kind:IndexBounds e#pos
		    (mk_expr (Assert(`ASSERT,arg_types_assert,call)))
              in
              let call =
		List.fold_right
		  (fun opt c ->
		     match opt with
                       | (tmp,e,_ass) -> mk_expr (Let(tmp,e,c)))
		  arg_types_asserts call
              in
	      let call = append prolog call in
	      let call =
		if epilog.expr_node = Void then call else
		  let tmp = tmp_var_name () in
		  mk_expr (Let(tmp,call,append epilog (mk_var tmp)))
	      in
              define_locals ~writes:locals call
	end
    | JCEassign_var(v,e1) ->
(*
        begin
          match e#mark with
            | "" -> ()
            | l -> Format.eprintf "met assign_var with label %s@." l
        end;
*)
	let e1' = value_assigned e#mark e#pos v.vi_type e1 in
	let e' = mk_expr (Assign(v.vi_final_name,e1')) in
	if e#typ = Jc_pervasives.unit_type then
          begin
(*
            eprintf "JCEassign(%s,..) : has type unit@." v.vi_name;
*)
            e'
          end
        else
          begin
(*
            eprintf "JCEassign(%s,..) : DOES NOT have type unit@." v.vi_name;
*)
            append e' (var v)
          end
    | JCEassign_heap(e1,fi,e2) ->
	let e2' = value_assigned e#mark e#pos fi.fi_type e2 in
	(* Define temporary variable for value assigned *)
	let tmp2 = tmp_var_name () in
(*
        eprintf "JCEassign_heap: tmp_var_name for tmp2 is %s@." tmp2;
*)
	let v2 = Jc_pervasives.var fi.fi_type tmp2 in
	let e2 =
	  new expr_with ~typ:fi.fi_type ~node:(JCEvar v2) e2
	in
	(* Translate assignment *)
        let tmp1, lets, e' = make_upd e#mark e#pos e1 fi e2 in
        let e' =
	  if (safety_checking()) && !Jc_options.inv_sem = InvOwnership then
            append (assert_mutable (LVar tmp1) fi) e'
	  else e'
	in
	let lets = (tmp2,e2') :: lets in
        let e' =
          if e#typ = Jc_pervasives.unit_type then
	    match e'.expr_node with
              | MultiAssign(m,p,lets',isrefa,ta,a,tmpe,e,f,l) ->
(*
                eprintf "multiassign for a unit type !@.";
                eprintf "length lets = %d, length lets' = %d@."
                  (List.length lets) (List.length lets');
*)
                  { e' with expr_node =
                      MultiAssign(m,p,lets@lets',isrefa,ta,a,tmpe,e,f,l)}
              | _ ->
                  make_lets lets e'
          else
            begin
(*
              eprintf "multiassign but not a unit type !@.";
*)
              make_lets lets (append e' (mk_var tmp2))
            end
        in
        if !Jc_options.inv_sem = InvOwnership then
          append e' (assume_field_invariants fi)
        else e'

    | JCEblock el ->
        List.fold_right append (List.map expr el) void
    | JCElet(v,e1,e2) ->
        let e1' = match e1 with
          | None ->
              any_value v.vi_region v.vi_type
          | Some e1 ->
	      value_assigned e#mark e#pos v.vi_type e1
	in
	let e2' = expr e2 in
        if v.vi_assigned then
	  mk_expr (Let_ref(v.vi_final_name,e1',e2'))
        else
	  mk_expr (Let(v.vi_final_name,e1',e2'))
    | JCEreturn_void -> mk_expr (Raise(jessie_return_exception,None))
    | JCEreturn(ty,e1) ->
	let e1' = value_assigned e#mark e#pos ty e1 in
	let e' = mk_expr (Assign(jessie_return_variable,e1')) in
	append e' (mk_expr (Raise(jessie_return_exception,None)))
    | JCEunpack(st,e1,as_st) ->
        let e1' = expr e1 in
        make_guarded_app e#mark Unpack e#pos
          (unpack_name st) [ e1'; mk_var (tag_name as_st) ]
    | JCEpack(st,e1,from_st) ->
        let e1' = expr e1 in
        make_guarded_app e#mark Pack e#pos
          (pack_name st) [ e1'; mk_var (tag_name from_st) ]
    | JCEassert(b,asrt,a) ->
(*
        Format.eprintf "assertion meet, kind %a for behaviors: %a@."
          Jc_output_misc.asrt_kind asrt
          (print_list comma Jc_output.identifier) b;
*)
	let a' =
	  named_assertion
	    ~type_safe:false ~global_assertion:false ~relocate:false
	    LabelHere LabelPre a
	in
(*
        Format.eprintf "assertion to check ?@.";
*)
	begin match asrt with
	  | Aassert | Ahint ->
	      if in_current_behavior b then
		mk_expr (Assert(`ASSERT,a',void))
	      else if in_default_behavior b then
		assumption [ a ] a'
              else
                void
	  | Aassume ->
	      if in_current_behavior b || in_default_behavior b then
		assumption [ a ] a'
	      else void
          | Acheck ->
(*
              (match b with
                 | [] -> Format.eprintf "check for no behavior@."
                 | b::_ -> Format.eprintf "check for behavior %s,...@." b#name);
*)
              if in_current_behavior b then
		mk_expr (Assert(`CHECK,a',void))
	      else void
	end
    | JCEloop(la,e1) ->
	let inv,assume_from_inv =
	  List.fold_left
	    (fun ((invariants,assumes) as acc) (names,inv,_) ->
	       match inv with
		 | Some i ->
		     if in_current_behavior names
		     then (i::invariants,assumes)
		     else
		       if List.exists
			 (fun behav -> behav#name = "default")
			 names
		       then
			 (invariants,i::assumes)
		       else
			 (invariants,assumes)
		 | None -> acc)
	    ([],[])
	    la.loop_behaviors
	in
        let inv' =
	  make_and_list
	    (List.map
	       (named_assertion
		  ~type_safe:false ~global_assertion:false ~relocate:false
		  LabelHere LabelPre) inv)
	in
        let assume_from_inv' =
	  make_and_list
	    (List.map
	       (named_assertion
		  ~type_safe:false ~global_assertion:false ~relocate:false
		  LabelHere LabelPre) assume_from_inv)
	in
	(* free invariant: trusted or not *)
	let free_inv = la.loop_free_invariant in
        let free_inv' =
	  named_assertion
	    ~type_safe:false ~global_assertion:false ~relocate:false
	    LabelHere LabelPre free_inv
        in
        let inv' =
	  if Jc_options.trust_ai then inv' else make_and inv' free_inv'
	in
	(* loop assigns

	   By default, the assigns clause for the function should be
	   taken

	   Yannick: wrong, as function's assigns clause does not deal
	   with newly allocated memory, nor local variables, which may
	   be assigned in the loop.

	   Claude: it is not wrong if we take care: the implicit loop
	   assigns generated from the function's assigns should relate
	   the state Pre (for the function) and current state. Whereas an
	   explicit loop assigns relates the state before entering the
	   loop and the current state. example:


	   int t[10];
	   //@ assigns t[0..9]
	   f() { int i;
	   int u[] = new int [10];
	   //@ loop assigns t[0..i], u[0..i]
	   for (i=0; i < 10; i++) {
	   t[i] = ...; u[i] = ...
	   }

	   the Why code should be

	   f() { let i = ref any_int() in
	   let u = alloc_array(10) // writes alloc
	   in
	   loop_init:
	   i := 0;
	   while (!i < 10) do
	     invariant
	        // from loop assigns
	        assigns(alloc@loop_init,intP@loop_init,intP,
	                    t[0..i] union u[0..i])
	        and
	        // from function's assigns
	        assigns(alloc@,intP@,intP, t[0..9])
	     intP := store(intP,t+!i,...);
	     intP := store(intP,u+!i,...);
	     i := !i + 1;
	   done;

	*)


	(* loop assigns from function's loop assigns *)

	let loop_assigns_from_function =
	  let s = get_current_spec () in
	  List.fold_left
	    (fun acc (_pos,id,b) ->
	       if is_current_behavior id then
		 match b.b_assigns with
		   | None -> acc
		   | Some(_pos,loclist) ->
		       let loclist = List.map old_to_pre_loc loclist in
		       match acc with
			 | None -> Some loclist
			 | Some loclist' -> Some (loclist @ loclist')
	       else acc
	    ) None (s.fs_default_behavior::s.fs_behavior)
	in

	(* This is the code producing the Why invariant from the user's loop assigns

   a loop assigns for behavior b should be

   - taken as an invariant if current behavior is b

   - taken as an assumption at loop entrance if current behavior is not b
     and b is "default"

     WARNING: this is UNSOUND if the defautl behavior has an assumes clause!!!
       -> temporarily disabled

   - otherwise ignored

*)


	let loop_assigns =
	  List.fold_left
	    (fun acc (names,_inv,ass) ->
	       match ass with
		 | Some i ->
		     if in_current_behavior names
		     then
		       match acc with
			 | None -> Some i
			 | Some l -> Some (i@l)
		     else
		       (*
			 if List.exists
			 (fun behav -> behav#name = "default")
			 names
			 then
			 (invariants,i::assumes)
		       else
			 (invariants,assumes)
		       *)
		       acc
		 | None -> acc)
	    None
	    la.loop_behaviors
	in

	let loop_label = fresh_loop_label() in

	let ass =
	  tr_assigns ~type_safe:false
	    (LabelName loop_label) infunction.fun_effects loop_assigns
	    e#pos
	in

	let ass_from_fun =
	  tr_assigns ~type_safe:false
	    LabelPre infunction.fun_effects loop_assigns_from_function
	    e#pos
	in

        let inv' =
	  make_and inv' (make_and (mark_assertion e#pos ass)
			   (mark_assertion e#pos ass_from_fun))
	in
	(* loop body *)
        let body = expr e1 in
	let add_assume s =
          let s = append (assumption assume_from_inv assume_from_inv') s in
          if Jc_options.trust_ai then
            append (assumption [ free_inv ] free_inv') s
          else s
        in
	let body = [ add_assume body ] in
	(* loop variant *)
	let loop_variant =
          match la.loop_variant with
            | Some (t,r) when variant_checking () &&
                !Jc_options.termination_policy <> TPnever ->
		let variant =
		  named_term
		    ~type_safe:false ~global_assertion:false ~relocate:false
		    LabelHere LabelPre t
	        in
                let variant,r = match r with
                  | None ->
		      term_coerce
                        ~type_safe:false ~global_assertion:false
                        LabelHere t#pos integer_type t#typ t variant, None
                  | Some id -> variant, Some id.li_name
                in
                Some (variant,r)
            | None when variant_checking () &&
                !Jc_options.termination_policy = TPalways ->
                eprintf
                  "Warning, generating a dummy variant for loop. \
                   Please provide a real variant or set termination policy \
                   to user or never\n%!";
                Some (LConst(Prim_int "0"),None)
            | _ -> None
        in
(*
        eprintf "Jc_interp.expr: adding loop label %s@." loop_label.lab_final_name;
*)
        make_label loop_label.lab_final_name
	  (mk_expr (While((mk_expr (Cte(Prim_bool true)),
                           inv', loop_variant, body))))

    | JCEcontract(req,dec,vi_result,behs,e) ->
	let r =
          match req with
            | Some a ->
                assertion
	          ~type_safe:false ~global_assertion:false ~relocate:false
	          LabelHere LabelPre a
            | _ -> LTrue
        in
        assert (dec = None);
        let ef = Jc_effect.expr Jc_pervasives.empty_fun_effect e in
	begin match behs with
	  | [_pos,id,b] ->
	      assert (b.b_throws = None);
	      assert (b.b_assumes = None);
	      let a =
		assertion
		  ~type_safe:false ~global_assertion:false ~relocate:false
		  LabelHere LabelPre b.b_ensures
	      in
              let post = match b.b_assigns with
                | None -> a
                | Some(_,locs) ->
                    make_and a
	              (tr_assigns ~type_safe:false
	                 LabelPre
                         ef (* infunction.fun_effects*) (Some locs)
	                 e#pos)
              in
              if safety_checking () then
                begin
                  let tmp = tmp_var_name () in
                  mk_expr (Let(tmp,
                               mk_expr (Triple(true,r,expr e,LTrue,[])),
                               append
                                 (mk_expr
                                    (BlackBox(Annot_type(LTrue,unit_type,[],[],post,[]))))
                                 (mk_expr (Var tmp))))
                end
              else if is_current_behavior id then
                if r = LTrue
                then
                  mk_expr (Triple(true,LTrue,expr e,post,[]))
                else
                  append
                    (mk_expr (BlackBox(Annot_type(LTrue,unit_type,[],[],r,[]))))
                    (mk_expr (Triple(true,LTrue,expr e,post,[])))
              else
(*
                let reads = read_effects
                  ~callee_reads:ef.fe_reads
                  ~callee_writes:ef.fe_writes ~params:[] ~region_list:[]
                in
                let _writes = write_effects
                  ~callee_reads:ef.fe_reads
                  ~callee_writes:ef.fe_writes ~params:[] ~region_list:[]
                in
*)
                append
                  (mk_expr (BlackBox(Annot_type(LTrue,unit_type,[],[],r,[]))))
                  (*
                  (mk_expr (BlackBox(Annot_type(LTrue, tr_var_type vi_result,reads, writes, post, []))))
                  *)
                  (let tmp = tmp_var_name () in
                   mk_expr (Let(tmp,
                                (mk_expr (Triple(true,LTrue,expr e,LTrue,[]))),
                                (mk_expr (BlackBox(Annot_type(LTrue, tr_var_type vi_result,[], [], post, [])))))))
	  | _ -> assert false
	end
    | JCEthrow(exc,Some e1) ->
        let e1' = expr e1 in
        mk_expr (Raise(exception_name exc,Some e1'))
    | JCEthrow(exc, None) ->
        mk_expr (Raise(exception_name exc,None))
    | JCEtry (s, catches, _finally) ->
(*      assert (finally.jc_statement_node = JCEblock []); (\* TODO *\) *)
        let catch (s,excs) (ei,v_opt,st) =
          if ExceptionSet.mem ei excs then
            (mk_expr (Try(s,
                 exception_name ei,
                 Option_misc.map (fun v -> v.vi_final_name) v_opt,
                 expr st)),
             ExceptionSet.remove ei excs)
          else
            begin
(* YMo: too many questions about warning due to generated Jessie *)
(*               eprintf "Warning: exception %s cannot be thrown@." *)
(*                 ei.exi_name; *)
              (s,excs)
            end
        in
        let ef = Jc_effect.expr empty_fun_effect s in
        let (s,_) =
          List.fold_left catch (expr s,ef.fe_raises) catches
        in s
    | JCEmatch (e, psl) ->
        let tmp = tmp_var_name () in
        let body = pattern_list_expr expr (LVar tmp) e#region
          e#typ psl in
        mk_expr (Let(tmp, expr e, body))
  in
  let e' =
    (* Ideally, only labels used in logical annotations should be kept *)
    let lab = e#mark in
    if lab = "" then e' else
      begin
        match e' with
            (*
              | MultiAssign _ -> assert false
            *)
          | _ ->
(*
              if lab = "L2" then eprintf "Jc_interp.expr: adding label %s to expr %a@." lab Output.fprintf_expr e';
*)
              make_label e#mark e'
      end
  in
  let e' =
    if e#typ = Jc_pervasives.unit_type then
      if match e#original_type with
        | JCTany | JCTnative Tunit -> false
        | _ -> true
      then
        match e'.expr_node with
          | MultiAssign _ -> e'
          | _ ->
	      (* Create dummy temporary *)
	      let tmp = tmp_var_name () in
	      mk_expr (Let(tmp,e',void))
      else e'
    else
      match e'.expr_node with
        | MultiAssign _ -> assert false
        | _ -> e'
  in
(*
  begin
    match e' with
      | MultiAssign _ -> eprintf "Jc_interp.expr produces MultiAssign@.";
      | _ -> ()
  end;
*)
  e'



(*****

finalization: removing MultiAssign expressions

***)

let make_old_style_update ~mark ~pos alloc tmpp tmpshift mem i b1 b2 tmp2 =
  if safety_checking() then
    match b1,b2 with
      | true,true ->
          make_app "safe_upd_" [ mk_var mem; mk_var tmpshift; mk_var tmp2 ]
      | true,false ->
          make_guarded_app ~mark IndexBounds pos "lsafe_lbound_upd_"
            [ alloc; mk_var mem; mk_var tmpp; mk_expr (Cte i); mk_var tmp2 ]
      | false,true ->
          make_guarded_app ~mark IndexBounds pos "rsafe_rbound_upd_"
            [ alloc; mk_var mem; mk_var tmpp; mk_expr (Cte i); mk_var tmp2 ]
      | false,false ->
          make_guarded_app ~mark PointerDeref pos "upd_"
            [ alloc; mk_var mem ; mk_var tmpshift; mk_var tmp2 ]
  else
    make_app "safe_upd_" [ mk_var mem; mk_var tmpshift; mk_var tmp2 ]

let make_old_style_update_no_shift ~mark ~pos alloc tmpp mem b1 b2 tmp2 =
  if safety_checking() then
    match b1,b2 with
      | true,true ->
          make_app "safe_upd_" [ mk_var mem; mk_var tmpp; mk_var tmp2 ]
      | true,false ->
          make_guarded_app ~mark IndexBounds pos "lsafe_lbound_upd_"
            [ alloc; mk_var mem; mk_var tmpp; mk_expr (Cte (Prim_int "0")); mk_var tmp2 ]
      | false,true ->
          make_guarded_app ~mark IndexBounds pos "rsafe_rbound_upd_"
            [ alloc; mk_var mem; mk_var tmpp; mk_expr (Cte (Prim_int "0")); mk_var tmp2 ]
      | false,false ->
          make_guarded_app ~mark PointerDeref pos "upd_"
            [ alloc; mk_var mem ; mk_var tmpp; mk_var tmp2 ]
  else
    make_app "safe_upd_" [ mk_var mem; mk_var tmpp; mk_var tmp2 ]

let make_not_assigns talloc mem t l =
  let l = List.map (fun (i,_,_,_) -> i) l in
  let l = List.sort Pervasives.compare l in
  let rec merge l acc =
    match l,acc with
      | [],_ -> acc
      | i::r, [] -> merge r [(i,i)]
      | i::r, (a,b)::acc' ->
          if i=b+1 then merge r ((a,i)::acc')
          else merge r ((i,i)::acc)
  in
  let i,l = match merge l []
  with [] -> assert false
    | i::l -> i,l
  in
  let pset_of_interval (a,b) =
    if a=b then LApp("pset_singleton",[
                       LApp("shift",[LVar t;
                                     LConst (Prim_int (string_of_int a))])])
    else LApp("pset_range",[
                LApp("pset_singleton", [LVar t]);
                LConst(Prim_int (string_of_int a));
                LConst(Prim_int (string_of_int b))])
  in
  let pset = List.fold_left
    (fun acc i ->
       LApp("pset_union",[pset_of_interval i; acc]))
    (pset_of_interval i)
    l
  in
  LPred("not_assigns",[talloc;LDerefAtLabel(mem,"") ; LDeref mem ; pset])

(*****************************)
(* axioms, lemmas, goals     *)
(*****************************)

let tr_axiom loc id ~is_axiom labels a acc =

  if Jc_options.debug then
    Format.printf "[interp] axiom %s@." id;

  let lab = match labels with [lab] -> lab | _ -> LabelHere in
  (* Special (local) translation of effects for predicates with polymorphic memories.
     We first entirely exclude their effects from the assertion, then only restore the effects that
     are relevant in this axiom. So the effects from other axioms won't be translated. *)
  let ef = Jc_effect.assertion empty_effects (restrict_poly_mems_in_assertion MemoryMap.empty a) in
  let a' =
    assertion ~type_safe:false ~global_assertion:true ~relocate:false lab lab @@
      restrict_poly_mems_in_assertion ef.e_memories a
  in
  let params = tmodel_parameters ~label_in_name:true ef in
  let new_id = get_unique_name id in
  reg_decl
    ~out_mark:new_id
    ~in_mark:id
    ~name:id
    ~beh:(if is_axiom then "axiom" else "lemma")
    loc;
  let a' =
    List.fold_right (fun (n,_v,ty') a' -> LForall(n,ty',[],a')) params a'
  in
  Goal((if is_axiom then KAxiom else KLemma),
       {Output.name = new_id; loc = Loc.extract loc},a') :: acc




(***********************************)
(*             axiomatic decls     *)
(***********************************)


let tr_axiomatic_decl acc d =
  match d with
    | Jc_typing.ABaxiom(loc,id,labels,p) ->
	tr_axiom loc ~is_axiom:true id labels p acc

(******************************************************************************)
(*                                 Functions                                  *)
(******************************************************************************)

let excep_posts_for_others exc_opt excep_behaviors =
  ExceptionMap.fold
    (fun exc _bl acc ->
       match exc_opt with
         | Some exc' ->
	     if exc.exi_tag = exc'.exi_tag then
	       acc
	     else
	       (exception_name exc, LTrue) :: acc
         | None -> (exception_name exc, LTrue) :: acc
    ) excep_behaviors []

let fun_parameters ~type_safe params write_params read_params =
  let write_params =
    List.map (fun (n,ty') -> (n,Ref_type(Base_type ty'))) write_params
  in
  let read_params =
    List.map (fun (n,ty') -> (n,Base_type ty')) read_params
  in
  let params =
    List.map (fun v ->
		let n,ty' = param ~type_safe v in
		(n, Base_type ty')
	     ) params
  in
  let params = params @ write_params @ read_params in
  match params with
    | [] -> [ ("tt", unit_type) ]
    | _ -> params

let annot_fun_parameters params write_params read_params annot_type =
  let params = fun_parameters ~type_safe:true params write_params read_params in
  List.fold_right (fun (n,ty') acc -> Prod_type(n, ty', acc))
    params annot_type

let function_body _f spec behavior_name body =
  set_current_behavior behavior_name;
  set_current_spec spec;
  let e' = expr body in
  reset_current_behavior ();
  reset_current_spec ();
  e'

(* Only used for internal function, hence type-safe parameter set to false *)
let assume_in_precondition b pre =
  match b.b_assumes with
    | None -> pre
    | Some a ->
	let a' =
	  assertion ~type_safe:false ~global_assertion:false ~relocate:false
	    LabelHere LabelHere a
	in
	make_and a' pre

(* Only used for external prototype, hence type-safe parameter set to true *)
let assume_in_postcondition b post =
  match b.b_assumes with
    | None -> post
    | Some a ->
	let a' =
	  assertion ~type_safe:true ~global_assertion:false ~relocate:true
	    LabelOld LabelOld a
	in
	make_impl a' post

let function_prototypes = Hashtbl.create 7

let get_valid_pred_app ~in_param vi =
  match vi.vi_type with
    | JCTpointer (pc, n1o, n2o) ->
	(* TODO: what about bitwise? *)
	let v' =
          term ~type_safe:false ~global_assertion:false ~relocate:false
	    LabelHere LabelHere (new term_var vi)
	in
	  begin match n1o, n2o with
            | None, None -> LTrue
	    | Some n, None ->
		let ac = alloc_class_of_pointer_class pc in
                let a' =
		  make_valid_pred_app ~in_param ~equal:false
		    (ac, vi.vi_region) pc
                    v' (Some (const_of_num n)) None
                in
		  bind_pattern_lets a'
	    | None, Some n ->
		let ac = alloc_class_of_pointer_class pc in
                let a' =
		  make_valid_pred_app ~in_param ~equal:false
		    (ac, vi.vi_region) pc
                    v' None (Some (const_of_num n))
                in
		  bind_pattern_lets a'
            | Some n1, Some n2 ->
		let ac = alloc_class_of_pointer_class pc in
                let a' =
		  make_valid_pred_app  ~in_param ~equal:false (ac, vi.vi_region) pc
                    v' (Some (const_of_num n1)) (Some (const_of_num n2))
                in
		  bind_pattern_lets a'
	  end
    | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull | JCTany
    | JCTtype_var _ -> LTrue

let tr_allocates ~type_safe alloc_tables locs =
  let at_locs =
    List.map
      (fun loc -> alloc_table_name (lderef_alloc_class ~type_safe loc, loc#region), loc)
      locs
  in
  let alloc_same at =
    let at = alloc_table_name at in
    let args = [LDerefAtLabel (at, ""); LDeref at] in
    let to_pset = pset ~type_safe ~global_assertion:false LabelHere % location_set_all_of_location in
    match List.fold_left (fun acc (at', loc) -> if at = at' then loc :: acc else acc) [] at_locs with
      | [] -> LPred ("alloc_same_except", args @ [LVar "pset_empty"])
      | loc :: locs ->
          let pset =
            List.fold_left
              (fun acc loc -> LApp ("pset_union", [to_pset loc; acc]))
              (to_pset loc)
              locs
          in
          LPred ("alloc_same_except", args @ [pset])
  in
  AllocMap.fold (fun at _ acc -> make_and acc (alloc_same at)) alloc_tables LTrue

let pre_tr_fun f _funpos spec _body acc =
  begin
    match spec.fs_decreases with
      | None -> ()
      | Some(t,r) ->
	  Hashtbl.add decreases_clause_table f.fun_tag (t,r)
  end;
  acc


let tr_fun f funpos spec body acc =

  if Jc_options.debug then
    Format.printf "[interp] function %s@." f.fun_name;
  Jc_options.lprintf "Jc_interp: function %s@." f.fun_name;

  (* handle parameters that are assigned in the body *)

  let assigned_params =
    List.fold_left
      (fun acc (_,v) ->
         if v.vi_assigned then
           begin
             v.vi_assigned <- false;
             v :: acc
           end
         else
           acc)
      [] f.fun_parameters
  in

  (* global variables valid predicates *)
  let variables_valid_pred_apps = LTrue
(* Yannick: commented out because not taken into account in effects
    Hashtbl.fold
      (fun _ (vi, _) acc ->
         let req = get_valid_pred_app vi in
	   make_and req acc)
      Jc_typing.variables_table LTrue
*)
  in

  (* precondition for calling the function and extra one for analyzing it *)

  let external_requires =
    named_assertion ~type_safe:true ~global_assertion:false ~relocate:false
      LabelHere LabelHere spec.fs_requires
  in
  let external_requires =
    if Jc_options.trust_ai then
      external_requires
    else
      let free_requires =
	named_assertion ~type_safe:true ~global_assertion:false ~relocate:false
	  LabelHere LabelHere spec.fs_free_requires
      in
	make_and external_requires free_requires
  in

  let internal_requires =
    named_assertion ~type_safe:false ~global_assertion:false ~relocate:false
      LabelHere LabelHere spec.fs_requires
  in
  let free_requires =
    named_assertion ~type_safe:false ~global_assertion:false ~relocate:false
      LabelHere LabelHere spec.fs_free_requires
  in
  let free_requires = make_and variables_valid_pred_apps free_requires in
  let internal_requires = make_and internal_requires free_requires in
  let internal_requires =
    List.fold_left
      (fun acc (_,v) ->
         let req = get_valid_pred_app  ~in_param:true v in
	   make_and req acc)
      internal_requires f.fun_parameters
  in


  (* partition behaviors as follows:
     - (optional) 'safety' behavior (if Arguments Invariant Policy is selected)
     - (optional) 'inferred' behaviors (computed by analysis)
     - user defined behaviors *)

  let behaviors = spec.fs_default_behavior :: spec.fs_behavior in
  let (safety_behavior,
       normal_behaviors_inferred, normal_behaviors,
       excep_behaviors_inferred, excep_behaviors) =
    List.fold_left
      (fun (safety,normal_inferred,normal,excep_inferred,excep) (pos,id,b) ->
	 let make_post ~type_safe ~internal =
	   let post =
	     if internal && Jc_options.trust_ai then
	       b.b_ensures
	     else
	       Assertion.mkand [ b.b_ensures;
				 b.b_free_ensures ] ()
	   in
	   let post =
	     named_assertion
	       ~type_safe ~global_assertion:false ~relocate:false
	       LabelPost LabelOld post
	   in
           let post = match b.b_assigns with
             | None ->
		 Jc_options.lprintf
		   "Jc_interp: behavior '%s' has no assigns@." id;
		 post
             | Some(assigns_pos,loclist) ->
		 Jc_options.lprintf
		   "Jc_interp: behavior '%s' has assigns clause with %d elements@."
		   id (List.length loclist);
		 let assigns_post =
                   mark_assertion assigns_pos
                     (tr_assigns
                        ~type_safe
			~region_list:f.fun_param_regions
                        LabelOld
                        f.fun_effects
                        ~allocates:b.b_allocates
                        (Some loclist)
                        funpos)
		 in
		 mark_assertion pos (make_and post assigns_post)
	   in
           (* Add alloc_extends[except] predicates for those alloc tables modified by the function, i.e. *)
           (* listed in the f.fun_effects.fe_writes. *)
           (* We except psets of locations specified in the allocates clause i.e. b.b_allocates. *)
           (* IMPORTANT: We should add the predicates BOTH to the external and internal postconditions, *)
           (* otherwise safety might be violated. *)
           let post = match b.b_allocates with
               | None -> post
               | Some (pos', locs) ->
                   mark_assertion pos @@ make_and post @@ mark_assertion pos' @@
                     tr_allocates ~type_safe f.fun_effects.fe_writes.e_alloc_tables locs
           in
           post
	 in
	 let internal_post = make_post ~type_safe:false ~internal:true in
	 let external_post = make_post ~type_safe:true ~internal:false in
	 let behav = (id,b,internal_post,external_post) in
         match b.b_throws with
           | None ->
               begin match id with
                 | "safety" ->
		     assert (b.b_assumes = None);
		     let internal_post =
		       make_and variables_valid_pred_apps internal_post
		     in
		     let external_post =
		       make_and variables_valid_pred_apps external_post
		     in
                     (id, b, internal_post, external_post) :: safety,
                     normal_inferred, normal, excep_inferred, excep
                 | "inferred" ->
		     assert (b.b_assumes = None);
                     safety, behav :: normal_inferred,
                     (if Jc_options.trust_ai then normal else behav :: normal),
                     excep_inferred, excep
                 | _ ->
                     safety, normal_inferred, behav :: normal,
                     excep_inferred, excep
               end
           | Some exc ->
               if id = "inferred" then
		 begin
		   assert (b.b_assumes = None);
                   safety, normal_inferred, normal,
		   ExceptionMap.add_merge
		     List.append exc [behav] excep_inferred,
		   if Jc_options.trust_ai then excep else
                     ExceptionMap.add_merge List.append exc [behav] excep
		 end
               else
                 safety, normal_inferred, normal, excep_inferred,
                 ExceptionMap.add_merge List.append exc [behav] excep)
      ([], [], [], ExceptionMap.empty, ExceptionMap.empty)
      behaviors
  in
  let user_excep_behaviors = excep_behaviors in
  let excep_behaviors =
    ExceptionSet.fold
      (fun exc acc ->
         if ExceptionMap.mem exc acc then acc else
           let b =
             { default_behavior with
                 b_throws = Some exc;
		 b_ensures = (new assertion JCAtrue); }
           in
           ExceptionMap.add
	     exc [exc.exi_name ^ "_b", b, LTrue, LTrue] acc)
      f.fun_effects.fe_raises
      excep_behaviors
  in

  (* Effects, parameters and locals *)

  let params = List.map snd f.fun_parameters in

  let external_write_effects =
    write_effects
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
  in
  let external_read_effects =
    read_effects
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
  in
  let external_write_params =
    write_parameters
      ~type_safe:true
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
  in
  let internal_write_params =
    write_parameters
      ~type_safe:false
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
  in
  let external_read_params =
    read_parameters
      ~type_safe:true
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
      ~already_used:(List.map fst external_write_params)
  in
  let internal_read_params =
    read_parameters
      ~type_safe:false
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
      ~already_used:(List.map fst internal_write_params)
  in
  let internal_write_locals =
    write_locals
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
  in
  let internal_read_locals =
    read_locals
      ~callee_reads:f.fun_effects.fe_reads
      ~callee_writes:f.fun_effects.fe_writes
      ~region_list:f.fun_param_regions
      ~params
  in
  let define_locals e' =
    define_locals ~reads:internal_read_locals ~writes:internal_write_locals e'
  in

  (* Postcondition *)

  let add_modif_postcondition
      ~internal f (_id,b,internal_post,external_post) acc =
    let post = if internal then internal_post else external_post in
    make_and (f b post) acc
  in
  let add_postcondition ~internal =
    add_modif_postcondition ~internal (fun _b post -> post)
  in
  let internal_safety_post =
    List.fold_right (add_postcondition ~internal:true) safety_behavior LTrue
  in
  let external_safety_post =
    List.fold_right (add_postcondition ~internal:false) safety_behavior LTrue
  in
  let normal_post =
    List.fold_right
      (add_modif_postcondition ~internal:false assume_in_postcondition)
      normal_behaviors LTrue
  in
  let normal_post_inferred =
    List.fold_right (add_postcondition ~internal:false)
      normal_behaviors_inferred LTrue
  in
  let excep_posts =
    ExceptionMap.fold
      (fun exc bl acc ->
         let a' =
	   List.fold_right (add_postcondition ~internal:false) bl LTrue
	 in
         (exception_name exc, a') :: acc
      ) excep_behaviors []
  in
  let excep_posts_inferred =
    ExceptionMap.fold
      (fun exc bl acc ->
         let a' =
           List.fold_right
	     (add_modif_postcondition ~internal:false assume_in_postcondition)
	     bl LTrue
         in
	 (exception_name exc, a') :: acc
      ) excep_behaviors_inferred []
  in

  (* Function type *)

  let ret_type = tr_var_type f.fun_result in
  let fparams = List.map snd f.fun_parameters in
  let param_normal_post =
    if is_purely_exceptional_fun spec then LFalse else
      make_and_list [external_safety_post; normal_post; normal_post_inferred]
  in
  let param_excep_posts = excep_posts @ excep_posts_inferred in
  let acc =
    let annot_type = (* function declaration with precondition *)
      Annot_type(external_requires, ret_type,
                 external_read_effects, external_write_effects,
		 param_normal_post, param_excep_posts)
    in
    let fun_type =
      annot_fun_parameters fparams
	external_write_params external_read_params annot_type
    in
    let newid = f.fun_final_name ^ "_requires" in
    Hashtbl.add function_prototypes newid fun_type;
    Param(false, id_no_loc newid, fun_type) :: acc
  in
  let acc = (* function declaration without precondition *)
    let annot_type =
      Annot_type(LTrue, ret_type,
                 external_read_effects, external_write_effects,
		 param_normal_post, param_excep_posts)
    in
    let fun_type =
      annot_fun_parameters fparams
	external_write_params external_read_params annot_type
    in
    let newid = f.fun_final_name in
    Hashtbl.add function_prototypes newid fun_type;
    Param(false, id_no_loc newid, fun_type) :: acc
  in


  (* restore assigned status for parameters assigned in the body *)

  List.iter
    (fun v -> v.vi_assigned <- true)
    assigned_params;

  (* Function body *)

  match body with
    | None -> acc (* function was only declared *)
    | Some body ->
        if Jc_options.verify <> [] &&
          not (List.mem f.fun_name Jc_options.verify)
        then
          acc (* function is not in the list of functions to verify *)
        else
          let () =
	    printf "Generating Why function %s@." f.fun_final_name
	  in

	  (* parameters *)
	  let params =
	    fun_parameters ~type_safe:false fparams
	      internal_write_params internal_read_params
	  in

	  let wrap_body f spec bname body =
	    (* rename formals after parameters are computed and before body
	       is treated *)
	    let list_of_refs =
	      List.fold_right
		(fun id bl ->
		   if id.vi_assigned
		   then
		     let n = id.vi_final_name in
		     let newn = "mutable_" ^ n in
		     id.vi_final_name <- newn;
		     (newn, n) :: bl
		   else bl)
		fparams []
	    in
            let body = function_body f spec bname body in
	    let body =
	      if !Jc_options.inv_sem = InvOwnership then
		append (assume_all_invariants fparams) body
	      else body
	    in
	    let body = define_locals body in
	    let body = match f.fun_result.vi_type with
	      | JCTnative Tunit ->
		  mk_expr (Try(append body (mk_expr (Raise(jessie_return_exception,None))),
		               jessie_return_exception, None, void))
	      | _ ->
                  let result = f.fun_result in
		  let e' = any_value
                    result.vi_region result.vi_type in
		  mk_expr (Let_ref(jessie_return_variable, e',
			           mk_expr (Try(append body (mk_expr Absurd),
			                        jessie_return_exception, None,
			                        mk_expr (Deref jessie_return_variable)))))
	    in
	    let body = make_label "init" body in
	    let body =
	      List.fold_right
		(fun (mut_id,id) e' ->
                   mk_expr (Let_ref(mut_id, plain_var id, e')))
		list_of_refs body
	    in
	    (* FS#393: restore parameter real names *)
	    List.iter
	      (fun v ->
		 let n = v.vi_final_name in
		 if List.mem_assoc n list_of_refs then
		   v.vi_final_name <- List.assoc n list_of_refs
	      ) fparams;
	    body
	  in

          (* safety behavior *)
	  let acc =
	    if Jc_options.verify_behavior "safety" ||
               Jc_options.verify_behavior "variant" then
              let behav = if Jc_options.verify_behavior "safety"
                then "safety" else "variant" in
              let safety_body = wrap_body f spec behav body in
              let newid = f.fun_name ^ "_safety" in
              reg_decl
		~out_mark:newid
		~in_mark:f.fun_name
		~name:("function " ^ f.fun_name)
		~beh:"Safety"
		funpos;
              if is_purely_exceptional_fun spec then acc else
		if Jc_options.verify_invariants_only then acc else
                  Def(
                    id_no_loc newid,
                    !Jc_options.termination_policy <> TPalways,
                    (* false = we require termination proofs *)
                    mk_expr (Fun(
                      params,
                      internal_requires,
                      safety_body,
                      internal_safety_post,
                      excep_posts_for_others None excep_behaviors)))
		  :: acc
	    else acc
	  in

          (* normal behaviors *)
          let acc =
            List.fold_right
              (fun (id,b,internal_post,_) acc ->
		 if Jc_options.verify_behavior id then
                   let normal_body = wrap_body f spec id body in
                   let newid = f.fun_name ^ "_ensures_" ^ id in
                   let beh =
                     if id="default" then "default behavior" else
		       "Behavior `"^id^"'"
                   in
                   reg_decl
                     ~out_mark:newid
                     ~in_mark:f.fun_name
                     ~name:("function " ^ f.fun_name)
                     ~beh
                     funpos;
                   Def(
                     id_no_loc newid,
                     true, (* we do not require termination *)
                     mk_expr (Fun(
		       params,
		       assume_in_precondition b internal_requires,
		       normal_body,
		       internal_post,
		       excep_posts_for_others None excep_behaviors)))
		   :: acc
		 else acc
              ) normal_behaviors acc
          in

          (* exceptional behaviors *)
          let acc =
            ExceptionMap.fold
              (fun exc bl acc ->
                 List.fold_right
                   (fun (id,b,internal_post,_) acc ->
		      if Jc_options.verify_behavior id then
			let except_body = wrap_body f spec id body in
                        let newid = f.fun_name ^ "_exsures_" ^ id in
                        reg_decl
                          ~out_mark:newid
                          ~in_mark:f.fun_name
                          ~name:("function " ^ f.fun_name)
                          ~beh:("Behavior `" ^ id ^ "'")
                          funpos;
                        Def(id_no_loc newid,
                            true, (* we do not require termination *)
                            mk_expr (Fun(
			      params,
			      assume_in_precondition b internal_requires,
			      except_body,
			      LTrue,
			      (exception_name exc, internal_post) ::
                                excep_posts_for_others (Some exc)
				excep_behaviors)))
                        :: acc
		      else acc
		   ) bl acc
	      ) user_excep_behaviors acc
          in
          acc

let tr_fun f funpos spec body acc =
  set_current_function f;
  let acc = tr_fun f funpos spec body acc in
  reset_current_function ();
  acc

let tr_specialized_fun n fname param_name_assoc acc =

  let rec modif_why_type = function
    | Prod_type(n,t1,t2) ->
	if StringMap.mem n param_name_assoc then
	  modif_why_type t2
	else Prod_type(n,t1,modif_why_type t2)
    | Base_type b -> Base_type b
    | Ref_type(t) -> Ref_type (modif_why_type t)
    | Annot_type (pre,t,reads,writes,post,signals) ->
	Annot_type (modif_assertion pre, modif_why_type t,
		    modif_namelist reads,
		    modif_namelist writes,
		    modif_assertion post,
		    List.map (fun (x,a) -> (x,modif_assertion a)) signals)

  and modif_assertion a =
    match a with
      | LTrue
      | LFalse -> a
      | LAnd(a1,a2) -> LAnd(modif_assertion a1,modif_assertion a2)
      | LOr(a1,a2) -> LOr(modif_assertion a1,modif_assertion a2)
      | LIff(a1,a2) -> LIff(modif_assertion a1,modif_assertion a2)
      | LNot(a1) -> LNot(modif_assertion a1)
      | LImpl(a1,a2) -> LImpl(modif_assertion a1,modif_assertion a2)
      | LIf(t,a1,a2) -> LIf(modif_term t,modif_assertion a1,modif_assertion a2)
      | LLet(id,t,a) -> LLet(id,modif_term t,modif_assertion a)
      | LForall(id,t,trigs,a) -> LForall(id,t,triggers trigs,modif_assertion a)
      | LExists(id,t,trigs,a) -> LExists(id,t,triggers trigs,modif_assertion a)
      | LPred(id,l) -> LPred(id,List.map modif_term l)
      | LNamed (n, a) -> LNamed (n, modif_assertion a)

  and triggers trigs =
    let pat = function
      | LPatT t -> LPatT (modif_term t)
      | LPatP a -> LPatP (modif_assertion a) in
    List.map (List.map pat) trigs

  and modif_term t =
    match t with
      | LConst(_c) -> t
      | LApp(id,l) -> LApp(id,List.map modif_term l)
      | LVar(id) ->
	  let id = StringMap.find_or_default id id param_name_assoc in
	  LVar id
      | LDeref(id) ->
	  let id = StringMap.find_or_default id id param_name_assoc in
	  LDeref id
      | LDerefAtLabel(id,l) ->
	  let id = StringMap.find_or_default id id param_name_assoc in
	  LDerefAtLabel(id,l)
      | Tnamed(n,t) -> Tnamed(n,modif_term t)
      | TIf(t1,t2,t3) ->
	  TIf(modif_term t1,modif_term t2,modif_term t3)
      | TLet(id,t1,t2) ->
	  let id = StringMap.find_or_default id id param_name_assoc in
	  TLet(id,modif_term t1,modif_term t2)

  and modif_namelist names =
    fst (List.fold_right
	   (fun id (acc,set) ->
	      let id = StringMap.find_or_default id id param_name_assoc in
	      id :: acc, StringSet.add id set
	   ) names ([],StringSet.empty))
  in

  let fun_type = Hashtbl.find function_prototypes fname in
  let new_fun_type = modif_why_type fun_type in
  Param(false, id_no_loc n, new_fun_type) :: acc


(******************************************************************************)
(*                               Logic entities                               *)
(******************************************************************************)

let tr_logic_type (id,l) acc = Type(id_no_loc id,List.map Jc_type_var.name l) :: acc


let tr_exception ei acc =
  Jc_options.lprintf "producing exception '%s'@." ei.exi_name;
  let typ = match ei.exi_type with
    | Some tei -> Some (tr_base_type tei)
    | None -> None
  in
  Exception(id_no_loc (exception_name ei), typ) :: acc

(* let tr_native_type nty acc = *)
(*   let lt = tr_base_type (JCTnative nty) in *)
(*   Logic(false,logic_bitvector_of_native nty,["",lt],bitvector_type) *)
(*   :: Logic(false,logic_native_of_bitvector nty,["",bitvector_type],lt) *)
(*   :: Axiom((logic_native_of_bitvector nty)^"_of_"^(logic_bitvector_of_native nty), *)
(* 	   LForall("x",lt, *)
(* 		   LPred(equality_op_for_type (JCTnative nty), *)
(*                          [LApp(logic_native_of_bitvector nty, *)
(*                                [LApp(logic_bitvector_of_native nty,  *)
(*                                      [LVar "x"])]); *)
(*                           LVar "x"]))) *)
(*   :: Axiom((logic_bitvector_of_native nty)^"_of_"^(logic_native_of_bitvector nty), *)
(* 	   LForall("x",bitvector_type, *)
(* 		   LPred("eq", (\* TODO: equality for bitvectors ? *\) *)
(*                          [LApp(logic_bitvector_of_native nty, *)
(*                                [LApp(logic_native_of_bitvector nty,  *)
(*                                      [LVar "x"])]); *)
(*                           LVar "x"]))) *)
(*   :: acc *)

let range_of_enum ri =
  Num.add_num (Num.sub_num ri.ei_max ri.ei_min) (Num.Int 1)

let tr_enum_type ri (* to_int of_int *) acc =
  let name = ri.ei_name in
  let min = Num.string_of_num ri.ei_min in
  let max = Num.string_of_num ri.ei_max in
  let width = Num.string_of_num (range_of_enum ri) in
  let lt = simple_logic_type name in
  let in_bounds x =
    LAnd(LPred("le_int",[LConst(Prim_int min); x]),
         LPred("le_int",[x; LConst(Prim_int max)]))
  in
  let safe_of_int_type =
    let post =
      LPred("eq_int",
            [LApp(logic_int_of_enum ri,[LVar "result"]);
             if !Jc_options.int_model = IMbounded then LVar "x"
             else LApp(mod_of_enum ri,[LVar "x"])])
    in
    Prod_type("x", Base_type(why_integer_type),
              Annot_type(LTrue,
                         Base_type lt,
                         [],[],post,[]))
  in
  let of_int_type =
    let pre =
      if !Jc_options.int_model = IMbounded then in_bounds (LVar "x") else LTrue
    in
    let post =
      LPred("eq_int",
            [LApp(logic_int_of_enum ri,[LVar "result"]);
             if !Jc_options.int_model = IMbounded then LVar "x"
             else LApp(mod_of_enum ri,[LVar "x"])])
    in
    Prod_type("x", Base_type(why_integer_type),
              Annot_type(pre,Base_type lt,[],[],post,[]))
  in
  let any_type =
    Prod_type("", Base_type(simple_logic_type "unit"),
              Annot_type(LTrue,Base_type lt,[],[],LTrue,[]))
  in
  let bv_conv =
    if !Region.some_bitwise_region then
      [Logic(false,id_no_loc (logic_bitvector_of_enum ri),
	     ["",lt],bitvector_type) ;
       Logic(false,id_no_loc (logic_enum_of_bitvector ri),
	     ["",bitvector_type],lt) ;
       Goal(KAxiom,id_no_loc ((logic_enum_of_bitvector ri)^"_of_"^
				(logic_bitvector_of_enum ri)),
	    LForall("x",lt, [],
		    LPred(equality_op_for_type (JCTenum ri),
                         [LApp(logic_enum_of_bitvector ri,
                               [LApp(logic_bitvector_of_enum ri,
                                     [LVar "x"])]);
                          LVar "x"])));
       Goal(KAxiom,id_no_loc ((logic_bitvector_of_enum ri)^"_of_"^
				(logic_enum_of_bitvector ri)),
	   LForall("x",bitvector_type, [],
		   LPred("eq", (* TODO: equality for bitvectors ? *)
                         [LApp(logic_bitvector_of_enum ri,
                               [LApp(logic_enum_of_bitvector ri,
                                     [LVar "x"])]);
                          LVar "x"]))) ]
    else []
  in
  Type(id_no_loc name,[])
  :: Logic(false,id_no_loc (logic_int_of_enum ri),
           [("",lt)],why_integer_type)
  :: Logic(false,id_no_loc (logic_enum_of_int ri),
           [("",why_integer_type)],lt)
  :: Predicate(false,id_no_loc (eq_of_enum ri),[("x",lt);("y",lt)],
               LPred("eq_int",[LApp(logic_int_of_enum ri,[LVar "x"]);
                               LApp(logic_int_of_enum ri,[LVar "y"])]))
  :: (if !Jc_options.int_model = IMmodulo then
        let width = LConst (Prim_int width) in
        let fmod t = LApp (mod_of_enum ri, [t]) in
        [Logic (false, id_no_loc (mod_of_enum ri),
                ["x", simple_logic_type "int"], simple_logic_type "int");
         Goal(KAxiom,id_no_loc (name ^ "_mod_def"),
                LForall ("x", simple_logic_type "int", [],
                         LPred ("eq_int", [LApp (mod_of_enum ri, [LVar "x"]);
                                           LApp (logic_int_of_enum ri,
                                                 [LApp (logic_enum_of_int ri,
                                                        [LVar "x"])])])));
         Goal(KAxiom,id_no_loc (name ^ "_mod_lb"),
                LForall ("x", simple_logic_type "int", [],
                         LPred ("ge_int", [LApp (mod_of_enum ri, [LVar "x"]);
                                           LConst (Prim_int min)])));
         Goal(KAxiom,id_no_loc (name ^ "_mod_gb"),
                LForall ("x", simple_logic_type "int", [],
                         LPred ("le_int", [LApp (mod_of_enum ri, [LVar "x"]);
                                           LConst (Prim_int max)])));
         Goal(KAxiom,id_no_loc (name ^ "_mod_id"),
                LForall ("x", simple_logic_type "int", [],
                         LImpl (in_bounds (LVar "x"),
                                LPred ("eq_int", [LApp (mod_of_enum ri,
                                                        [LVar "x"]);
                                                  LVar "x"]))));
         Goal(KAxiom,id_no_loc (name ^ "_mod_lt"),
                LForall ("x", simple_logic_type "int", [],
                         LImpl (LPred ("lt_int", [LVar "x";
                                                  LConst (Prim_int min)]),
                                LPred ("eq_int", [fmod (LVar "x");
                                                  fmod (LApp ("add_int",
                                                              [LVar "x";
                                                               width]))]))));
         Goal(KAxiom,id_no_loc (name ^ "_mod_gt"),
                LForall ("x", simple_logic_type "int", [],
                         LImpl (LPred ("gt_int", [LVar "x";
                                                  LConst (Prim_int max)]),
                                LPred ("eq_int", [fmod (LVar "x");
                                                  fmod (LApp ("sub_int",
                                                              [LVar "x";
                                                               width]))]))));
        ]
      else [])
  @ Param(false,id_no_loc (fun_enum_of_int ri),of_int_type)
  :: Param(false,id_no_loc (safe_fun_enum_of_int ri),safe_of_int_type)
  :: Param(false,id_no_loc (fun_any_enum ri),any_type)
  :: Goal(KAxiom,id_no_loc (name^"_range"),
           LForall("x",lt, [],in_bounds
                     (LApp(logic_int_of_enum ri,[LVar "x"]))))
  :: Goal(KAxiom,id_no_loc (name^"_coerce"),
           LForall("x",why_integer_type, [],
                   LImpl(in_bounds (LVar "x"),
                         LPred("eq_int",
                               [LApp(logic_int_of_enum ri,
                                     [LApp(logic_enum_of_int ri,
                                           [LVar "x"])]) ;
                                LVar "x"]))))
(*
  :: Goal(KAxiom,id_no_loc (name^"_extensionality"),
           LForall("x",lt, [],
           LForall("y",lt, [ (* [LPatP(LPred(eq_of_enum ri,
                                         [LVar "x"; LVar "y"]))] *) ],
                   LImpl(LPred(eq_of_enum ri,[LVar "x"; LVar "y"]),
                         LPred("eq",[LVar "x"; LVar "y"])
                         ))))
*)
  :: Goal(KAxiom,id_no_loc (name^"_extensionality"),
           LForall("x",lt, [],
           LForall("y",lt, [ [LPatP(LPred("eq_int_bool",
                               [LApp(logic_int_of_enum ri, [LVar "x"]);
                                LApp(logic_int_of_enum ri, [LVar "y"])]))] ],
                   LImpl(LPred("eq_int_bool",
                               [LApp(logic_int_of_enum ri, [LVar "x"]);
                                LApp(logic_int_of_enum ri, [LVar "y"])]),
                         LPred("eq",[LVar "x"; LVar "y"])
                         ))))
  :: bv_conv
  @ acc

let tr_enum_type_pair ri1 ri2 acc =
  (* Information from first enum *)
  let name1 = ri1.ei_name in
  let min1 = ri1.ei_min in
  let max1 = ri1.ei_max in
  (* Information from second enum *)
  let name2 = ri2.ei_name in
  let min2 = ri2.ei_min in
  let max2 = ri2.ei_max in
  if not (!Jc_options.int_model = IMmodulo) then acc else
    if max1 </ min2 || max2 </ min1 then acc else
      (* Compute intersection of ranges *)
      let min = if min1 <=/ min2 && min2 <=/ max1 then min2 else min1 in
      let max = if min1 <=/ max2 && max2 <=/ max1 then max2 else max1 in
      let in_bounds x =
        LAnd(LPred("le_int",[LConst(Prim_int (Num.string_of_num min)); x]),
             LPred("le_int",[x; LConst(Prim_int (Num.string_of_num max))]))
      in
      (* Integer model is modulo and enum ranges intersect. Produce useful
       * axioms that relate both modulos when they coincide.
       *)
      let range1 = range_of_enum ri1 in
      let range2 = range_of_enum ri2 in
      let mod_coincide smallri bigri smallname bigname =
        (* When modulo the big range is in the intersection of the ranges,
         * both modulos coincide.
         *)
        let modsmall = LApp(mod_of_enum smallri,[LVar "x"]) in
        let modbig = LApp(mod_of_enum bigri,[LVar "x"]) in
        Goal(KAxiom,id_no_loc (smallname ^ "_" ^ bigname ^ "_mod_coincide"),
              LForall("x",why_integer_type, [],
                      LImpl(in_bounds modbig,
                            LPred("eq_int",[modsmall;modbig]))))
      in
      if range1 </ range2 then
        mod_coincide ri1 ri2 name1 name2 :: acc
      else if range2 </ range1 then
        mod_coincide ri2 ri1 name2 name1 :: acc
      else
        mod_coincide ri1 ri2 name1 name2
        :: mod_coincide ri2 ri1 name2 name1 :: acc

let tr_variable vi _e acc =
  if vi.vi_assigned then
    let t = Ref_type(tr_var_type vi) in
      Param(false,id_no_loc vi.vi_final_name,t)::acc
  else
    let t = tr_base_type vi.vi_type in
      Logic(false,id_no_loc vi.vi_final_name,[],t)::acc

let tr_region r acc =
  Type(id_no_loc r.r_final_name,[]) :: acc

let tr_memory (mc,r) acc =
  Param(
    false,id_no_loc (memory_name(mc,r)),
    Ref_type(Base_type(memory_type mc))) :: acc

let tr_alloc_table (pc,r) acc =
  Param(
    false,id_no_loc (alloc_table_name(pc,r)),
    Ref_type(Base_type(alloc_table_type pc))) :: acc

let tr_tag_table (rt,r) acc =
  Param(
    false,id_no_loc (tag_table_name(rt,r)),
    Ref_type(Base_type(tag_table_type rt))) :: acc


(******************************************************************************)
(*                                  Roots                                     *)
(******************************************************************************)

let tr_root rt acc =
  let pc = JCroot rt in
  let ac = alloc_class_of_pointer_class pc in
  let acc =
    if root_is_union rt then
      (* Declarations of field memories. *)
      let acc =
	if root_is_plain_union rt && !Jc_options.separation_sem = SepRegions
        then acc
        else
            let mem = bitvector_type in
            Param(false,id_no_loc (union_memory_name rt),
		  Ref_type(Base_type mem)) :: acc
      in
      let in_param = false in
        (* Validity parameters *)
           make_valid_pred ~in_param ~equal:true ac pc
        :: make_valid_pred ~in_param ~equal:false ac pc
        :: make_valid_pred ~in_param ~equal:false ~right:false ac pc
        :: make_valid_pred ~in_param ~equal:false ~left:false ac pc
(*
        :: make_valid_pred ~in_param ~equal:false (* TODO ? *) JCalloc_bitvector pc
*)
        (* Allocation parameter *)
        :: make_alloc_param ~arg:Singleton ac pc
        :: make_alloc_param ~arg:Range_0_n ~check_size:true ac pc
        :: make_alloc_param ~arg:Range_0_n ~check_size:false ac pc
(*
        :: make_alloc_param ~check_size:true JCalloc_bitvector pc
        :: make_alloc_param ~check_size:false JCalloc_bitvector pc
*)
        :: acc
    else
      make_valid_pred ~in_param:false ~equal:true ac pc
      :: make_valid_pred ~in_param:false ~equal:false ac pc
      :: acc
  in
  let lt = tr_base_type (JCTpointer(pc,None,None)) in
  let conv =
    if !Region.some_bitwise_region then
    [Logic(false,id_no_loc (logic_bitvector_of_variant rt),
	   ["",lt],bitvector_type);
     Logic(false,id_no_loc (logic_variant_of_bitvector rt),
	   ["",bitvector_type],lt);
     Goal(KAxiom,id_no_loc ((logic_variant_of_bitvector rt)^"_of_"^
			      (logic_bitvector_of_variant rt)),
	   LForall("x",lt, [],
		   LPred(equality_op_for_type (JCTpointer (pc,None,None)),
                         [LApp(logic_variant_of_bitvector rt,
			       [LApp(logic_bitvector_of_variant rt,
                                     [LVar "x"])]);
                          LVar "x"])));
     Goal(KAxiom,id_no_loc ((logic_bitvector_of_variant rt)^"_of_"^
			      (logic_variant_of_bitvector rt)),
	   LForall("x",bitvector_type, [],
		   LPred("eq", (* TODO: equality for bitvectors ? *)
                         [LApp(logic_bitvector_of_variant rt,
			       [LApp(logic_variant_of_bitvector rt,
                                       [LVar "x"])]);
                          LVar "x"])))
    ]
    else
      []
  in
  let tag_table =
    Param(
      false,
      id_no_loc (variant_tag_table_name rt),
      Ref_type(
        Base_type {
          logic_type_name = tag_table_type_name;
          logic_type_args = [root_model_type rt];
        }))
  in
  let alloc_table =
    Param(
      false,
      id_no_loc (variant_alloc_table_name rt),
      Ref_type(
        Base_type {
          logic_type_name = alloc_table_type_name;
          logic_type_args = [root_model_type rt];
        }))
  in
  let type_def = Type(id_no_loc (root_type_name rt), []) in
  (* Axiom: the variant can only have the given tags *)
  let axiom_variant_has_tag =
    let v = "x" in
    Goal (KAxiom, id_no_loc (variant_axiom_on_tags_name rt),
      LForall (v, pointer_type ac pc, [],
                  make_or_list @@
                    List.map
                      (make_instanceof @@ LVar v)
                      rt.ri_hroots))
  in
  (* Axioms: int_of_tag(T1) = 1, ... *)
  let (acc, _) = List.fold_left
    (fun (acc, index) st ->
       let axiom =
         Goal(KAxiom,
           id_no_loc (axiom_int_of_tag_name st),
           make_eq
             (make_int_of_tag st)
             (LConst(Prim_int(string_of_int index)))
         )
       in axiom::acc, index+1)
    (acc, 1)
    rt.ri_hroots
  in
  let acc =
    type_def :: alloc_table :: tag_table :: axiom_variant_has_tag :: conv @
    acc
  in
  acc

(*
  Local Variables:
  compile-command: "unset LANG; make -j -C .. bin/jessie.byte"
  End:
*)
