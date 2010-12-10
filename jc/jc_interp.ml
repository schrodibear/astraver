(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                  *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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



open Jc_stdlib
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

let pos_table = Hashtbl.create 97

let abs_fname f =
  if Filename.is_relative f then
    Filename.concat (Unix.getcwd ()) f
  else f

type source_ref =
    {
      in_mark: string;
      pos: Loc.position
    }

type gui_elem =
    {
      out_mark: string;
      kind: kind option;
      name: string option;
      beh: string option
    }

let reg_pos sce gui =
  if gui.out_mark <> "" && StdHashtbl.mem Output.pos_table gui.out_mark then
    (* If GUI element already refered to in output table, do not
     * reference it twice. This is the case in particular for generated
     * annotations. *)
    gui.out_mark
  else
    (* Generate a new mark if not fixed in GUI element *)
    let mark =
      if gui.out_mark = "" then
	Jc_pervasives.new_label_name()
      else gui.out_mark
    in
    let (n,f,l,b,e,k) =
      if sce.in_mark <> "" && Hashtbl.mem Jc_options.pos_table sce.in_mark then
	(* If source location present in input table, copy information to
	 * output table. *)
	let (f,l,b,e,k,o) = Hashtbl.find Jc_options.pos_table sce.in_mark in
	let n =
	  try match List.assoc "name" o with
            | Rc.RCident s | Rc.RCstring s -> Some s
            | _ -> raise Not_found
	  with Not_found -> gui.name
	in
	(n,f,l,b,e,k)
      else
	(* By default, refer to the Jessie source file *)
	let b,e = sce.pos in
	let f = abs_fname b.Lexing.pos_fname in
	let l = b.Lexing.pos_lnum in
	let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
	let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
	(gui.name,f,l,fc,lc,None)
    in
    (* If present, always prefer new kind *)
    let k = match gui.kind with None -> k | Some k -> Some k in
    Hashtbl.replace pos_table mark (k,n,gui.beh,f,l,b,e);
    mark

let reg_check ?mark ?kind pos =
  let sce =
    { in_mark = Option_misc.map_default (fun x -> x) "" mark; pos = pos; }
  in
  let gui = { out_mark = ""; kind = kind; name = None; beh = None; } in
  reg_pos sce gui

let reg_decl ~in_mark ~out_mark ~name ~beh pos =
  let sce = { in_mark = in_mark; pos = pos; } in
  let gui =
    { out_mark = out_mark; kind = None; name = Some name; beh = Some beh; }
  in
  ignore (reg_pos sce gui)

let make_check ?mark ?kind pos e' =
  let mark = reg_check ?mark ?kind pos in
(*
  eprintf "Jc_interp.make_check: adding label %s@." mark;
*)
  make_label mark e'

let make_guarded_app ~mark kind pos f args =
  make_check ~mark ~kind pos (make_app f args)


let print_locs fmt =
  Hashtbl.iter
    (fun id (kind,name,beh,f,l,b,e) ->
       fprintf fmt "[%s]@\n" id;
       Option_misc.iter
         (fun k -> fprintf fmt "kind = %a@\n" print_kind k) kind;
       Option_misc.iter
         (fun n -> fprintf fmt "name = \"%s\"@\n" n) name;
       Option_misc.iter
	 (fun b -> fprintf fmt "behavior = \"%s\"@\n" b) beh;
       fprintf fmt "file = \"%s\"@\n" (String.escaped f);
       fprintf fmt "line = %d@\n" l;
       fprintf fmt "begin = %d@\n" b;
       fprintf fmt "end = %d@\n@\n" e)
    pos_table


(******************************************************************************)
(*                                 Operators                                  *)
(******************************************************************************)

let native_operator_type op = match snd op with
  | `Unit -> Jc_pervasives.unit_type
  | `Boolean -> Jc_pervasives.boolean_type
  | `Integer -> Jc_pervasives.integer_type
  | `Real -> Jc_pervasives.real_type
  | `Double -> Jc_pervasives.double_type
  | `Float -> Jc_pervasives.float_type
  | `Binary80 -> JCTnative (Tgenfloat `Binary80)

let unary_op: expr_unary_op -> string = function
  | `Uminus, `Integer -> "neg_int"
  | `Uminus, `Real -> "neg_real"
  | `Unot, `Boolean -> "not"
  | `Ubw_not, `Integer -> "bw_compl"
  | _ -> assert false (* not proper type *)

let term_unary_op: expr_unary_op -> string = function
  | `Uminus, `Integer -> "neg_int"
  | `Uminus, `Real -> "neg_real"
  | `Unot, `Boolean -> "bool_not"
  | `Ubw_not, `Integer -> "bw_compl"
  | _ -> assert false (* not proper type *)

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
      | `Bmod -> assert false
  in
  if float_model_has_safe_functions() && (not (safety_checking()))
  then s ^ (float_format t) ^"_safe" else s^ (float_format t)



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

let bin_op: expr_bin_op -> string = function
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
  | `Bdiv, `Integer ->
      if safety_checking () then "computer_div_" else "computer_div"
  | `Bmod, `Integer ->
      if safety_checking () then "computer_mod_" else "computer_mod"
      (* pointer *)
  | `Beq, `Pointer ->
      if safety_checking () then "eq_pointer" else "safe_eq_pointer"
  | `Bneq, `Pointer ->
      if safety_checking () then "neq_pointer" else "safe_neq_pointer"
  | `Bsub, `Pointer ->
      if safety_checking () then "sub_pointer_" else "safe_sub_pointer_"
      (* real *)
  | `Bgt, `Real -> "gt_real_"
  | `Blt, `Real -> "lt_real_"
  | `Bge, `Real -> "ge_real_"
  | `Ble, `Real -> "le_real_"
  | `Beq, `Real -> "eq_real_"
  | `Bneq, `Real -> "neq_real_"
  | `Bgt, `Float -> "gt_single"
  | `Blt, `Float -> "lt_single"
  | `Bge, `Float -> "ge_single"
  | `Ble, `Float -> "le_single"
  | `Beq, `Float -> "eq_single"
  | `Bneq,`Float -> "ne_single"
  | `Bgt, `Double -> "gt_double"
  | `Blt, `Double -> "lt_double"
  | `Bge, `Double -> "ge_double"
  | `Ble, `Double -> "le_double"
  | `Beq, `Double -> "eq_double"
  | `Bneq, `Double -> "ne_double"
  | `Badd, `Real -> "add_real"
  | `Bsub, `Real -> "sub_real"
  | `Bmul, `Real -> "mul_real"
  | `Bdiv, `Real ->
      if safety_checking () then "div_real_" else "div_real"
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
  | `Bland, _ -> assert false
  | `Blor, _ -> assert false
  | `Bconcat, _ -> "string_concat"
  | op, opty ->
      Jc_typing.typing_error Loc.dummy_position
        "Can't use operator %s with type %s in expressions"
        (string_of_op op) (string_of_op_type opty)

let term_bin_op: term_bin_op -> string = function
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
(*  | `Beq_bool, `Boolean -> "eq_bool"
  | `Bneq_bool, `Boolean -> "neq_bool"*)
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
  | `Biff, _ | `Bimplies, _ ->
      assert false (* TODO *)
  | op, opty ->
      Jc_typing.typing_error Loc.dummy_position
        "Can't use operator %s with type %s in terms"
        (string_of_op op) (string_of_op_type opty)

let pred_bin_op: pred_bin_op -> string = function
    (* integer *)
  | `Bgt, `Integer -> "gt_int"
  | `Blt, `Integer -> "lt_int"
  | `Bge, `Integer -> "ge_int"
  | `Ble, `Integer -> "le_int"
  | `Beq, `Integer -> "eq_int"
  | `Bneq, `Integer -> "neq_int"
      (* pointer *)
  | `Beq, (`Pointer | `Logic) -> "eq"
  | `Bneq, (`Pointer | `Logic) -> "neq"
      (* real *)
  | `Beq, `Real -> "eq_real"
  | `Bneq, `Real -> "neq_real"
  | `Bgt, `Real -> "gt_real"
  | `Blt, `Real -> "lt_real"
  | `Bge, `Real -> "ge_real"
  | `Ble, `Real -> "le_real"
      (* logical *)
  | `Blor, `Boolean -> "bor"
  | `Bland, `Boolean -> "band"
  | `Biff, `Boolean
  | `Bimplies, `Boolean -> assert false (* TODO *)
      (* boolean *)
  | `Beq, `Boolean -> "eq_bool"
  | `Bneq, `Boolean -> "eq_bool"
  | op, opty ->
      Jc_typing.typing_error Loc.dummy_position
        "Can't use operator %s with type %s in assertions"
        (string_of_op op) (string_of_op_type opty)


(******************************************************************************)
(*                                   types                                    *)
(******************************************************************************)

let has_equality_op = function
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

let equality_op_for_type = function
  | JCTnative Tunit -> assert false
  | JCTnative Tboolean -> "eq_bool"
  | JCTnative Tinteger -> "eq_int"
  | JCTnative Treal -> "eq_real"
  | JCTnative (Tgenfloat f) -> ("eq_"^(float_format f))
  | JCTnative Tstring -> "eq"
  | JCTlogic _s -> (* TODO *) assert false
  | JCTenum ei -> eq_of_enum ei
  | JCTpointer _
  | JCTnull ->  "eq"
  | JCTany -> assert false
  | JCTtype_var _ -> assert false (* TODO ? *)


(******************************************************************************)
(*                                 Structures                                 *)
(******************************************************************************)

let tr_struct st acc =
  let tagid_type = tag_id_type (struct_root st) in
    (* Declarations of field memories. *)
  let acc =
    if !Jc_options.separation_sem = SepRegions then acc else
      if struct_of_plain_union st then acc else
        List.fold_left
          (fun acc fi ->
             let mem = memory_type (JCmem_field fi) in
             Param(
               false,
               field_memory_name fi,
               Ref_type(Base_type mem))::acc)
          acc st.jc_struct_info_fields
  in
  (* Declarations of translation functions for union *)
  let vi = struct_root st in
  let acc =
    if not (root_is_union vi) then acc else
      if integral_union vi then acc else
        let uty = bitvector_type in
        List.fold_left
          (fun acc fi ->
	     if has_equality_op fi.jc_field_info_type then
               Logic(false,logic_field_of_union fi,
                     [("",uty)],tr_base_type fi.jc_field_info_type)
               :: Logic(false,logic_union_of_field fi,
			[("",tr_base_type fi.jc_field_info_type)],uty)
               :: Axiom((logic_field_of_union fi)^"_of_"^(logic_union_of_field fi),
			LForall("x",tr_base_type fi.jc_field_info_type, [],
				LPred(equality_op_for_type fi.jc_field_info_type,
                                      [LApp(logic_field_of_union fi,
                                            [LApp(logic_union_of_field fi,
                                                  [LVar "x"])]);
                                       LVar "x"])))
               :: acc
	     else acc)
          acc st.jc_struct_info_fields
  in
  (* declaration of the tag_id *)
  let acc =
    Logic(false,tag_name st,[],tagid_type)::acc
  in

  let acc =
    if struct_of_union st then acc
    else
      let pc = JCtag(st,[]) in
      let ac = alloc_class_of_pointer_class pc in
	(* Validity parameters *)
	make_valid_pred ~equal:true ac pc
	:: make_valid_pred ~equal:false ac pc
	:: make_valid_pred ~equal:false ~right:false ac pc
	:: make_valid_pred ~equal:false ~left:false ac pc
	:: make_valid_pred ~equal:true (* TODO ? *) JCalloc_bitvector pc
	  (* Allocation parameters *)
	:: make_alloc_param ~check_size:true ac pc
	:: make_alloc_param ~check_size:false ac pc
	:: make_alloc_param ~check_size:true JCalloc_bitvector pc
	:: make_alloc_param ~check_size:false JCalloc_bitvector pc
	:: (if Region.exists_bitwise () then make_conversion_params pc else [])
	@ acc
  in

  match st.jc_struct_info_parent with
    | None ->
        (* axiom for parenttag *)
        let name = st.jc_struct_info_name ^ "_parenttag_bottom" in
        let p = LPred("parenttag", [ LVar (tag_name st); LVar "bottom_tag" ]) in
        Axiom(name, p)::acc
    | Some(p, _) ->
        (* axiom for parenttag *)
        let name =
          st.jc_struct_info_name ^ "_parenttag_" ^ p.jc_struct_info_name
        in
        let p =
          LPred("parenttag", [ LVar (tag_name st); LVar (tag_name p) ])
        in
        Axiom(name, p)::acc


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
          else
            (*
              Format.eprintf"real constant: %s@." x;
            *)
            raise Not_found
     | `Double ->
          if String.length s <= 15 (* x < 10^15 < 2^53 *) then x
          else
            (*
              Format.eprintf"real constant: %s@." x;
            *)
            raise Not_found
     | `Binary80 -> raise Not_found
  else
    match f,x with
      | _ , "0.5" -> x
      | `Float, "0.1" -> "0x0.199999Ap0"
      | _ -> raise Not_found

let rec term_coerce ~type_safe ~global_assertion lab ?(cast=false) pos
    ty_dst ty_src e e' =
  let rec aux a b =
    match a,b with
      | JCTlogic (t,tl), JCTlogic (u,ul) when t = u -> List.for_all2 aux tl ul
      | JCTtype_var _, JCTtype_var _ -> true (*jc_typing take care of that*)
      | (JCTtype_var _, _) | (_,JCTtype_var _) -> true
      | JCTpointer (JCroot rt1,_,_), JCTpointer (JCroot rt2,_,_) -> rt1 == rt2
      | _ -> false
  in
  match ty_dst, ty_src with
      (* identity *)
    | JCTnative t, JCTnative u when t = u -> e'
    | (JCTlogic _|JCTtype_var _), (JCTlogic _|JCTtype_var _)
      when aux ty_dst ty_src -> e'
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
	begin
	  match e' with
	    | LApp (f,[LConst (Prim_real _) as c])
		when f = "single_of_real_exact" || f = "single_of_real_exact" ->
		c
	    | _ -> LApp((float_format f)^"_value",[ e' ])
	end
    | JCTnative (Tgenfloat f), JCTnative Treal ->
	begin
          try
	    match e' with
	      | LConst (Prim_real x) ->
		  LApp ((float_format f)^"_of_real_exact",
		        [LConst (Prim_real (float_of_real f x))])
	      | _ -> raise Not_found
          with Not_found ->
	    LApp ("round_"^(float_format f)^"_logic",
		  [ logic_current_rounding_mode () ; e' ])
	end
    | JCTnative (Tgenfloat _f), (JCTnative Tinteger | JCTenum _) ->
        term_coerce ~type_safe ~global_assertion lab pos ty_dst (JCTnative Treal) e
          (term_coerce ~type_safe ~global_assertion lab pos (JCTnative Treal) ty_src e e')
    | JCTnative Tinteger, JCTnative Treal ->
	assert false (* LApp("int_of_real",[ e' ]) *)
      (* between enums and integer *)
    | JCTenum ri1, JCTenum ri2
	when ri1.jc_enum_info_name = ri2.jc_enum_info_name -> e'
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
    | JCTpointer(pc1,_,_), JCTpointer(JCtag(st2,_),_,_)
        when Jc_typing.substruct st2 pc1 -> e'
    | JCTpointer(JCtag(st1,_),_,_), JCTpointer _ ->
	let tag =
	  ttag_table_var ~label_in_name:global_assertion lab
	    (struct_root st1,e#region)
	in
        LApp("downcast", [ tag; e'; LVar (tag_name st1) ])
    |  _ ->
         Jc_typing.typing_error pos
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
            | `Bmod, `Integer ->
                mod_num v1 v2
            | (`Badd | `Barith_shift_right | `Bbw_and | `Bbw_or | `Bbw_xor
              | `Bdiv | `Beq | `Bge | `Bgt | `Ble | `Blogical_shift_right
              | `Blt | `Bmod | `Bmul | `Bneq | `Bshift_left | `Bsub), _ ->
		raise Exit
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
      | JCEalloc _ | JCEfree _ | JCEmatch _ |JCEunpack _ |JCEpack _
      | JCEthrow _ | JCEtry _ | JCEreturn _ | JCEloop _ | JCEblock _
      | JCEcontract _ | JCEassert _
      | JCElet _ | JCEassign_heap _ | JCEassign_var _ | JCEapp _
      | JCEreturn_void -> raise Exit

  in
  try Some(eval e) with Exit | Division_by_zero -> None

let rec fits_in_enum ri e =
  match eval_integral_const e with
    | Some c -> ri.jc_enum_info_min <=/ c && c <=/ ri.jc_enum_info_max
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
	      { e' with expr_node = Cte(Prim_real(n ^ ".0")) }
	  | _ ->
	      make_app "real_of_int" [ e' ]
	end
    | JCTnative Treal, JCTenum ri ->
	begin match e'.expr_node with
	  | Cte(Prim_int n) ->
	      { e' with expr_node = Cte(Prim_real(n ^ ".0")) }
	  | _ ->
	      make_app "real_of_int" [ make_app (logic_int_of_enum ri) [ e' ] ]
	end
    | JCTnative Tinteger, JCTnative Treal ->
	assert false (* make_app "int_of_real" [ e' ] *)
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
        if enlarge then
          make_app ((float_format f2)^"_to_"^(float_format f1)) [ e' ]
        else if check_int_overflow then
          make_guarded_app ~mark FPoverflow pos
            ((float_format f2)^"_to_"^(float_format f1))
            [current_rounding_mode () ; e' ]
        else
          make_app ((float_format f2)^"_to_"^(float_format f1))
            [ current_rounding_mode () ; e' ]
    | JCTnative (Tgenfloat f), JCTnative Treal ->
	begin
          try
	    match e'.expr_node with
	      | Cte (Prim_real x) ->
		  let s = float_of_real f x in
		  make_app ((float_format f)^"_of_real_exact")
		  [ { e' with expr_node = Cte (Prim_real s) } ]
	      | _ -> raise Not_found
          with Not_found ->
	    if check_int_overflow then
	      make_guarded_app ~mark FPoverflow pos
	        ((float_format f)^"_of_real")
	        [ current_rounding_mode () ; e' ]
	    else
	      make_app ((float_format f)^"_of_real_safe")
	        [ current_rounding_mode () ; e' ]
	end
    | JCTnative Treal, JCTnative (Tgenfloat f) ->
	make_app ((float_format f)^"_value") [ e' ]
      (* between enums and integer *)
    | JCTenum ri1, JCTenum ri2
	when ri1.jc_enum_info_name = ri2.jc_enum_info_name -> e'
    | JCTenum ri1, JCTenum ri2 ->
        let e' = make_app (logic_int_of_enum ri2) [ e' ] in
        if not check_int_overflow || fits_in_enum ri1 e then
          make_app (safe_fun_enum_of_int ri1) [ e' ]
        else
          make_guarded_app ~mark ArithOverflow pos (fun_enum_of_int ri1) [ e' ]
    | JCTnative Tinteger, JCTenum ri ->
        make_app (logic_int_of_enum ri) [ e' ]
    | JCTenum ri, JCTnative Tinteger ->
        if not check_int_overflow || fits_in_enum ri e then
          make_app (safe_fun_enum_of_int ri) [ e' ]
        else
          make_guarded_app ~mark ArithOverflow pos (fun_enum_of_int ri) [ e' ]
      (* between pointers and null *)
    | JCTpointer _ , JCTnull -> e'
    | JCTpointer(pc1,_,_), JCTpointer(JCtag(st2,_),_,_)
        when Jc_typing.substruct st2 pc1 -> e'
    | JCTpointer(JCtag(st1,_),_,_), JCTpointer _  ->
	let downcast_fun =
	  if safety_checking () then "downcast_" else "safe_downcast_"
	in
	let tag = tag_table_var(struct_root st1,e#region) in
        make_guarded_app ~mark DownCast pos downcast_fun
          [ tag; e'; mk_var(tag_name st1) ]
    | _ ->
        Jc_typing.typing_error pos
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
(*     | JCTbinary(t1,(`Bsub,`Pointer),t2) -> *)
(*         let t1' = LApp("address",[ ft t1 ]) in *)
(*         let t2' = LApp("address",[ ft t2 ]) in *)
(* 	let st = pointer_struct t1#typ in *)
(* 	let s = string_of_int (struct_size_in_bytes st) in *)
(*         LApp( *)
(* 	  term_bin_op (`Bdiv,`Integer), *)
(* 	  [ LApp(term_bin_op (`Bsub,`Integer), [ t1'; t2' ]); *)
(* 	    LConst(Prim_int s) ]) *)
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
        TIf(t1', t2', t3')
    | JCTlet(vi,t1,t2) ->
        let t1' = ft t1 in
        let t2' = ft t2 in
        TLet(vi.jc_var_info_final_name, t1', t2')
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
    | JCTinstanceof(t1,lab',st) ->
      let lab = if relocate && lab' = LabelHere then lab else lab' in
        let t1' = ft t1 in
	let tag =
	  ttag_table_var ~label_in_name:global_assertion lab
	    (struct_root st,t1#region)
	in
        LApp("instanceof_bool",[ tag; t1'; LVar (tag_name st) ])
    | JCTcast(t1,lab',st) ->
      let lab = if relocate && lab' = LabelHere then lab else lab' in
        if struct_of_union st then
	  ft t1
	else
          let t1' = ft t1 in
	  let tag =
	    ttag_table_var ~label_in_name:global_assertion lab
	      (struct_root st,t1#region)
	  in
          LApp("downcast",[ tag; t1'; LVar (tag_name st) ])
    | JCTbitwise_cast(t1,_lab,_st) ->
	ft t1
    | JCTrange_cast(t1,ri) ->
(*         eprintf "range_cast in term: from %a to %a@."  *)
(*           print_type t1#typ print_type (JCTenum ri); *)
        let t1' = ft t1 in
        term_coerce ~cast:true t1#pos (JCTenum ri) t1#typ t1 t1'
    | JCTreal_cast(t1,rc) ->
        let t1' = ft t1 in
        begin match rc with
          | Integer_to_real ->
              term_coerce t1#pos real_type t1#typ t1 t1'
          | Double_to_real ->
              term_coerce t1#pos real_type t1#typ t1 t1'
	  | Float_to_real ->
	      term_coerce t1#pos real_type t1#typ t1 t1'
(*
          | Real_to_integer ->
              term_coerce t1#pos integer_type t1#typ t1 t1'
*)
	  | Round(f,_rm) ->
              term_coerce t1#pos (JCTnative (Tgenfloat f)) t1#typ t1 t1'
	end
    | JCTderef(t1,lab',fi) ->
	let lab = if relocate && lab' = LabelHere then lab else lab' in
	let mc,_ufi_opt = tderef_mem_class ~type_safe t1 fi in
	begin match mc with
	  | JCmem_field fi' ->
	      assert (fi.jc_field_info_tag = fi'.jc_field_info_tag);
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
		match fi.jc_field_info_bitsize with
		  | Some x -> x / 8
		  | None -> assert false
	      in
	      let off = string_of_int off and size = string_of_int size in
	      let e' =
		LApp("extract_bytes",
		     [ e'; LConst(Prim_int off); LConst(Prim_int size) ])
	      in
	      (* Convert bitvector into appropriate type *)
	      begin match fi.jc_field_info_type with
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
		match fi.jc_field_info_bitsize with
		  | Some x -> x / 8
		  | None -> assert false
	      in
	      let off = string_of_int off and size = string_of_int size in
	      let e' =
		LApp("select_bytes",
		     [ mem; t1'; LConst(Prim_int off); LConst(Prim_int size) ])
	      in
	      (* Convert bitvector into appropriate type *)
	      begin match fi.jc_field_info_type with
		| JCTenum ri -> LApp(logic_enum_of_bitvector ri,[e'])
		| _ty -> assert false (* TODO *)
	      end
	end
    | JCTapp app ->
        let f = app.jc_app_fun in
        let args =
	  List.fold_right (fun arg acc -> (ft arg) :: acc) app.jc_app_args []
        in
        let args =
          try List.map2 (fun e e' -> (e,e')) app.jc_app_args args
          with Invalid_argument _ -> assert false
        in
        let args =
          try
            List.map2
              (fun v (t,t') -> term_coerce t#pos v.jc_var_info_type t#typ t t')
              f.jc_logic_info_parameters args
          with Invalid_argument _ ->
            eprintf "fun = %s, len pars = %d, len args' = %d@."
              f.jc_logic_info_name
              (List.length f.jc_logic_info_parameters)
              (List.length args);
            assert false
        in
	let relab (lab1,lab2) =
	  (lab1, if lab2 = LabelHere then lab else lab2)
	in
	let label_assoc =
	  if relocate then
	    (LabelHere,lab) :: List.map relab app.jc_app_label_assoc
	  else app.jc_app_label_assoc
	in
        make_logic_fun_call ~label_in_name:global_assertion
	  ~region_assoc:app.jc_app_region_assoc
	  ~label_assoc:label_assoc
	  f args
    | JCTold t1 ->
	let lab = if relocate && oldlab = LabelHere then lab else oldlab in
	term ~type_safe ~global_assertion ~relocate lab oldlab t1
    | JCTat(t1,lab') ->
	let lab = if relocate && lab' = LabelHere then lab else lab' in
	term ~type_safe ~global_assertion ~relocate lab oldlab t1
    | JCTrange(_t1,_t2) -> assert false (* TODO ? *)
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
    | JCTtypeof(t,st) ->
	let t' = term ~type_safe ~global_assertion ~relocate lab oldlab t in
	make_typeof st t#region t'

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
(* 	if Jc_options.debug then printf "%a@." Jc_output.assertion a; *)
        let t1' = ft t1 in
        let t2' = ft t2 in
        let ty = native_operator_type op in
        LPred(pred_bin_op (op :> pred_bin_op),
              [ term_coerce t1#pos ty t1#typ t1 t1';
                term_coerce t2#pos ty t2#typ t2 t2' ])
    | JCAapp app ->
        let f = app.jc_app_fun in
        let args =
	  List.fold_right (fun arg acc -> (ft arg) :: acc) app.jc_app_args []
        in
        let args =
          try List.map2 (fun e e' -> (e,e')) app.jc_app_args args
          with Invalid_argument _ -> assert false
        in
        let args =
          try
            List.map2
              (fun v (t,t') -> term_coerce t#pos v.jc_var_info_type t#typ t t')
              f.jc_logic_info_parameters args
          with Invalid_argument _ ->
            eprintf "fun = %s, len pars = %d, len args' = %d@."
              f.jc_logic_info_name
              (List.length f.jc_logic_info_parameters)
              (List.length args);
            assert false
        in
	let label_assoc =
	  if relocate then
	    let relab (lab1,lab2) =
	      (lab1, if lab2 = LabelHere then lab else lab2)
	    in
	    (LabelHere,lab) :: List.map relab app.jc_app_label_assoc
	  else app.jc_app_label_assoc
	in
        make_logic_pred_call
	  ~label_in_name:global_assertion
	  ~region_assoc:app.jc_app_region_assoc
	  ~label_assoc:label_assoc
	  f args
    | JCAquantifier(Forall,v,trigs,a1) ->
        LForall(v.jc_var_info_final_name,
                tr_var_base_type v,
                triggers fa ft trigs,
                fa a1)
    | JCAquantifier(Exists,v,trigs, a1) ->
        LExists(v.jc_var_info_final_name,
                tr_var_base_type v,
                triggers fa ft trigs,
                fa a1)
    | JCAold a1 ->
	let lab = if relocate && oldlab = LabelHere then lab else oldlab in
	assertion ~type_safe ~global_assertion ~relocate lab oldlab a1
    | JCAat(a1,lab') ->
	let lab = if relocate && lab' = LabelHere then lab else lab' in
	assertion ~type_safe ~global_assertion ~relocate lab oldlab a1
    | JCAbool_term t1 ->
        let t1' = ft t1 in
        LPred("eq",[ t1'; LConst(Prim_bool true) ])
    | JCAinstanceof(t1,lab',st) ->
	let lab = if relocate && lab' = LabelHere then lab else lab' in
        let t1' = ft t1 in
	let tag =
	  ttag_table_var ~label_in_name:global_assertion lab
	    (struct_root st,t1#region)
	in
        LPred("instanceof",[ tag; t1'; LVar (tag_name st) ])
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
	LLet(vi.jc_var_info_final_name,ft t, fa p)
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
    | JCLSderef(locs,lab,fi,_r) ->
        let m = tmemory_var ~label_in_name:global_assertion lab
	  (JCmem_field fi,locs#region) in
        (*begin
          match locs#node with
              (* reduce the pset_deref of a singleton *)
            | JCLSvar vi ->
                let v = tvar ~label_in_name:global_assertion before vi in
                LApp("pset_singleton",[LApp("select", [m;v])])
            | _ ->*) LApp("pset_deref", [m;fpset locs])
        (*end*)
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

let rec collect_locations ~type_safe ~global_assertion before (refs,mems) loc =
(*
  let ft = term ~type_safe ~global_assertion ~relocate:false before before in
*)
  match loc#node with
    | JCLderef(e,lab,fi,_fr) ->
        let iloc = pset ~type_safe ~global_assertion lab e in
        let mc =
(*           if field_of_union fi then FVvariant (union_of_field fi) else *)
	  JCmem_field fi
        in
        let l =
          try
            let l = MemoryMap.find (mc,location_set_region e) mems in
            iloc::l
          with Not_found -> [iloc]
        in
        (refs, MemoryMap.add (mc,location_set_region e) l mems)
    | JCLderef_term(_t1,_fi) ->
	assert false
(*
        let iloc = LApp("pset_singleton",[ ft t1 ]) in
        let mc = JCmem_field fi in
        let l =
          try
            let l = MemoryMap.find (mc,t1#region) mems in
            iloc::l
          with Not_found -> [iloc]
        in
        (refs, MemoryMap.add (mc,t1#region) l mems)
*)
    | JCLvar vi ->
        let var = vi.jc_var_info_final_name in
        (StringMap.add var true refs,mems)
    | JCLat(loc,_lab) ->
        collect_locations ~type_safe ~global_assertion before (refs,mems) loc

let rec collect_pset_locations ~type_safe ~global_assertion loc =
  let ft = term ~type_safe ~global_assertion ~relocate:false in
  match loc#node with
    | JCLderef(e,lab,_fi,_fr) ->
        pset ~type_safe ~global_assertion lab e
    | JCLderef_term(t1,_fi) ->
	let lab = match t1#label with Some l -> l | None -> assert false in
	LApp("pset_singleton",[ ft lab lab t1 ])
    | JCLvar _vi ->
	LVar "pset_empty"
    | JCLat(loc,_lab) ->
        collect_pset_locations ~type_safe ~global_assertion loc

let assigns ~type_safe ?region_list before ef locs loc =
  match locs with
    | None -> LTrue
    | Some locs ->
  let refs =
    (* HeapVarSet.fold
            (fun v m ->
               if Ceffect.is_alloc v then m
               else StringMap.add (heap_var_name v) (Reference false) m)
            assigns.Ceffect.assigns_var
    *)
    VarMap.fold
      (fun v _labs m -> StringMap.add v.jc_var_info_final_name false m)
      ef.jc_writes.jc_effect_globals StringMap.empty
  in
  let mems =
    MemoryMap.fold
      (fun (fi,r) _labs acc ->
	 if (* TODO: bug some assigns \nothing clauses are not translated e.g. in Purse.java (perhaps when no region is used). The first test resolve the problem but may hide another bug : What must be region_list when --no-region is used? *)
	   !Jc_options.separation_sem = SepNone || Option_misc.map_default (RegionList.mem r) true region_list then
	   begin
(*
	     eprintf "ASSIGNS FOR FIELD %s@."
	       (match fi with JCmem_field f -> f.jc_field_info_name
		  | _ -> "??");
*)
             MemoryMap.add (fi,r) [] acc
	   end
	 else
	   begin
(*
	     eprintf "IGNORING ASSIGNS FOR FIELD %s@."
	       (match fi with JCmem_field f -> f.jc_field_info_name
		  | _ -> "??");
*)
             MemoryMap.add (fi,r) [] acc
	   end
      ) ef.jc_writes.jc_effect_memories MemoryMap.empty
  in
  let refs,mems =
    List.fold_left (collect_locations ~type_safe ~global_assertion:false before) (refs,mems) locs
  in
  let a =
    StringMap.fold
      (fun v p acc ->
        if p then acc else
          make_and acc (LPred("eq", [LVar v; lvar ~constant:false (* <<- CHANGE THIS *) ~label_in_name:false before v])))
      refs LTrue
  in
  MemoryMap.fold
    (fun (mc,r) p acc ->
       let v = memory_name(mc,r) in
       let ac = alloc_class_of_mem_class mc in
       let _,alloc = talloc_table_var ~label_in_name:false before (ac,r) in

       make_and acc
	 (let a = LPred("not_assigns",
                [alloc;
                 lvar ~constant:false (* <<- CHANGE THIS *)
                   ~label_in_name:false before v;
                 LVar v; location_list' p]) in
	  LNamed(reg_check loc,a))
    ) mems a

let reads ~type_safe ~global_assertion locs (mc,r) =
  let refs = StringMap.empty
  in
  let mems = MemoryMap.empty
  in
  let _refs,mems =
    List.fold_left (collect_locations ~type_safe ~global_assertion LabelOld) (refs,mems) locs
  in
  let p = try MemoryMap.find (mc,r) mems with Not_found -> [] in
  location_list' p


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
	      Hashtbl.find
		Jc_typing.logic_constants_table
		vi.jc_var_info_tag
	    in
	      const_int_term init
	  with Not_found -> None
	end
    | JCTapp app ->
	begin
	  try
	    let _, init =
	      Hashtbl.find
		Jc_typing.logic_constants_table
		app.jc_app_fun.jc_logic_info_tag
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
	      Hashtbl.find
		Jc_typing.logic_constants_table
		vi.jc_var_info_tag
	    in
	      const_int_term init
	  with Not_found -> None
	end
    | JCEapp call ->
	begin match call.jc_call_fun with
	  | JClogic_fun li ->
	      begin
		try
		  let _, init =
		    Hashtbl.find
		      Jc_typing.logic_constants_table
		      li.jc_logic_info_tag
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
    | JCEalloc _ | JCEfree _ | JCEassert _
    | JCEcontract _ | JCEblock _ | JCEloop _
    | JCEreturn_void | JCEreturn _ | JCEtry _
    | JCEthrow _ | JCEpack _ | JCEunpack _
    | JCEcast _ | JCEmatch _ | JCEshift _
    | JCEbitwise_cast _ ->
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
	  ~node:(JCLSderef(old_to_pre_lset lset, old_to_pre lab, fi, lset#region))
	  lset
    | JCLSrange(lset,t1,t2) ->
	new location_set_with
	  ~node:(JCLSrange(old_to_pre_lset lset,
			   Option_misc.map old_to_pre_term t1,
			   Option_misc.map old_to_pre_term t2))
	  lset
    | JCLSrange_term(lset,t1,t2) ->
	new location_set_with
	  ~node:(JCLSrange_term(old_to_pre_term lset,
				Option_misc.map old_to_pre_term t1,
				Option_misc.map old_to_pre_term t2))
	  lset
    | JCLSat(lset,lab) ->
	new location_set_with
	  ~node:(JCLSat(old_to_pre_lset lset,old_to_pre lab))
	  lset

let rec old_to_pre_loc loc =
  match loc#node with
    | JCLvar _ -> loc
    | JCLat(l,lab) ->
	new location_with
	  ~node:(JCLat(old_to_pre_loc l, old_to_pre lab))
	  loc
    | JCLderef(lset,lab,fi,_region) ->
	new location_with
	  ~node:(JCLderef(old_to_pre_lset lset,old_to_pre lab, fi, lset#region))
	  loc
    | JCLderef_term(t1,fi) ->
	new location_with
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
          Hashtbl.find decreases_clause_table (f.jc_fun_info_tag)
        with Not_found ->
          Hashtbl.add decreases_clause_table (f.jc_fun_info_tag) dummy_measure;
          eprintf
            "Warning: generating dummy decrease variant for recursive \
             function %s. Please provide a real variant or set \
             termination policy to user or never\n%!" f.jc_fun_info_name;
          dummy_measure)
    | TPuser ->
        (try
          Hashtbl.find decreases_clause_table (f.jc_fun_info_tag)
         with Not_found -> raise Exit)
    | TPnever -> raise Exit




(* Translate the heap update `e1.fi = tmp2'

   essentially we want

   let tmp1 = [e1] in
   fi := upd(fi,tmp1,tmp2)

   special cases are considered to avoid statically known safety properties:
   if e1 has the form p + i then we build

   let tmpp = p in
   let tmpi = i in
   let tmp1 = shift(tmpp, tmpi) in
    // depending on type of p and value of i
   ...
*)
(*
let rec make_upd_simple mark pos e1 fi tmp2 =
  (* Temporary variables to avoid duplicating code *)
  let tmpp = tmp_var_name () in
  let tmpi = tmp_var_name () in
  let tmp1 = tmp_var_name () in
  (* Define memory and allocation table *)
  let mc,_ufi_opt = deref_mem_class ~type_safe:false e1 fi in
  let mem = plain_memory_var (mc,e1#region) in
  let ac = alloc_class_of_mem_class mc in
  let alloc = alloc_table_var (ac,e1#region) in
  let lets, e' =
    if safety_checking () then
      let p,off,lb,rb = destruct_pointer e1 in
      let p' = expr p in
      let i' = offset off in
      let letspi =
	[ (tmpp,p') ; (tmpi,i') ;
	  (tmp1,make_app "shift" [Var tmpp; Var tmpi])]
      in
      match off, lb, rb with
	| Int_offset s, Some lb, Some rb when bounded lb rb s ->
            let e1' = expr e1 in
	    [ (tmp1, e1') ],
            make_app "safe_upd_" [ mem; Var tmp1; Var tmp2 ]
	| Int_offset s, Some lb, _ when lbounded lb s ->
	    letspi,
            make_guarded_app ~mark IndexBounds pos "lsafe_lbound_upd_"
              [ alloc; mem; Var tmpp; Var tmpi; Var tmp2 ]
	| Int_offset s, _, Some rb when rbounded rb s ->
	    letspi,
            make_guarded_app ~mark IndexBounds pos "rsafe_rbound_upd_"
              [ alloc; mem; Var tmpp; Var tmpi; Var tmp2 ]
	| Int_offset s, None, None when s = 0 ->
	    [ (tmp1, p') ],
            make_guarded_app ~mark PointerDeref pos "upd_"
              [ alloc; mem ; Var tmp1; Var tmp2 ]
	| _ ->
	    letspi,
            make_guarded_app ~mark PointerDeref pos "offset_upd_"
              [ alloc; mem ; Var tmpp; Var tmpi; Var tmp2 ]
    else
      let e1' = expr e1 in
      [ (tmp1,e1') ],
      make_app "safe_upd_" [ mem; Var tmp1; Var tmp2 ]
  in
  tmp1, lets, e'
*)



let rec make_upd_simple mark pos e1 fi tmp2 =
  (* Temporary variables to avoid duplicating code *)
  let tmpp = tmp_var_name () in
(*
  eprintf "make_upd_simple: tmp_var_name for tmpp is %s@." tmpp;
*)
  let tmpi = tmp_var_name () in
(*
  eprintf "make_upd_simple: tmp_var_name for tmpi is %s@." tmpi;
*)
  let tmp1 = tmp_var_name () in
(*
  eprintf "make_upd_simple: tmp_var_name for tmp1 is %s@." tmp1;
*)
  (* Define memory and allocation table *)
  let mc,_ufi_opt = deref_mem_class ~type_safe:false e1 fi in
  let mem = match (plain_memory_var (mc,e1#region)).expr_node with
    | Var v -> v
    | _ -> assert false
  in
  let ac = alloc_class_of_mem_class mc in
(*
  let alloc_var = alloc_table_name (ac,e1#region) in
*)
  let alloc = alloc_table_var (ac,e1#region) in
  let is_ref,talloc = talloc_table_var ~label_in_name:true LabelHere (ac,e1#region) in
  let p,off,lb,rb = destruct_pointer e1 in
  let p' = expr p in
  let i' = offset off in
  let letspi =
    [ (tmpp,p') ; (tmpi,i') ;
      (tmp1,make_app "shift" [mk_var tmpp; mk_var tmpi])]
  in
  try
    let s,b1,b2 =
      match off, lb, rb with
        | Int_offset s, Some lb, Some rb when bounded lb rb s ->
            (*
              make_app "safe_upd_" [ mem; mk_var tmp1; mk_var tmp2 ]
            *)
            s,true,true
        | Int_offset s, Some lb, _ when lbounded lb s ->
	    (*
              make_guarded_app ~mark IndexBounds pos "lsafe_lbound_upd_"
              [ alloc; mem; mk_var tmpp; mk_var tmpi; mk_var tmp2 ]
            *)
            s, true, false
        | Int_offset s, _, Some rb when rbounded rb s ->
	    (*
              make_guarded_app ~mark IndexBounds pos "rsafe_rbound_upd_"
              [ alloc; mem; mk_var tmpp; mk_var tmpi; mk_var tmp2 ]
            *)
            s, false, true
              (*
	        | Int_offset s, None, None when int_of_string s = 0 ->
	        [ (tmp1, p') ],
              (*
                make_guarded_app ~mark PointerDeref pos "upd_"
                [ alloc; mem ; mk_var tmp1; mk_var tmp2 ]
              *)
                Upd(alloc, mem , mk_var tmp1, mk_var tmp2)
              *)
        | Int_offset s, None, None ->
	    (*
              make_guarded_app ~mark PointerDeref pos "upd_"
              [ alloc; mem ; mk_var tmp1; mk_var tmp2 ]
            *)
            s, false, false
        | _ ->
            raise Exit
    in
(*    Format.eprintf "found constant update let %s = %a in (%s + %d).%s = ...@." tmpp Output.fprintf_expr p' tmpp s mem;
*)
    let letspi = if s = 0 then [ (tmpp,p') ] else letspi in
    tmp1, [],
    mk_expr (MultiAssign(mark,pos,letspi, is_ref, talloc, alloc, tmpp, p', mem, [s, b1, b2, tmp2]))
 with Exit ->
   tmp1,letspi,
   if (safety_checking()) then
     make_guarded_app ~mark PointerDeref pos "offset_upd_"
	       [ alloc; mk_var mem ; mk_var tmpp; mk_var tmpi; mk_var tmp2 ]
   else
     make_app "safe_upd_" [ mk_var mem; mk_var tmp1; mk_var tmp2 ]


and make_upd_union mark pos off e1 fi tmp2 =
  let e1' = expr e1 in
  (* Convert value assigned into bitvector *)
  let e2' = match fi.jc_field_info_type with
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
    match fi.jc_field_info_bitsize with
      | Some x -> x / 8
      | None -> assert false
  in
  let union_size =
    (union_type e1#typ).jc_root_info_union_size_in_bytes
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
  let e2' = match fi.jc_field_info_type with
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
    match fi.jc_field_info_bitsize with
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
  let tmp2 = v2.jc_var_info_name in
  (* Dispatch depending on kind of memory *)
  let mc,ufi_opt = deref_mem_class ~type_safe:false e1 fi in
  match mc,ufi_opt with
    | JCmem_field fi', None ->
	assert (fi.jc_field_info_tag = fi'.jc_field_info_tag);
	make_upd_simple mark pos e1 fi tmp2
    | JCmem_field fi', Some ufi ->
	assert (fi.jc_field_info_tag = fi'.jc_field_info_tag);
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
    match fi.jc_field_info_bitsize with
      | Some x -> x / 8
      | None -> assert false
  in
  let off = string_of_int off and size = string_of_int size in
  let e' =
    make_app "extract_bytes" [ e'; mk_expr (Cte(Prim_int off)); mk_expr(Cte(Prim_int size)) ]
  in
  (* Convert bitvector into appropriate type *)
  match fi.jc_field_info_type with
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
    match fi.jc_field_info_bitsize with
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
  match fi.jc_field_info_type with
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
  let ty = vi.jc_var_info_type in
  let tmp = tmp_var_name() (* vi.jc_var_info_name *) in
  let e,a = type_assert tmp ty e in
  (tmp, e, a) :: lets , (mk_var tmp) :: params

and value_assigned mark pos ty e =
    let tmp = tmp_var_name () in
    let e,a = type_assert tmp ty e in
    if a <> LTrue && safety_checking() then
      mk_expr (Let(tmp,e,make_check ~mark ~kind:IndexBounds pos
            (mk_expr (Assert(`ASSERT,a,mk_var tmp)))))
    else e

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
        mk_expr (And(e1',e2'))
    | JCEbinary(e1,(`Blor,_),e2) ->
        let e1' = expr e1 in
        let e2' = expr e2 in
        (* lazy disjunction *)
        mk_expr (Or(e1',e2'))
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
          | _ -> make_app
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
        mk_expr (If(e1',e2',e3'))
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
    | JCEinstanceof(e1,st) ->
        let e1' = expr e1 in
        let tag = tag_table_var (struct_root st,e1#region) in
        (* always safe *)
        make_app "instanceof_" [ tag; e1'; mk_var(tag_name st) ]
    | JCEcast(e1,st) ->
        if struct_of_union st then
	  expr e1
	else
          let e1' = expr e1 in
          let tmp = tmp_var_name () in
(*
          eprintf "JCEcast: tmp_var_name for tmp is %s@." tmp;
*)
          let tag = tag_table_var (struct_root st,e1#region) in
	  let downcast_fun =
	    if safety_checking () then "downcast_" else "safe_downcast_"
	  in
          let call =
            make_guarded_app e#mark DownCast e#pos downcast_fun
	      [ tag; mk_var tmp; mk_var(tag_name st) ]
          in
          mk_expr (Let(tmp,e1',call)) (* Yannick: why a temporary here? *)
    | JCEbitwise_cast(e1,_st) ->
	expr e1
    | JCErange_cast(e1,ri) ->
        let e1' = expr e1 in
        coerce ~check_int_overflow:(safety_checking())
          e#mark e#pos (JCTenum ri) e1#typ e1 e1'
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
        let alloc = plain_alloc_table_var (ac,e#region) in
	let pc = JCtag(st,[]) in
	let args = alloc_arguments (ac,e#region) pc in
        if !Jc_options.inv_sem = InvOwnership then
          let tag = plain_tag_table_var (struct_root st,e#region) in
          let mut = mutable_name pc in
          let com = committed_name pc in
          make_app "alloc_parameter_ownership"
            [alloc; mk_var mut; mk_var com; tag; mk_var (tag_name st);
             coerce ~check_int_overflow:(safety_checking())
	       e1#mark e1#pos integer_type
	       e1#typ e1 e1']
	else
          make_guarded_app e#mark
            AllocSize e#pos
            (alloc_param_name ~check_size:(safety_checking()) ac pc)
            (coerce ~check_int_overflow:(safety_checking())
	       e1#mark e1#pos integer_type
	       e1#typ e1 e1'
             :: args)
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


    | JCEapp call ->
	begin match call.jc_call_fun with
          | JClogic_fun f ->
              let arg_types_asserts, args =
		try match f.jc_logic_info_parameters with
		  | [] -> [], []
		  | params ->
(*
		      let param_types =
			List.map (fun v -> v.jc_var_info_type) params
		      in
*)
		      List.fold_right2 list_type_assert
			params call.jc_call_args ([],[])
		with Invalid_argument _ -> assert false
              in
	      let param_assoc =
		List.map2 (fun param arg -> param,arg)
		  f.jc_logic_info_parameters call.jc_call_args
	      in
	      let with_body =
		try
                  let _f,body =
		    Hashtbl.find Jc_typing.logic_functions_table
		      f.jc_logic_info_tag
		  in
		  match body with
		    | JCTerm _ -> true
		    | JCNone | JCReads _ -> false
		    | JCAssertion _ | JCInductive _ -> assert false
                with Not_found -> false
	      in
	      let pre, fname, locals, prolog, epilog, args =
		make_arguments
                  ~callee_reads: f.jc_logic_info_effects
                  ~callee_writes: empty_effects
                  ~region_assoc: call.jc_call_region_assoc
		  ~param_assoc ~with_globals:true ~with_body
		  f.jc_logic_info_final_name args
	      in
	      assert (pre = LTrue);
	      assert (fname = f.jc_logic_info_final_name);
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
		try match f.jc_fun_info_parameters with
		  | [] -> [], []
		  | params ->
		      let params =
			List.map (fun (_,v) -> v) params
		      in
		      List.fold_right2 list_type_assert
			params call.jc_call_args ([],[])
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
		  ) call.jc_call_args args []
	      in
	      let param_assoc =
		List.map2 (fun (_,param) arg -> param,arg)
		  f.jc_fun_info_parameters call.jc_call_args
	      in
	      let fname =
		if safety_checking () then
		  f.jc_fun_info_final_name ^ "_requires"
		else f.jc_fun_info_final_name
	      in
	      let with_body =
		try
		  let _f,_loc,_s,body =
                    Hashtbl.find Jc_typing.functions_table f.jc_fun_info_tag
		  in
		  body <> None
                with Not_found ->
                  (*
                    eprintf "Fatal error: tag for %s not found@." f.jc_fun_info_name;
                    assert false
                  *)
                  false
	      in
	      let args =
		match f.jc_fun_info_builtin_treatment with
		  | TreatNothing -> args
		  | TreatGenFloat format ->
		      (mk_var (float_format format))::(current_rounding_mode ())::args
	      in
	      let pre, fname, locals, prolog, epilog, new_args =
		make_arguments
                  ~callee_reads: f.jc_fun_info_effects.jc_reads
                  ~callee_writes: f.jc_fun_info_effects.jc_writes
                  ~region_assoc: call.jc_call_region_assoc
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

	      let this_comp = f.jc_fun_info_component in
	      let current_comp = (get_current_function()).jc_fun_info_component in
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
                           vi.jc_var_info_name tmp;
*)
                         VarMap.add vi (LVar tmp) acc)
                      VarMap.empty f.jc_fun_info_parameters arg_types_asserts
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
                          match li.jc_logic_info_parameters with
                              v1::_ -> li.jc_logic_info_name,v1.jc_var_info_type
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
	let e1' = value_assigned e#mark e#pos v.jc_var_info_type e1 in
	let e' = mk_expr (Assign(v.jc_var_info_final_name,e1')) in
	if e#typ = Jc_pervasives.unit_type then
          begin
(*
            eprintf "JCEassign(%s,..) : has type unit@." v.jc_var_info_name;
*)
            e'
          end
        else
          begin
(*
            eprintf "JCEassign(%s,..) : DOES NOT have type unit@." v.jc_var_info_name;
*)
            append e' (var v)
          end
    | JCEassign_heap(e1,fi,e2) ->
	let e2' = value_assigned e#mark e#pos fi.jc_field_info_type e2 in
	(* Define temporary variable for value assigned *)
	let tmp2 = tmp_var_name () in
(*
        eprintf "JCEassign_heap: tmp_var_name for tmp2 is %s@." tmp2;
*)
	let v2 = Jc_pervasives.var fi.jc_field_info_type tmp2 in
	let e2 =
	  new expr_with ~typ:fi.jc_field_info_type ~node:(JCEvar v2) e2
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
                  { e' with expr_node =
                      MultiAssign(m,p,lets@lets',isrefa,ta,a,tmpe,e,f,l)}
              | _ ->
                  make_lets lets e'
          else
            make_lets lets (append e' (mk_var tmp2))
        in
        if !Jc_options.inv_sem = InvOwnership then
          append e' (assume_field_invariants fi)
        else e'

    | JCEblock el ->
        List.fold_right append (List.map expr el) void
    | JCElet(v,e1,e2) ->
        let e1' = match e1 with
          | None ->
              any_value v.jc_var_info_type
          | Some e1 ->
	      value_assigned e#mark e#pos v.jc_var_info_type e1
	in
	let e2' = expr e2 in
        if v.jc_var_info_assigned then
	  mk_expr (Let_ref(v.jc_var_info_final_name,e1',e2'))
        else
	  mk_expr (Let(v.jc_var_info_final_name,e1',e2'))
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
	    la.jc_loop_behaviors
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
	let free_inv = la.jc_free_loop_invariant in
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
		 match b.jc_behavior_assigns with
		   | None -> acc
		   | Some(_pos,loclist) ->
		       let loclist = List.map old_to_pre_loc loclist in
		       match acc with
			 | None -> Some loclist
			 | Some loclist' -> Some (loclist @ loclist')
	       else acc
	    ) None (s.jc_fun_default_behavior::s.jc_fun_behavior)
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
	    la.jc_loop_behaviors
	in

	let loop_label = fresh_loop_label() in

	let ass =
	  assigns ~type_safe:false
	    (LabelName loop_label) infunction.jc_fun_info_effects loop_assigns
	    e#pos
	in

	let ass_from_fun =
	  assigns ~type_safe:false
	    LabelPre infunction.jc_fun_info_effects loop_assigns_from_function
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
          match la.jc_loop_variant with
            | Some (t,r) when safety_checking () &&
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
                  | Some id -> variant, Some id.jc_logic_info_name
                in
                Some (variant,r)
            | None when safety_checking () &&
                !Jc_options.termination_policy = TPalways ->
                eprintf
                  "Warning, generating a dummy variant for loop. \
                   Please provide a real variant or set termination policy \
                   to user or never\n%!";
                Some (LConst(Prim_int "0"),None)
            | _ -> None
        in
(*
        eprintf "Jc_interp.expr: adding loop label %s@." loop_label.label_info_final_name;
*)
        make_label loop_label.label_info_final_name
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
	      assert (b.jc_behavior_throws = None);
	      assert (b.jc_behavior_assumes = None);
	      let a =
		assertion
		  ~type_safe:false ~global_assertion:false ~relocate:false
		  LabelHere LabelPre b.jc_behavior_ensures
	      in
              let post = match b.jc_behavior_assigns with
                | None -> a
                | Some(_,locs) ->
                    make_and a
	              (assigns ~type_safe:false
	                 LabelPre
                         ef (* infunction.jc_fun_info_effects*) (Some locs)
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
                  ~callee_reads:ef.jc_reads
                  ~callee_writes:ef.jc_writes ~params:[] ~region_list:[]
                in
                let _writes = write_effects 
                  ~callee_reads:ef.jc_reads
                  ~callee_writes:ef.jc_writes ~params:[] ~region_list:[]
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
                 Option_misc.map (fun v -> v.jc_var_info_final_name) v_opt,
                 expr st)),
             ExceptionSet.remove ei excs)
          else
            begin
(* YMo: too many questions about warning due to generated Jessie *)
(*               eprintf "Warning: exception %s cannot be thrown@." *)
(*                 ei.jc_exception_info_name; *)
              (s,excs)
            end
        in
        let ef = Jc_effect.expr empty_fun_effect s in
        let (s,_) =
          List.fold_left catch (expr s,ef.jc_raises) catches
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
      if e#original_type <> Jc_pervasives.unit_type then
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
  LPred("not_assigns",[talloc;LVarAtLabel(mem,"") ; LVar mem ; pset])





let rec finalize e =
  match e.expr_node with
    | Absurd | Void | Cte _ | Var _ | BlackBox _ | Assert _ | Triple _
    | Deref _
    | Raise(_, None)
        -> e
    | Loc (l, e1) -> {e with expr_node = Loc(l,finalize e1) }
(*
    | Label (l, e) -> Label(l,finalize e)
*)
    | Fun (_, _, _, _, _) -> assert false
    | Try (e1, exc, arg, e2) ->
        {e with expr_node = Try(finalize e1, exc, arg, finalize e2)}
    | Raise (id, Some e1) ->
        {e with expr_node = Raise(id, Some(finalize e1))}
    | App (e1, e2) ->
        {e with expr_node = App(finalize e1, finalize e2)}
    | Let_ref (x, e1, e2) ->
        {e with expr_node = Let_ref(x, finalize e1, finalize e2)}
    | Let (x, e1, e2) ->
        {e with expr_node = Let(x, finalize e1, finalize e2)}
    | Assign (x, e1) ->
        {e with expr_node = Assign(x, finalize e1) }
    | Block(l) ->
        {e with expr_node = Block(List.map finalize l) }
    | While (e1, inv, var, l) ->
        {e with expr_node = While(finalize e1, inv, var, List.map finalize l)}
    | If (e1, e2, e3) ->
        {e with expr_node = If(finalize e1, finalize e2, finalize e3)}
    | Not e1 ->
        {e with expr_node = Not(finalize e1)}
    | Or (e1, e2) ->
        {e with expr_node = Or(finalize e1, finalize e2) }
    | And (e1, e2) ->
        {e with expr_node = And(finalize e1, finalize e2) }
    | MultiAssign(mark,pos,lets,isrefalloc,talloc,alloc,tmpe,_e,mem,l) ->
(*
        eprintf "finalizing a MultiAssign@.";
*)
        match l with
          | [] -> assert false
          | [(i,b1,b2,e')] ->
              if i=0 then
                 make_lets lets
                   (make_old_style_update_no_shift ~mark ~pos alloc tmpe mem b1 b2 e')
              else
                let tmpshift = tmp_var_name () in
(*
                eprintf "Jc_interp.finalize: tmp_var_name for tmpshift is %s@." tmpshift;
*)
                let i = Prim_int (string_of_int i) in
                make_lets lets
                  (make_lets [tmpshift,make_app "shift" [mk_var tmpe; mk_expr (Cte i)]]
                     (make_old_style_update ~mark ~pos alloc tmpe tmpshift mem i b1 b2 e'))
          | _ ->
              let pre =
                if safety_checking() then
                  make_and_list
                    (List.fold_left
                       (fun acc (i,b1,b2,_) ->
                          (* valid e+i *)
                          let i = LConst (Prim_int (string_of_int i)) in
                          (if b1 then LTrue else
                             (* offset_min(alloc,e) <= i *)
	                     LPred ("le_int",
		                    [LApp("offset_min",
                                          [talloc; LVar tmpe]);
                                     i])) ::
                            (if b2 then LTrue else
                               (* i <= offset_max(alloc,e) *)
	                       LPred ("le_int",
		                      [i ;
                                       LApp("offset_max",
                                            [talloc; LVar tmpe])]))
                          ::acc
                       )
                       []
                       l)
                else LTrue
              in
              let post =
                (* TODO ! generer le not_assigns !!!! *)
                make_and_list
                  (make_not_assigns talloc mem tmpe l ::
                     List.map
                     (fun (i,_,_,e') ->
                        (* (e+i).f == e' *)
                        LPred("eq",
                              [ LApp("select",
                                     [ LVar mem;
                                       LApp("shift",
                                            [ LVar tmpe ; LConst (Prim_int (string_of_int i))] )]);
                                LVar e'])) l)
              in
              let reads = if isrefalloc then
                match talloc with
                  | LVar v -> [v;mem]
                  | _ -> assert false
              else
                [mem]
              in
              make_lets lets
                (mk_expr (BlackBox (Annot_type(pre,unit_type,reads,[mem],post,[]))))


let expr e = finalize (expr e)


(*****************************)
(* axioms, lemmas, goals   *)
(**************************)

let tr_axiom loc id ~is_axiom labels a acc =

  if Jc_options.debug then
    Format.printf "[interp] axiom %s@." id;

  let lab = match labels with [lab] -> lab | _ -> LabelHere in
  let ef = Jc_effect.assertion empty_effects a in
  let a' =
    assertion ~type_safe:false ~global_assertion:true ~relocate:false lab lab a
  in
  let params = tmodel_parameters ~label_in_name:true ef in
  let new_id = get_unique_name id in
  reg_decl
    ~out_mark:new_id
    ~in_mark:id
    ~name:id
    ~beh:(if is_axiom then "axiom" else "lemma")
    loc;
  let a' = List.fold_right (fun (n,_v,ty') a' -> LForall(n,ty',[],a')) params a' in
  if is_axiom then
    Axiom(new_id,a') :: acc
  else
    Goal(new_id,a') :: Axiom(new_id ^ "_as_axiom",a') :: acc




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
	     if exc.jc_exception_info_tag = exc'.jc_exception_info_tag then
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
  match b.jc_behavior_assumes with
    | None -> pre
    | Some a ->
	let a' =
	  assertion ~type_safe:false ~global_assertion:false ~relocate:false
	    LabelHere LabelHere a
	in
	make_and a' pre

(* Only used for external prototype, hence type-safe parameter set to true *)
let assume_in_postcondition b post =
  match b.jc_behavior_assumes with
    | None -> post
    | Some a ->
	let a' =
	  assertion ~type_safe:true ~global_assertion:false ~relocate:true
	    LabelOld LabelOld a
	in
	make_impl a' post

let function_prototypes = Hashtbl.create 0

let get_valid_pred_app vi =
  match vi.jc_var_info_type with
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
		  make_valid_pred_app ~equal:false
		    (ac, vi.jc_var_info_region) pc
                    v' (Some (const_of_num n)) None
                in
		  bind_pattern_lets a'
	    | None, Some n ->
		let ac = alloc_class_of_pointer_class pc in
                let a' =
		  make_valid_pred_app ~equal:false
		    (ac, vi.jc_var_info_region) pc
                    v' None (Some (const_of_num n))
                in
		  bind_pattern_lets a'
            | Some n1, Some n2 ->
		let ac = alloc_class_of_pointer_class pc in
                let a' =
		  make_valid_pred_app ~equal:false (ac, vi.jc_var_info_region) pc
                    v' (Some (const_of_num n1)) (Some (const_of_num n2))
                in
		  bind_pattern_lets a'
	  end
    | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull | JCTany
    | JCTtype_var _ -> LTrue


let pre_tr_fun f _funpos spec _body acc =
  begin
    match spec.jc_fun_decreases with
      | None -> ()
      | Some(t,r) ->
	  Hashtbl.add decreases_clause_table f.jc_fun_info_tag (t,r)
  end;
  acc


let tr_fun f funpos spec body acc =

  if Jc_options.debug then
    Format.printf "[interp] function %s@." f.jc_fun_info_name;

  Jc_options.lprintf "Jc_interp: function %s@." f.jc_fun_info_name;
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
      LabelHere LabelHere spec.jc_fun_requires
  in
  let external_requires =
    if Jc_options.trust_ai then
      external_requires
    else
      let free_requires =
	named_assertion ~type_safe:true ~global_assertion:false ~relocate:false
	  LabelHere LabelHere spec.jc_fun_free_requires
      in
	make_and external_requires free_requires
  in

  let internal_requires =
    named_assertion ~type_safe:false ~global_assertion:false ~relocate:false
      LabelHere LabelHere spec.jc_fun_requires
  in
  let free_requires =
    named_assertion ~type_safe:false ~global_assertion:false ~relocate:false
      LabelHere LabelHere spec.jc_fun_free_requires
  in
  let free_requires = make_and variables_valid_pred_apps free_requires in
  let internal_requires = make_and internal_requires free_requires in
  let internal_requires =
    List.fold_left
      (fun acc (_,v) ->
         let req = get_valid_pred_app v in
	   make_and req acc)
      internal_requires f.jc_fun_info_parameters
  in


  (* partition behaviors as follows:
     - (optional) 'safety' behavior (if Arguments Invariant Policy is selected)
     - (optional) 'inferred' behaviors (computed by analysis)
     - user defined behaviors *)

  let behaviors = spec.jc_fun_default_behavior :: spec.jc_fun_behavior in
  let (safety_behavior,
       normal_behaviors_inferred, normal_behaviors,
       excep_behaviors_inferred, excep_behaviors) =
    List.fold_left
      (fun (safety,normal_inferred,normal,excep_inferred,excep) (pos,id,b) ->
	 let make_post ~type_safe ~internal =
	   let post =
	     if internal && Jc_options.trust_ai then
	       b.jc_behavior_ensures
	     else
	       Assertion.mkand [ b.jc_behavior_ensures;
				 b.jc_behavior_free_ensures ] ()
	   in
	   let post =
	     named_assertion
	       ~type_safe ~global_assertion:false ~relocate:false
	       LabelPost LabelOld post
	   in
           let post = match b.jc_behavior_assigns with
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
                     (assigns ~type_safe
			~region_list:f.jc_fun_info_param_regions
			LabelOld f.jc_fun_info_effects (Some loclist) funpos)
		 in
		 mark_assertion pos (make_and post assigns_post)
	   in post
	 in
	 let internal_post = make_post ~type_safe:false ~internal:true in
	 let external_post = make_post ~type_safe:true ~internal:false in
	 let behav = (id,b,internal_post,external_post) in
         match b.jc_behavior_throws with
           | None ->
               begin match id with
                 | "safety" ->
		     assert (b.jc_behavior_assumes = None);
		     let internal_post =
		       make_and variables_valid_pred_apps internal_post
		     in
		     let external_post =
		       make_and variables_valid_pred_apps external_post
		     in
                     (id, b, internal_post, external_post) :: safety,
                     normal_inferred, normal, excep_inferred, excep
                 | "inferred" ->
		     assert (b.jc_behavior_assumes = None);
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
		   assert (b.jc_behavior_assumes = None);
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
                 jc_behavior_throws = Some exc;
		 jc_behavior_ensures = (new assertion JCAtrue); }
           in
           ExceptionMap.add
	     exc [exc.jc_exception_info_name ^ "_b", b, LTrue, LTrue] acc)
      f.jc_fun_info_effects.jc_raises
      excep_behaviors
  in

  (* Effects, parameters and locals *)

  let params = List.map snd f.jc_fun_info_parameters in

  let external_write_effects =
    write_effects
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
      ~params
  in
  let external_read_effects =
    read_effects
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
      ~params
  in
  let external_write_params =
    write_parameters
      ~type_safe:true
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
      ~params
  in
  let internal_write_params =
    write_parameters
      ~type_safe:false
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
      ~params
  in
  let external_read_params =
    read_parameters
      ~type_safe:true
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
      ~params
      ~already_used:(List.map fst external_write_params)
  in
  let internal_read_params =
    read_parameters
      ~type_safe:false
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
      ~params
      ~already_used:(List.map fst internal_write_params)
  in
  let internal_write_locals =
    write_locals
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
      ~params
  in
  let internal_read_locals =
    read_locals
      ~callee_reads:f.jc_fun_info_effects.jc_reads
      ~callee_writes:f.jc_fun_info_effects.jc_writes
      ~region_list:f.jc_fun_info_param_regions
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

  let ret_type = tr_var_type f.jc_fun_info_result in
  let fparams = List.map snd f.jc_fun_info_parameters in
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
    let newid = f.jc_fun_info_final_name ^ "_requires" in
    Hashtbl.add function_prototypes newid fun_type;
    Param(false, newid, fun_type) :: acc
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
    let newid = f.jc_fun_info_final_name in
    Hashtbl.add function_prototypes newid fun_type;
    Param(false, newid, fun_type) :: acc
  in

  (* Function body *)

  match body with
    | None -> acc (* function was only declared *)
    | Some body ->
        if Jc_options.verify <> [] &&
          not (List.mem f.jc_fun_info_name Jc_options.verify)
        then
          acc (* function is not in the list of functions to verify *)
        else
          let () =
	    printf "Generating Why function %s@." f.jc_fun_info_final_name
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
		   if id.jc_var_info_assigned
		   then
		     let n = id.jc_var_info_final_name in
		     let newn = "mutable_" ^ n in
		     id.jc_var_info_final_name <- newn;
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
	    let body = match f.jc_fun_info_result.jc_var_info_type with
	      | JCTnative Tunit ->
		  mk_expr (Try(append body (mk_expr (Raise(jessie_return_exception,None))),
		               jessie_return_exception, None, void))
	      | _ ->
		  let e' = any_value f.jc_fun_info_result.jc_var_info_type in
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
		 let n = v.jc_var_info_final_name in
		 if List.mem_assoc n list_of_refs then
		   v.jc_var_info_final_name <- List.assoc n list_of_refs
	      ) fparams;
	    body
	  in

          (* safety behavior *)
	  let acc =
	    if Jc_options.verify_behavior "safety" then
              let safety_body = wrap_body f spec "safety" body in
              let newid = f.jc_fun_info_name ^ "_safety" in
              reg_decl
		~out_mark:newid
		~in_mark:f.jc_fun_info_name
		~name:("function " ^ f.jc_fun_info_name)
		~beh:"Safety"
		funpos;
              if is_purely_exceptional_fun spec then acc else
		if Jc_options.verify_invariants_only then acc else
                  Def(
                    newid,
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
                   let newid = f.jc_fun_info_name ^ "_ensures_" ^ id in
                   let beh =
                     if id="default" then "Default behavior" else
		       "Normal behavior `"^id^"'"
                   in
                   reg_decl
                     ~out_mark:newid
                     ~in_mark:f.jc_fun_info_name
                     ~name:("function " ^ f.jc_fun_info_name)
                     ~beh
                     funpos;
                   Def(
                     newid,
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
                        let newid = f.jc_fun_info_name ^ "_exsures_" ^ id in
                        reg_decl
                          ~out_mark:newid
                          ~in_mark:f.jc_fun_info_name
                          ~name:("function " ^ f.jc_fun_info_name)
                          ~beh:("Exceptional behavior `" ^ id ^ "'")
                          funpos;
                        Def(newid,
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
      | LVarAtLabel(id,l) ->
	  let id = StringMap.find_or_default id id param_name_assoc in
	  LVarAtLabel(id,l)
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
  Param(false, n, new_fun_type) :: acc


(******************************************************************************)
(*                               Logic entities                               *)
(******************************************************************************)

let tr_logic_type (id,l) acc = Type(id,List.map Jc_type_var.name l) :: acc


let tr_exception ei acc =
  Jc_options.lprintf "producing exception '%s'@." ei.jc_exception_info_name;
  let typ = match ei.jc_exception_info_type with
    | Some tei -> Some (tr_base_type tei)
    | None -> None
  in
  Exception(exception_name ei, typ) :: acc

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
  Num.add_num (Num.sub_num ri.jc_enum_info_max ri.jc_enum_info_min) (Num.Int 1)

let tr_enum_type ri (* to_int of_int *) acc =
  let name = ri.jc_enum_info_name in
  let min = Num.string_of_num ri.jc_enum_info_min in
  let max = Num.string_of_num ri.jc_enum_info_max in
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
      [Logic(false,logic_bitvector_of_enum ri,["",lt],bitvector_type) ;
       Logic(false,logic_enum_of_bitvector ri,["",bitvector_type],lt) ;
       Axiom((logic_enum_of_bitvector ri)^"_of_"^(logic_bitvector_of_enum ri),
	   LForall("x",lt, [],
		   LPred(equality_op_for_type (JCTenum ri),
                         [LApp(logic_enum_of_bitvector ri,
                               [LApp(logic_bitvector_of_enum ri,
                                     [LVar "x"])]);
                          LVar "x"])));
       Axiom((logic_bitvector_of_enum ri)^"_of_"^(logic_enum_of_bitvector ri),
	   LForall("x",bitvector_type, [],
		   LPred("eq", (* TODO: equality for bitvectors ? *)
                         [LApp(logic_bitvector_of_enum ri,
                               [LApp(logic_enum_of_bitvector ri,
                                     [LVar "x"])]);
                          LVar "x"]))) ]
    else []
  in
  Type(name,[])
  :: Logic(false,logic_int_of_enum ri,
           [("",lt)],why_integer_type)
  :: Logic(false,logic_enum_of_int ri,
           [("",why_integer_type)],lt)
  :: Predicate(false,eq_of_enum ri,[("x",lt);("y",lt)],
               LPred("eq_int",[LApp(logic_int_of_enum ri,[LVar "x"]);
                               LApp(logic_int_of_enum ri,[LVar "y"])]))
  :: (if !Jc_options.int_model = IMmodulo then
        let width = LConst (Prim_int width) in
        let fmod t = LApp (mod_of_enum ri, [t]) in
        [Logic (false, mod_of_enum ri,
                ["x", simple_logic_type "int"], simple_logic_type "int");
         Axiom (name ^ "_mod_def",
                LForall ("x", simple_logic_type "int", [],
                         LPred ("eq_int", [LApp (mod_of_enum ri, [LVar "x"]);
                                           LApp (logic_int_of_enum ri,
                                                 [LApp (logic_enum_of_int ri,
                                                        [LVar "x"])])])));
         Axiom (name ^ "_mod_lb",
                LForall ("x", simple_logic_type "int", [],
                         LPred ("ge_int", [LApp (mod_of_enum ri, [LVar "x"]);
                                           LConst (Prim_int min)])));
         Axiom (name ^ "_mod_gb",
                LForall ("x", simple_logic_type "int", [],
                         LPred ("le_int", [LApp (mod_of_enum ri, [LVar "x"]);
                                           LConst (Prim_int max)])));
         Axiom (name ^ "_mod_id",
                LForall ("x", simple_logic_type "int", [],
                         LImpl (in_bounds (LVar "x"),
                                LPred ("eq_int", [LApp (mod_of_enum ri,
                                                        [LVar "x"]);
                                                  LVar "x"]))));
         Axiom (name ^ "_mod_lt",
                LForall ("x", simple_logic_type "int", [],
                         LImpl (LPred ("lt_int", [LVar "x";
                                                  LConst (Prim_int min)]),
                                LPred ("eq_int", [fmod (LVar "x");
                                                  fmod (LApp ("add_int",
                                                              [LVar "x";
                                                               width]))]))));
         Axiom (name ^ "_mod_gt",
                LForall ("x", simple_logic_type "int", [],
                         LImpl (LPred ("gt_int", [LVar "x";
                                                  LConst (Prim_int max)]),
                                LPred ("eq_int", [fmod (LVar "x");
                                                  fmod (LApp ("sub_int",
                                                              [LVar "x";
                                                               width]))]))));
        ]
      else [])
  @ Param(false,fun_enum_of_int ri,of_int_type)
  :: Param(false,safe_fun_enum_of_int ri,safe_of_int_type)
  :: Param(false,fun_any_enum ri,any_type)
  :: Axiom(name^"_range",
           LForall("x",lt, [],in_bounds
                     (LApp(logic_int_of_enum ri,[LVar "x"]))))
  :: Axiom(name^"_coerce",
           LForall("x",why_integer_type, [],
                   LImpl(in_bounds (LVar "x"),
                         LPred("eq_int",
                               [LApp(logic_int_of_enum ri,
                                     [LApp(logic_enum_of_int ri,
                                           [LVar "x"])]) ;
                                LVar "x"]))))
  :: bv_conv
  @ acc

let tr_enum_type_pair ri1 ri2 acc =
  (* Information from first enum *)
  let name1 = ri1.jc_enum_info_name in
  let min1 = ri1.jc_enum_info_min in
  let max1 = ri1.jc_enum_info_max in
  (* Information from second enum *)
  let name2 = ri2.jc_enum_info_name in
  let min2 = ri2.jc_enum_info_min in
  let max2 = ri2.jc_enum_info_max in
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
        Axiom(smallname ^ "_" ^ bigname ^ "_mod_coincide",
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
  if vi.jc_var_info_assigned then
    let t = Ref_type(tr_var_type vi) in
      Param(false,vi.jc_var_info_final_name,t)::acc
  else
    let t = tr_base_type vi.jc_var_info_type in
      Logic(false,vi.jc_var_info_final_name,[],t)::acc

let tr_region r acc =
  Type(r.jc_reg_final_name,[]) :: acc

let tr_memory (mc,r) acc =
  Param(
    false,memory_name(mc,r),
    Ref_type(Base_type(memory_type mc))) :: acc

let tr_alloc_table (pc,r) acc =
  Param(
    false,alloc_table_name(pc,r),
    Ref_type(Base_type(alloc_table_type pc))) :: acc

let tr_tag_table (rt,r) acc =
  Param(
    false,tag_table_name(rt,r),
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
            Param(false,union_memory_name rt,Ref_type(Base_type mem)) :: acc
      in
	(* Validity parameters *)
	make_valid_pred ~equal:true ac pc
	:: make_valid_pred ~equal:false ac pc
	:: make_valid_pred ~equal:false ~right:false ac pc
	:: make_valid_pred ~equal:false ~left:false ac pc
        :: make_valid_pred ~equal:false (* TODO ? *) JCalloc_bitvector pc
	  (* Allocation parameter *)
	:: make_alloc_param ~check_size:true ac pc
	:: make_alloc_param ~check_size:false ac pc
	:: make_alloc_param ~check_size:true JCalloc_bitvector pc
	:: make_alloc_param ~check_size:false JCalloc_bitvector pc
	:: acc
    else
      make_valid_pred ~equal:true ac pc :: make_valid_pred ~equal:false ac pc :: acc
  in
  let of_ptr_addr =
    Logic(false, of_pointer_address_name rt,
	  [ ("",raw_pointer_type why_unit_type) ], pointer_type ac pc)
  in
  let addr_axiom =
    let p = "p" in
    Axiom("pointer_addr_of_" ^ (of_pointer_address_name rt),
	  LForall(p, raw_pointer_type why_unit_type, [],
		  make_eq_pred (JCTpointer(pc,None,None))
		    (LVar p)
		    (LApp("pointer_address",
			  [ LApp(of_pointer_address_name rt,
				 [ LVar p ])]))))
  in
  let rev_addr_axiom =
    let p = "p" in
    Axiom((of_pointer_address_name rt) ^ "_of_pointer_addr",
	  LForall(p, pointer_type ac pc, [],
		  make_eq_pred (JCTpointer(pc,None,None))
		    (LVar p)
		    (LApp(of_pointer_address_name rt,
			  [ LApp("pointer_address",
				 [ LVar p ])]))))
  in
  let lt = tr_base_type (JCTpointer(pc,None,None)) in
  let conv =
    if !Region.some_bitwise_region then
    [Logic(false,logic_bitvector_of_variant rt,["",lt],bitvector_type);
     Logic(false,logic_variant_of_bitvector rt,["",bitvector_type],lt);
     Axiom((logic_variant_of_bitvector rt)^"_of_"^(logic_bitvector_of_variant rt),
	   LForall("x",lt, [],
		   LPred(equality_op_for_type (JCTpointer (pc,None,None)),
                         [LApp(logic_variant_of_bitvector rt,
			       [LApp(logic_bitvector_of_variant rt,
                                     [LVar "x"])]);
                          LVar "x"])));
     Axiom((logic_bitvector_of_variant rt)^"_of_"^(logic_variant_of_bitvector rt),
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
      variant_tag_table_name rt,
      Ref_type(
        Base_type {
          logic_type_name = tag_table_type_name;
          logic_type_args = [root_model_type rt];
        }))
  in
  let alloc_table =
    Param(
      false,
      variant_alloc_table_name rt,
      Ref_type(
        Base_type {
          logic_type_name = alloc_table_type_name;
          logic_type_args = [root_model_type rt];
        }))
  in
  let type_def = Type(root_type_name rt, []) in
  (* Axiom: the variant can only have the given tags *)
  let axiom_variant_has_tag =
    let v = "x" in
    let tag_table = generic_tag_table_name rt in
    Axiom(
      variant_axiom_on_tags_name rt,
      LForall(
        v,
        pointer_type ac pc, [],
        LForall(
          tag_table,
          tag_table_type rt, [],
          make_or_list
            (List.map
               (make_instanceof (LVar tag_table) (LVar v))
               rt.jc_root_info_hroots)
      )))
  in
  (* Axioms: int_of_tag(T1) = 1, ... *)
  let (acc, _) = List.fold_left
    (fun (acc, index) st ->
       let axiom =
         Axiom(
           axiom_int_of_tag_name st,
           make_eq
             (make_int_of_tag st)
             (LConst(Prim_int(string_of_int index)))
         )
       in axiom::acc, index+1)
    (acc, 1)
    rt.jc_root_info_hroots
  in
  let acc =
    type_def::alloc_table::tag_table::axiom_variant_has_tag
    :: of_ptr_addr :: addr_axiom :: rev_addr_axiom
    :: conv @ acc
  in
  acc

(*
  Local Variables:
  compile-command: "unset LANG; make -j -C .. bin/jessie.byte"
  End:
*)
