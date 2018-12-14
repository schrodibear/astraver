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
open Extlib

(* Import from Why *)
open Jc.Constructors
open Jc.Ast
open Jc.Env
open! Jc.Common

(* Utility functions *)
open! Common
open! Jessie_integer

(*****************************************************************************)
(* Smart constructors.                                                       *)
(*****************************************************************************)

let mktype tnode = new ptype tnode

let mkexpr enode pos = new pexpr ~pos enode

let null_expr = mkexpr (JCPEconst JCCnull) Why_loc.dummy_position
let true_expr = mkexpr (JCPEconst(JCCboolean true)) Why_loc.dummy_position
let false_expr = mkexpr (JCPEconst(JCCboolean false)) Why_loc.dummy_position
let zero_expr = mkexpr (JCPEconst(JCCinteger "0")) Why_loc.dummy_position
let one_expr = mkexpr (JCPEconst(JCCinteger "1")) Why_loc.dummy_position

let mktag tag_node pos = new ptag ~pos tag_node

let mkidentifier name pos = new identifier ~pos name

let rec mkconjunct elist pos =
  match elist with
    | [] -> true_expr
    | [e] -> e
    | e::el -> mkexpr (JCPEbinary(e,`Bland,mkconjunct el pos)) pos

let rec mkdisjunct elist pos =
  match elist with
    | [] -> false_expr
    | [e] -> e
    | e::el -> mkexpr (JCPEbinary(e,`Blor,mkdisjunct el pos)) pos

let mkimplies antec conseq pos =
  match antec, conseq with
  | _, [] -> true_expr
  | [], _ -> mkconjunct conseq pos
  | _ -> mkexpr (JCPEbinary (mkconjunct antec pos, `Bimplies, mkconjunct conseq pos)) pos

let mkdecl dnode pos = new decl ~pos dnode

(*****************************************************************************)
(* Locate Jessie expressions on source program.                              *)
(*****************************************************************************)

let reg_position ?id ?kind:_ ?name pos =
  Jc.Print.jc_reg_pos "_C" ?id ?name (Why_loc.extract pos)

(* [locate] should be called on every Jessie expression which we would like to
 * locate in the original source program.
*)
let locate ?pos e =
  (* Recursively label conjuncts so that splitting conjuncts in Why still
   * allows to locate the resulting VC.
  *)
  let rec dopos ~toplevel e =
    (* Generate (and store) a label associated to this source location *)
    let pos =
      match pos with
      | None -> e#pos
      | Some pos ->
        if Location.is_unknown e#pos then pos else e#pos
    in
    (* Don't register unknown locations *)
    if not (Location.is_unknown pos) then
      let lab = reg_position pos in
      let e =
        match e#node with
        | JCPEbinary (e1, `Bland, e2) ->
          begin match e1#node, e2#node with
          | JCPElabel _, JCPElabel _ -> e (* already labelled *)
          | JCPElabel _, _ -> (* [e1] already labelled *)
            let e2 = dopos ~toplevel:false e2 in
            mkexpr (JCPEbinary (e1, `Bland, e2)) pos
          | _, JCPElabel _ -> (* [e2] already labelled *)
            let e1 = dopos ~toplevel:false e1 in
            mkexpr (JCPEbinary (e1, `Bland, e2)) pos
          | _,_ -> (* none already labelled *)
            let e1 = dopos ~toplevel:false e1 in
            let e2 = dopos ~toplevel:false e2 in
            mkexpr (JCPEbinary (e1, `Bland, e2)) pos
          end
        | _ -> e
      in
      (* Do not generate a label for every intermediate conjunct *)
      match e#node with
      | JCPEbinary (_e1,`Bland,_e2) when not toplevel -> e
      | _ ->
        (* Label the expression accordingly *)
        mkexpr (JCPElabel (lab, e)) pos
    else
      e
  in
  dopos ~toplevel:true e

(*****************************************************************************)
(* Cil to Jessie translation of operators                                    *)
(*****************************************************************************)

let unop = function
  | Neg Check -> `Uminus
  | Neg Modulo -> `Uminus_mod
  | BNot -> `Ubw_not
  | LNot -> `Unot

let binop = function
  | PlusA Check -> `Badd
  | PlusA Modulo -> `Badd_mod
  | PlusPI -> `Badd
  | IndexPI -> `Badd
  | MinusA Check -> `Bsub
  | MinusA Modulo -> `Bsub_mod
  | MinusPI -> `Bsub
  | MinusPP -> `Bsub
  | Mult Check -> `Bmul
  | Mult Modulo -> `Bmul_mod
  | Div Check -> `Bdiv
  | Div Modulo -> `Bdiv_mod
  | Mod Check-> `Bmod
  | Mod Modulo -> `Bmod_mod
  | Shiftlt Check -> `Bshift_left
  | Shiftlt Modulo -> `Bshift_left_mod
  | Shiftrt -> assert false (* Should be decided at point used *)
  | Lt -> `Blt
  | Gt -> `Bgt
  | Le -> `Ble
  | Ge -> `Bge
  | Eq -> `Beq
  | Ne -> `Bneq
  | BAnd -> `Bbw_and
  | BXor -> `Bbw_xor
  | BOr -> `Bbw_or
  | LAnd -> `Bland
  | LOr -> `Blor

let relation = function
  | Rlt -> `Blt
  | Rgt -> `Bgt
  | Rle -> `Ble
  | Rge -> `Bge
  | Req -> `Beq
  | Rneq -> `Bneq

let float_model = ref `Defensive

let rec name_with_profile s prof =
  match prof with
  | [] -> s
  | v :: rem ->
    let n = Name.logic_type v.lv_type in
    name_with_profile (s^"_"^n) rem

let translated_names_table = Hashtbl.create 257

exception CtePredicate of bool

let full_model_function linfo name default =
  match !float_model with
  | `Math ->
    Console.warning "\\%s always %b in mode JessieFloatModel(math)" name default;
    raise (CtePredicate default)
  | `Defensive | `Full | `Multirounding ->
    begin match (List.hd linfo.l_profile).lv_type with
    | Ctype x when x == doubleType -> "\\double_" ^ name
    | Ctype x when x == floatType -> "\\single_" ^ name
    | _ -> assert false
    end

let jessie_builtins = Hashtbl.create 17

let translated_name linfo largs =
  try
    let n = Hashtbl.find translated_names_table linfo.l_var_info.lv_id in
    n
  with
  | Not_found ->
    let name =
      match linfo.l_var_info.lv_name with
      | "\\abs" ->
        begin match linfo.l_type with
        | Some Lreal -> "\\real_abs"
        | Some Linteger -> "\\integer_abs"
        | _ -> assert false
        end
      | "\\min" ->
        begin match linfo.l_type with
        | Some Lreal -> "\\real_min"
        | Some Linteger -> "\\integer_min"
        | _ -> assert false
        end
      | "\\max" ->
        begin match linfo.l_type with
        | Some Lreal -> "\\real_max"
        | Some Linteger -> "\\integer_max"
        | _ -> assert false
        end
      | "\\exact" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\double_exact"
        | Ctype x when x == floatType -> "\\single_exact"
        | _ -> assert false
        end
      | "\\model" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\double_model"
        | Ctype x when x == floatType -> "\\single_model"
        | _ -> assert false
        end
      | "\\round_float" ->
        begin match (List.hd largs).term_node with
        | TDataCons (ctor, _args) ->
          begin
            match ctor.ctor_name with
            | "\\Double" -> "\\round_double"
            | "\\Single" -> "\\round_single"
            | s ->
              Console.unsupported "first arg '%s' of \\round_float unsupported (should be \\Double or \\Single)" s
          end
        | _ -> assert false
        end
      | "\\round_error" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\double_round_error"
        | Ctype x when x == floatType -> "\\single_round_error"
        | _ -> assert false
        end
      | "\\total_error" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\double_total_error"
        | Ctype x when x == floatType -> "\\single_total_error"
        | _ -> assert false
        end
      | "\\relative_error" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\double_relative_error"
        | Ctype x when x == floatType -> "\\single_relative_error"
        | _ -> assert false
        end
      | "\\pow" ->
        begin match linfo.l_type with
        | Some Lreal -> "\\real_pow"
        | _ -> assert false
        end
      | "\\sqrt" ->
        begin match linfo.l_type with
        | Some Lreal -> "\\real_sqrt"
        | _ -> assert false
        end
      | "\\sign" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\double_sign"
        | Ctype x when x == floatType -> "\\single_sign"
        | _ -> assert false
        end
      | "\\is_finite" ->
        full_model_function linfo "is_finite" true
      | "\\is_infinite" ->
        full_model_function linfo "is_infinite" false
      | "\\is_NaN" ->
        full_model_function linfo "is_NaN" false
      | "\\is_minus_infinity" ->
        full_model_function linfo "is_minus_infinity" false
      | "\\is_plus_infinity" ->
        full_model_function linfo "is_plus_infinity" false
      | "\\le_float" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\le_double"
        | Ctype x when x == floatType -> "\\le_single"
        | _ -> assert false
        end
      | "\\lt_float" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\lt_double"
        | Ctype x when x == floatType -> "\\lt_single"
        | _ -> assert false
        end
      | "\\ge_float" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\ge_double"
        | Ctype x when x == floatType -> "\\ge_single"
        | _ -> assert false
        end
      | "\\gt_float" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\gt_double"
        | Ctype x when x == floatType -> "\\gt_single"
        | _ -> assert false
        end
      | "\\eq_float" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\eq_double"
        | Ctype x when x == floatType -> "\\eq_single"
        | _ -> assert false
        end
      | "\\ne_float" ->
        begin match (List.hd linfo.l_profile).lv_type with
        | Ctype x when x == doubleType -> "\\ne_double"
        | Ctype x when x == floatType -> "\\ne_single"
        | _ -> assert false
        end
      | s ->
        try
          Hashtbl.find jessie_builtins s
        with
        | Not_found ->
          try
            let x = Hashtbl.find Rewrite.logic_names_overloading s in
            if !x then
              let ns = name_with_profile s linfo.l_profile in
              ns
            else begin
              s
            end
          with
          | Not_found ->
            s
    in
    Hashtbl.add translated_names_table linfo.l_var_info.lv_id name;
    name

(*****************************************************************************)
(* Cil to Jessie translation of types                                        *)
(*****************************************************************************)

let type_of_padding = mktype (JCPTidentifier (Name.Logic_type.padding, []))

let type_conversion_table = Hashtbl.create 0

let ctype ?bitsize ty =
  let tnode =
    match unrollType ty with
    | TVoid _attr -> JCPTnative Tunit
    | TInt (_ik, _attr) ->
      JCPTidentifier (Type.Integral.(name ?bitsize @@ of_typ_exn ty), [])
    | TFloat (fk, _attr) ->
      begin match !float_model with
      | `Math ->
        (* Mode "math": floats interpreted as reals *)
        JCPTnative Treal
      | `Defensive | `Full | `Multirounding ->
        begin match fk with
        | FFloat -> JCPTnative (Tgenfloat `Float)
        | FDouble -> JCPTnative (Tgenfloat `Double)
        | FLongDouble ->
          Console.unsupported "Jessie does not handle long double yet"
        end
      end
    | TPtr (_elemty, _attr) ->
      begin match Type.Ref.of_typ ty with
      | Some ty ->
        (* Do not use [_elemty] directly but rather [pointed_type ty] in order
         * to get to the array element in references, i.e. pointers to arrays.
        *)
        begin match unrollType (Type.Ref.typ ty) with
        | TComp (compinfo, _, _) ->
          let min_bound = Num.Int 0 in
          let max_bound =
            Num.num_of_string (Int64.to_string (Type.Ref.size ty - 1L))
          in
          JCPTpointer (compinfo.cname, [], Some min_bound, Some max_bound)
        | _ -> assert false
        end
      | None ->
        begin match unrollType (pointed_type ty) with
        | TComp (compinfo, _, _) ->
          JCPTpointer (compinfo.cname, [], None, None)
        | _ -> assert false
        end
      end
    | TArray _ -> assert false (* Removed by translation *)
    | TFun _ ->
      Console.unsupported "Function pointer type %a not allowed"  Printer.pp_typ ty
    | TNamed _ -> assert false (* Removed by call to [unrollType] *)
    | TComp (compinfo, _, _) -> JCPTidentifier (compinfo.cname, [])
    | TEnum (enuminfo, _) -> JCPTidentifier (enuminfo.ename, [])
    | TBuiltin_va_list _ -> Console.unsupported "Type builtin_va_list not allowed"
  in
  mktype tnode

let ltype t =
  (* Expand synonym types before translation. *)
  match Logic_utils.unroll_type t with
  | Ctype ty -> ctype ty
  | Ltype (s,[]) when s.lt_name = Utf8_logic.boolean ->
    mktype (JCPTidentifier ("boolean",[]))
  | Ltype (s,[]) -> mktype (JCPTidentifier (s.lt_name,[]))
  | Linteger -> mktype (JCPTnative Tinteger)
  | Lreal -> mktype (JCPTnative Treal)
  | Ltype(_,_)  -> Console.unsupported "polymorphic logic type"
  | Lvar _  -> Console.unsupported "logic type variable"
  | Larrow _ -> Console.unsupported "function type in logic"

let wrapper_name t = Name.typ (unrollType t) ^ "P"

(*****************************************************************************)
(* Cil to Jessie translation of constants                                    *)
(*****************************************************************************)

let native_type_of_fkind x : Jc.Env.native_type =
  match x with
  | FFloat -> Tgenfloat `Float
  | FDouble -> Tgenfloat `Double
  | FLongDouble -> failwith "Jessie does not handle long double yet"

let strip_float_suffix s =
  let l = pred(String.length s)  in
  match String.get s l with
  | 'f' | 'F' | 'l' | 'L' -> String.sub s 0 l
  | _ -> s


let logic_const ~loc:pos c lty =
  let c =
    match c with
    | Integer (_, Some s) -> JCPEconst (JCCinteger s)
    | Integer (n, None) -> JCPEconst (JCCinteger (Integer.to_string n))
    | LStr _ | LWStr _ -> Console.unsupported "string literals in logic"
    | LChr c -> JCPEconst (JCCinteger(string_of_int (Char.code c)))
    | LReal { r_literal = s } -> JCPEconst (JCCreal (strip_float_suffix s))
    | LEnum ei ->
      begin match Cil.isInteger (ei.eival) with
      | Some n ->
        let e =
          mkexpr (JCPEconst (JCCinteger (Integer.to_string n))) pos
        in
        JCPEcast (e, ctype (TEnum (ei.eihost, [])))
      | None -> assert false
      end
  in
  match c, lty with
  | JCPEcast _, _ -> c
  | _, Ctype ty -> JCPEcast (mkexpr c pos, ctype ty)
  | _ -> c

let rec const pos =
  function
  | CInt64 (_, ik, Some s) ->
    (* Use the textual representation if available *)
    JCPEcast (mkexpr (JCPEconst (JCCinteger s)) pos, ctype @@ TInt (ik, []))
  | CInt64 (i, ik, None) ->
    JCPEcast (mkexpr (JCPEconst (JCCinteger (Integer.to_string i))) pos, ctype @@ TInt (ik, []))
  | CStr _ | CWStr _ -> assert false (* Should have been rewritten *)
  | CChr c -> JCPEconst (JCCinteger (string_of_int (Char.code c)))
  | CReal (_f, fk, Some s) ->
    (* Use the textual representation if available *)
    let s = strip_float_suffix s in
    begin match !float_model with
    | `Math -> JCPEconst(JCCreal s)
    | `Defensive | `Full | `Multirounding ->
      (* add a cast to float or double depending on the value of fk *)
      JCPEcast(mkexpr (JCPEconst(JCCreal s)) pos,
               mktype (JCPTnative (native_type_of_fkind fk)))
    end
  | CReal (f, _fk, None) ->
    (* otherwise use the float value *)
    JCPEconst (JCCreal (string_of_float f))
  | CEnum item ->
    let e = mkexpr (const_of_expr pos item.eival) pos in
    JCPEcast (e, ctype (TEnum (item.eihost, [])))

and const_of_expr pos e =
  match (stripInfo e).enode with
  | Const c -> const pos c
  | _ -> assert false

and boolean_const =
  function
  | CInt64 (i, _ik, _text) ->
    if Integer.equal i Integer.zero then JCCboolean false
    else JCCboolean true
  | CStr _ | CWStr _ -> JCCboolean true
  | CChr c ->
    if Char.code c = 0 then JCCboolean false else JCCboolean true
  | CReal(f, _fk, _text) ->
    if f = 0.0 then JCCboolean false else JCCboolean true
  | CEnum {eival = e } -> boolean_const_of_expr e

and boolean_const_of_expr e =
  match (stripInfo e).enode with Const c -> boolean_const c | _ -> assert false

(*****************************************************************************)
(* Cil to Jessie translation of logic constructs                             *)
(*****************************************************************************)

let label =
  function
  | Label (lab, _, _) -> lab
  | Case _ | Default _ -> assert false

let builtin_label = Format.asprintf "%a" Cil_printer.pp_logic_builtin_label

let logic_label lab =
  let label_name s =
    LabelName {
      lab_name = s;
      lab_final_name = s;
      lab_times_used = 0;
    }
  in
  match lab with
  | BuiltinLabel b -> label_name (builtin_label b)
  | FormalLabel s -> label_name s
  | StmtLabel sref ->
    let labels = filter_out is_case_label !sref.labels in
    assert (not (labels = []));
    label_name (label (List.hd labels))

let logic_labels = List.map logic_label

let logic_labels_assoc = List.map logic_label

let term_lhost pos =
  function
  | TVar v ->
    begin try
      let li = Logic_env.find_logic_cons v in
      match li.l_labels with
      | [] -> mkexpr(JCPEvar v.lv_name) pos
      | [_] ->  mkexpr (JCPEapp (v.lv_name,[],[])) pos
      | _ ->
        Jessie_options.fatal
          "cannot handle logic constant %s with several labels"
          v.lv_name
    with
    | Not_found ->
      mkexpr (JCPEvar v.lv_name) pos
    end
  | TResult _ -> mkexpr (JCPEvar "\\result") pos
  | TMem t ->
    Console.unsupported "this kind of memory access is not currently supported: *%a" Printer.pp_term t

let product f t1 t2 =
  List.fold_right (fun x acc -> List.fold_right (fun y acc -> f x y :: acc) t2 acc) t1 []

let adjust_from_bitfield ~in_zone ~fi e =
  let ty = fi.ftype in
  if not in_zone && isArithmeticType ty && the fi.fsize_in_bits <> bitsSizeOf ty then
    mkexpr (JCPEcast (e, ctype ty)) e#pos
  else
    e

let pointer_comparison ~safe ~loc e1 rel e2 =
  let mkexpr node = mkexpr node loc in
  let sube = mkexpr (JCPEbinary (e1, `Bsub, e2)) in
  let e = JCPEbinary (sube, rel, zero_expr) in
  if safe then e
  else
    JCPEbinary (mkexpr (JCPEbinary (mkexpr (JCPEbase_block e1), `Beq, mkexpr (JCPEbase_block e2))), `Bland, mkexpr e)

let rec coerce_floats ~default_label t =
  let terms = terms ~default_label in
  match !float_model with
  | `Math -> terms t
  | `Defensive | `Full | `Multirounding ->
    if isLogicFloatType t.term_type then
      List.map
        (fun e -> mkexpr (JCPEcast (e, mktype (JCPTnative Treal))) t.term_loc)
        (terms t)
    else
      terms t

and terms ?(in_zone=false) ~default_label t =
  CurrentLoc.set t.term_loc;
  let term, terms, coerce_floats, terms_lval, default_label, terms_at =
    let default_label, for_current_term =
      let arg f = match default_label with `Force l | `Use l -> f l in
      match t.term_node with
      | Toffset (l, _) | Toffset_min (l, _) | Toffset_max (l, _) -> arg (fun l -> `Force l), `Force l
      | _                                                        -> arg (fun l -> `Use l), default_label
    in
    term ~default_label,
    terms ~default_label,
    coerce_floats ~default_label,
    terms_lval ~default_label,
    for_current_term,
    fun l -> terms ~default_label:(match default_label with `Use _ -> `Use l | `Force _ -> `Force l)
  in
  let enode =
    match constFoldTermNodeAtTop t.term_node with
    | TConst c -> [logic_const ~loc:t.term_loc c t.term_type]
    | TDataCons ({ctor_type = {lt_name = name} } as d,_args)
      when name = Utf8_logic.boolean ->
      [JCPEconst (JCCboolean (d.ctor_name = "\\true"))]
    | TDataCons(ctor,args) ->
      let args = List.map (terms ~in_zone) args in
      let args =
        List.fold_right (product (fun x y -> x::y)) args [[]]
      in
      List.map (fun x -> JCPEapp (ctor.ctor_name, [], x)) args
    | TUpdate _ -> Console.unsupported "logic update"
    | Toffset _ -> Console.unsupported "logic offset"
    | Toffset_max (_, t1) | Toffset_min (_, t1) as tnode ->
      let offset_kind =
        match tnode with
        | Toffset_max _ -> Offset_max
        | Toffset_min _ -> Offset_min
        | _ -> assert false
      in
      List.map (fun x -> JCPEoffset (offset_kind, x)) @@ terms t1
    | TLval lv ->
      List.map (fun x -> x#node) (terms_lval ~in_zone t.term_loc lv)

    | TSizeOf _ | TOffsetOf _ | TSizeOfE _ | TSizeOfStr _ | TAlignOf _ | TAlignOfE _ ->
      assert false (* Should be removed by constant folding *)
    | TUnOp (op, t) ->
      List.map (fun x -> JCPEunary(unop op,x)) (coerce_floats t)
    | TBinOp ((Lt | Gt | Le | Ge as op), t1, t2)
      when Type.Logic_c_type.map_default ~f:isPointerType t1.term_type ~default:false ->
      (* Pointer comparison is translated as subtraction + same_block *)
      let t1 = terms t1 in
      let t2 = terms t2 in
      let expr x y = pointer_comparison ~safe:false ~loc:t.term_loc x (binop op) y in
      product expr t1 t2
    | TBinOp (Shiftrt, t1, t2) ->
      let op =
        match t1.term_type with
        | Ctype ty1 ->
          if isSignedInteger ty1 then `Barith_shift_right
          else `Blogical_shift_right
        | Linteger -> `Barith_shift_right
        | _ -> assert false
      in
      product (fun x y -> JCPEbinary (x,op,y)) (terms t1) (terms t2)

    | TBinOp (Shiftlt _ as op, t1, t2) ->
      product (fun x y -> JCPEbinary (x, binop op, y)) (terms t1) (terms t2)
    | TBinOp ((Lt | Gt | Le | Ge) as op, t1, t2) ->
      product (fun x y -> JCPEbinary (x, binop op, y)) (terms t1) (terms t2)
    | TBinOp (op, t1, t2) ->
      product (fun x y -> JCPEbinary (x, binop op, y)) (coerce_floats t1) (coerce_floats t2)
    | TCastE (ty, _, t)
      when isIntegralType ty && isLogicRealType t.term_type ->
      List.map (fun x -> JCPEapp("\\truncate_real_to_int",[],[x])) (terms t)
    | TCastE (ty, oft, t')
      when isIntegralType ty && isLogicArithmeticType t'.term_type ->
      List.map
        (fun x -> (match oft with Check -> JCPEcast (x, ctype ty) | Modulo -> JCPEcast_mod (x, ctype ty)))
        (terms t')
    | TCastE (ty, _, t)
      when isFloatingType ty && isLogicArithmeticType t.term_type ->
      List.map (fun x -> JCPEcast (x, ctype ty)) (terms t)
    | TCastE (ty, _, t)
      when isIntegralType ty && Type.Logic_c_type.map_default ~f:isPointerType t.term_type ~default:false ->
      Console.unsupported "Casting from type %a to type %a not allowed"
        Printer.pp_logic_type t.term_type Printer.pp_typ ty
    | TCastE (ptrty, _, _t1) when isPointerType ptrty ->
      let rec strip_term_casts ?(cast=true) t =
        match t.term_node with
        | TCastE (_, _, t) when cast -> strip_term_casts ~cast:false t
        | TCastE (_, _, t') ->
          begin match (stripTermCasts t').term_node with
          | TConst _ -> t'
          | _ -> t
          end
        | _ -> t
      in
      let t = strip_term_casts t in
      begin match t.term_node with
      | Tnull -> [JCPEconst JCCnull]
      | TConst c
        when is_integral_logic_const c &&
             Integer.equal (value_of_integral_logic_const c) Integer.zero ->
        [JCPEconst JCCnull]
      | _ when Logic_utils.isLogicPointer t ->
        let dstty = unrollType @@ pointed_type ptrty in
        let srcty = unrollType @@ Type.Logic_c_type.(map ~f:pointed_type (of_logic_type_exn t.term_type)) in
        begin match srcty, dstty with
        | TComp (ci1, _, _), TComp (ci2, _, _) when ci1.cstruct && ci2.cstruct ->
          [JCPEcast (term t, ctype ptrty)]
        | _ ->
          Console.unsupported "Casting from type %a to type %a not allowed in logic"
            Printer.pp_logic_type t.term_type Printer.pp_typ ptrty
        end
      | _ ->
        Console.unsupported "Casting from non-pointer type %a to pointer type %a not allowed in logic"
          Printer.pp_logic_type t.term_type Printer.pp_typ ptrty
      end
    | TCastE (ty, _, t) ->
      (* TODO: support other casts in Jessie as well *)
      Console.unsupported "Casting from type %a to type %a not allowed"
        Printer.pp_logic_type t.term_type Printer.pp_typ ty
    | TAddrOf _tlv -> assert false (* Should have been rewritten *)
    | TStartOf tlv ->
      List.map (fun x -> x#node) (terms_lval ~in_zone t.term_loc tlv)
    | Tapp (linfo, labels, tlist) ->
      begin try
        let name = translated_name linfo tlist in
        let prof, tlist =
          if linfo.l_var_info.lv_name = "\\round_float" then
            List.tl linfo.l_profile, List.tl tlist
          else
            linfo.l_profile, tlist
        in
        let args =
          List.map2
            (fun lv t ->
               let t' = terms t in
               if isLogicFloatType t.term_type && isLogicRealType lv.lv_type
               then
                 List.map
                   (fun t' -> mkexpr (JCPEcast (t', mktype (JCPTnative Treal))) t.term_loc)
                   t'
               else t')
            prof
            tlist
        in
        let all_args = List.fold_right (product (fun x y -> x::y)) args [[]] in
        List.map
          (fun x -> JCPEapp (name, logic_labels_assoc labels, x)) all_args
      with
      | CtePredicate b ->
        [JCPEconst (JCCboolean b)]
      end
    | Tif (t1, t2, t3) ->
      let t1 = terms t1 in let t2 = terms t2 in let t3 = terms t3 in
      product (@@) (product (fun x y z -> JCPEif(x,y,z)) t1 t2) t3

    | Tpif (p, t1, t2) ->
      let cond = pred ~default_label p in
      let t1, t2 = map_pair terms (t1, t2) in
      product (@@) (product (fun x y z -> JCPEif (x, y, z)) [cond] t1) t2

    | Tat(t,lab) -> List.map (fun x -> JCPEat (x, logic_label lab)) (terms_at lab t)
    | Tbase_addr (_lab,t) -> List.map (fun x -> JCPEbase_block x) (terms t)
    | Tblock_length (_lab,_t) -> Console.unsupported "\\block_length operator"
    | Tnull -> [JCPEconst JCCnull]
    | Tlet (def, body) ->
      begin
        let v = def.l_var_info in
        match def.l_body, def.l_profile with
        | LBterm t, [] ->
          let jc_def = term t in
          let jc_body = term body in
          let typ = ltype v.lv_type in
          [JCPElet(Some typ, v.lv_name, Some jc_def, jc_body)]
        | LBpred p, [] ->
          let jc_def = pred ~default_label p in
          let jc_body = term body in
          [JCPElet(None,v.lv_name, Some jc_def, jc_body)]
        | (LBterm _ | LBpred _), _::_ ->
          Console.unsupported "local function definition"
        | (LBnone | LBreads _ | LBinductive _), _ ->
          Jessie_options.fatal "Unexpected definition for local variable"
      end
    | TCoerce (_t, _typ) -> Console.unsupported "term coercion"
    | TCoerceE (_t1, _t2) -> Console.unsupported "term coercion"
    | Tlambda _ ->
      Console.unsupported "Jessie plugin does not support lambda abstraction"
    | Ttypeof _ | Ttype _ -> assert false (* Should have been treated *)
    | Trange (low, high) ->
      let coerce t = if t.term_type = Linteger then t else { t with term_node = TLogic_coerce(Linteger, t) } in
      let low, high = map_pair (opt_map coerce) (low, high) in
      [JCPErange(opt_map term low,opt_map term high)]
    | Tunion l ->
      List.map (fun x -> x#node) (List.flatten (List.map terms l))
    | Tcomprehension _ -> Console.unsupported "sets by comprehension"
    | Tinter _ -> Console.unsupported " set intersection"
    | Tempty_set -> []
    | TLogic_coerce (Lreal, t) -> List.map (fun x -> x#node) (coerce_floats t)
    | TLogic_coerce (Linteger, t) -> List.map (fun x -> JCPEcast (x, mktype @@ JCPTnative Tinteger)) (terms t)
    | TLogic_coerce (_, t) -> List.map (fun x -> x#node) (terms t)
  in
  let enode =
    match default_label with
    | `Force l ->
      List.map
        (fun e ->
           match e with
           | JCPEat _ -> e
           | _ -> JCPEat (mkexpr e t.term_loc, logic_label l))
        enode
    | _ -> enode
  in
  List.map (Fn.flip mkexpr t.term_loc) enode

and tag ~default_label t =
  let tag_node =
    match t.term_node with
    | Ttypeof t -> JCPTtypeof (term ~default_label t)
    | Ttype ty ->
      let id = mkidentifier Type.Composite.(compinfo_cname @@ of_typ_exn @@ pointed_type ty) t.term_loc in
      JCPTtag id
    | _ ->
      (* Not a tag *)
      Console.unsupported "can't inerpret this term as tag: %a" Printer.pp_term t
  in
  mktag tag_node t.term_loc

and terms_lval ~in_zone ~default_label pos lv =
  let terms = terms ~default_label in
  match lv with
  | lhost, TNoOffset -> [term_lhost pos lhost]

  | (TVar _ | TResult _), _off ->
    assert false (* Should have been rewritten *)

  | TMem t, TModel(mi, toff) ->
    assert (toff = TNoOffset); (* Others should have been rewritten *)
    let e = terms t in
    List.map (fun e -> mkexpr (JCPEderef(e,mi.mi_name)) pos) e

  | TMem t, TField(fi,toff) ->
    assert (toff = TNoOffset); (* Others should have been rewritten *)
    let e = terms t in
    if not fi.fcomp.cstruct then (* field of union *)
      List.map (fun e -> mkexpr (JCPEcast(e,ctype fi.ftype)) pos) e
    else
      let repfi = Retype.FieldUF.repr fi in
      let e,fi =
        if Fieldinfo.equal fi repfi then
          e,fi
        else
          let caste =
            List.map
              (fun e ->
                 mkexpr (
                   JCPEcast(e,
                            ctype (TPtr (TComp (repfi.fcomp, empty_size_cache (),[]), [])))) pos)
              e
          in
          caste,repfi
      in
      List.map (fun e -> adjust_from_bitfield ~in_zone ~fi @@ mkexpr (JCPEderef(e,fi.fname)) pos) e

  | TMem t, TIndex (it, TField (fi, toff)) ->
    assert (toff = TNoOffset); (* Others should have been rewritten *)
    (* Normalization made it equivalent to simple add *)
    let e =
      product
        (fun t it -> mkexpr (JCPEbinary(t,`Badd,it)) pos)
        (terms t) (terms it)
    in
    if not fi.fcomp.cstruct then (* field of union *)
      List.map (fun e -> mkexpr (JCPEcast(e,ctype fi.ftype)) pos) e
    else
      let repfi = Retype.FieldUF.repr fi in
      let e,fi =
        if Fieldinfo.equal fi repfi then
          e,fi
        else
          let caste =
            List.map
              (fun e ->
                 mkexpr
                   (JCPEcast(e, ctype
                               (TPtr (TComp (repfi.fcomp, empty_size_cache (), []), [])))) pos)
              e
          in
          caste, repfi
      in
      List.map (fun e -> mkexpr (JCPEderef(e,fi.fname)) pos) e
  | TMem _e, TIndex _ ->
    Console.unsupported "cannot interpret this lvalue: %a"
      Printer.pp_term_lval lv

and term ~default_label t =
  match terms ~default_label t with
  | [ t ] -> t
  | _ ->
    Console.unsupported "Expecting a single term, not a set:@ %a@."
      Printer.pp_term t

and pred ~default_label p =
  CurrentLoc.set p.pred_loc;
  let term, _terms, coerce_floats, tag, pred, default_label, pred_at =
    let default_label, for_current_pred =
      let arg f = match default_label with `Force l | `Use l -> f l in
      match p.pred_content with
      | Pvalid (l, _) -> arg (fun l -> `Force l), `Force l
      | _             -> arg (fun l -> `Use l), default_label
    in
    term ~default_label,
    terms ~default_label,
    coerce_floats ~default_label,
    tag ~default_label,
    pred ~default_label,
    for_current_pred,
    fun l -> pred ~default_label:(match default_label with `Force _ -> `Force l | `Use _ -> `Use l)
  in
  let rec fully_valid =
    let mk_term t = Logic_const.term ~loc:p.pred_loc t Linteger in
    let tinteger = Logic_const.tinteger ~loc:p.pred_loc in
    fun ?omin ?omax t ->
      let supplied_offs = Option.(is_some omin && is_some omax) in
      let omin, omax = omin |? tinteger 0, omax |? tinteger 0 in
      let valid ~omin ~omax =
        let t = term t in
        let off_min = mkexpr (JCPEoffset (Offset_min, t)) p.pred_loc in
        let omin = mkexpr (JCPEbinary (off_min, `Ble, term omin)) p.pred_loc in
        let off_max = mkexpr (JCPEoffset (Offset_max, t)) p.pred_loc in
        let omax = mkexpr (JCPEbinary(off_max, `Bge, term omax)) p.pred_loc in
        mkconjunct [omin; omax] p.pred_loc
      in
      let omax =
        let size, size_gt_one =
          map_fst tinteger @@
          Type.Ref.(
            if Logic_utils.isLogicType (fun _ -> true) t.term_type then
              let typ = Logic_utils.logicCType t.term_type in
              let is_ref = is_ref typ and size = lazy (size (of_typ_exn typ)) in
              if is_ref && !!size > 1L then Int64.to_int !!size, true else 1, false
            else 1, false)
        in
        let one = tinteger 1 in
        if not supplied_offs && size_gt_one then
          mk_term @@ TBinOp (MinusA Check, mk_term @@ TBinOp (Mult Check, one, size), one)
        else
          omax
      in
      let wrap =
        let just_several =
          match map_pair (Logic_utils.constFoldTermToInt ~machdep:true) (omin, omax) with
          | Some v1, Some v2 ->
            Integer.(if le (sub v2 v1) sixteen then Some (to_int v1, to_int v2) else None)
          | _ -> None
        in
        fun e ->
          let i = make_temp_logic_var Linteger in
          let var_i = mkexpr (JCPEvar i.lv_name) p.pred_loc in
          match just_several with
          | Some (v1, v2) when v1 = v2 ->
            if v1 = 0 then e None else e @@ Some (tinteger v1)
          | Some (v1, v2) when Pervasives.(v1 <= v2) ->
            mkconjunct List.(range v1 `To v2 |> map @@ fun i -> e @@ Some (tinteger i)) p.pred_loc
          | Some _ -> mkexpr (JCPEconst (JCCboolean true)) p.pred_loc
          | None ->
            mkexpr
              (JCPEquantifier
                 (Forall, ltype Linteger, [new identifier i.lv_name], [],
                  mkimplies
                    [mkconjunct
                       [mkexpr (JCPEbinary (term omin, `Ble, var_i)) p.pred_loc;
                        mkexpr (JCPEbinary (var_i, `Ble, term omax)) p.pred_loc]
                       p.pred_loc]
                    [e @@ Some (Logic_const.tvar i)]
                    p.pred_loc))
              p.pred_loc
      in
      let gen_valid ci =
        valid ~omin ~omax ::
        [wrap @@ fun io ->
         mkconjunct
           (List.filter_map
              ~f:(fun fi ->
                  if Type.Ref.is_ref fi.ftype then
                    let size = Type.Ref.(size @@ of_typ_exn fi.ftype) in
                    if size > 0L then
                      Some
                        (fully_valid
                           (let t =
                              match io with
                              | None -> t
                              | Some i -> mk_term (TBinOp (PlusPI, t, i))
                            in
                            Logic_const.term (TLval (TMem t, TField (fi, TNoOffset))) @@ Ctype fi.ftype)
                           ~omin:(tinteger 0)
                           ~omax:(tinteger Int64.(to_int @@ size - 1L)))
                    else
                      None
                  else
                    None)
              ci.cfields)
           p.pred_loc]
      in
      mkconjunct
        (Type.Logic_c_type.map_default
           ~default:[valid ~omin ~omax]
           t.term_type
           ~f:(fun ty ->
               match unrollTypeDeep ty with
               | TPtr (TComp ({ cstruct = true } as ci, _, _), _)
               | TArray (TComp ({ cstruct = true } as ci, _, _), _, _, _) ->
                 gen_valid ci
               | ty when Type.Ref.(is_ref ty && Type.Composite.Struct.is_struct @@ typ @@ of_typ_exn ty) ->
                 gen_valid @@ Type.Composite.(compinfo @@ of_typ_exn @@ Type.Ref.(typ @@ of_typ_exn ty))
               | _ -> [valid ~omin ~omax]))
        p.pred_loc
  in
  let enode =
    match[@warning "-57"] p.pred_content with
    | Pfalse -> JCPEconst (JCCboolean false)

    | Ptrue -> JCPEconst (JCCboolean true)

    | Papp (pinfo, labels, tl) ->
      begin try
        let name = translated_name pinfo tl in
        let args =
          List.map2
            (fun lv t ->
               let t' = term t in
               if isLogicFloatType t.term_type && isLogicRealType lv.lv_type
               then
                 mkexpr (JCPEcast(t', mktype (JCPTnative Treal))) t.term_loc
               else
                 t')
            pinfo.l_profile
            tl
        in
        JCPEapp (name, logic_labels_assoc labels, args)
      with
      | CtePredicate b -> JCPEconst (JCCboolean b)
      end
    | Prel ((Rlt | Rgt | Rle | Rge as rel), t1, t2)
      when Type.Logic_c_type.map_default ~f:isPointerType ~default:false t1.term_type ->
      (* Pointer comparison is translated as subtraction + same_block *)
      pointer_comparison ~safe:false ~loc:p.pred_loc (term t1) (relation rel) (term t2)

    | Prel (Req, t1, t2) when isTypeTagType t1.term_type ->
      JCPEeqtype (tag t1, tag t2)

    | Prel (Rneq, t1, t2) when isTypeTagType t1.term_type ->
      let eq = mkexpr (JCPEeqtype(tag t1,tag t2)) p.pred_loc in
      JCPEunary (`Unot,eq)

    | Prel (rel,t1,t2) ->
      let res =
        product
          (fun t1 t2 -> mkexpr (JCPEbinary (t1, relation rel, t2)) p.pred_loc)
          (coerce_floats t1)
          (coerce_floats t2)
      in
      (mkconjunct res p.pred_loc)#node

    | Pand(p1,p2) ->
      JCPEbinary (pred p1, `Bland, pred p2)

    | Por (p1, p2) ->
      JCPEbinary(pred p1, `Blor, pred p2)

    | Pxor (p1,p2) ->
      let notp2 = { p2 with pred_content = Pnot p2; } in
      let p1notp2 = { p with pred_content = Pand(p1,notp2); } in
      let notp1 = { p1 with pred_content = Pnot p1; } in
      let p2notp1 = { p with pred_content = Pand(p2,notp1); } in
      JCPEbinary (pred p1notp2,`Blor, pred p2notp1)

    | Pimplies (p1, p2) ->
      JCPEbinary (pred p1, `Bimplies, pred p2)

    | Piff (p1, p2) ->
      JCPEbinary (pred p1, `Biff, pred p2)

    | Pnot p -> JCPEunary(`Unot,pred p)

    | Pif (t, p1, p2) -> JCPEif (term t, pred p1, pred p2)

    | Plet (def, body) ->
      begin
        let v = def.l_var_info in
        match def.l_body, def.l_profile with
        | LBterm t, [] ->
          let jc_def = term t in
          let jc_body = pred body in
          let typ = ltype v.lv_type in
          JCPElet (Some typ, v.lv_name, Some jc_def, jc_body)
        | LBpred p, [] ->
          let jc_def = pred p in
          let jc_body = pred body in
          JCPElet (None,v.lv_name, Some jc_def, jc_body)
        | (LBterm _ | LBpred _), _::_ ->
          Console.unsupported "local function definition"
        | (LBnone | LBreads _ | LBinductive _), _ ->
          Jessie_options.fatal "Unexpected definition for local variable"
      end

    | Pforall ([], p) -> (pred p)#node
    | Pforall ([v], p) ->
      JCPEquantifier(Forall, ltype v.lv_type, [new identifier v.lv_name], [], pred p)

    | Pforall (v :: q, subp) ->
      let newp = { p with pred_content = Pforall(q,subp) } in
      JCPEquantifier (Forall,ltype v.lv_type, [new identifier v.lv_name], [], pred newp)

    | Pexists ([], p) -> (pred p)#node

    | Pexists ([v], p) ->
      JCPEquantifier (Exists,ltype v.lv_type, [new identifier v.lv_name], [], pred p)

    | Pexists (v :: q, subp) ->
      let newp = { p with pred_content = Pexists(q,subp) } in
      JCPEquantifier (Exists,ltype v.lv_type, [new identifier v.lv_name], [], pred newp)

    | Pat (p, lab) -> JCPEat (pred_at lab p, logic_label lab)

    | Pvalid (lab, { term_node = Tat (t, lab') }) ->
      (pred { p with pred_content = Pat ({ p with pred_content = Pvalid (lab, t) }, lab') })#node

    | Pvalid (_lab,
              { term_node = TBinOp (PlusPI, t1,
                                    {term_node = Trange (start, stop)})}) ->
      let mk_one_pred t1 =
        let mk_valid_in_range ~guarded ~omin ~omax =
          let result = fully_valid t1 ~omin ~omax in
          if not guarded then
            result
          else
            let cond = mkexpr (JCPEbinary (term omin, `Ble, term omax)) p.pred_loc in
            mkexpr (JCPEif (cond, result, true_expr)) p.pred_loc
        in
        match start, stop with
        | None, _
        | _, None -> false_expr
        | Some ({ term_node = TConst (Integer (a, _))} as omin),
          Some ({ term_node = TConst (Integer (b, _))} as omax) ->
          if Integer.le a b then
            mk_valid_in_range ~guarded:false ~omin ~omax
          else
            true_expr
        | Some omin, Some omax ->
          mk_valid_in_range ~guarded:true ~omin ~omax
      in
      (mk_one_pred t1)#node

    | Pvalid (_lab, { term_node = TBinOp (PlusPI, t1, t2) }) -> (fully_valid t1 ~omin:t2 ~omax:t2)#node
    | Pvalid (_lab, t) -> (fully_valid t)#node

    | Pvalid_read _ -> Console.unsupported "\\valid_read predicate is unsupported"
    | Pvalid_function _ -> Console.unsupported "\\valid_function predicate is unsupported"

    | Pfresh (lab1, _lab2, t, _) ->
      (* TODO: take into account size *)
      JCPEat (mkexpr (JCPEfresh (term t)) p.pred_loc, logic_label lab1)
    | Pallocable _ -> Console.unsupported "\\allocable predicate is unsupported"

    | Pfreeable _ -> Console.unsupported "\\freeable predicate is unsupported"

    | Psubtype ({term_node = Ttypeof t}, {term_node = Ttype ty})
      when isPointerType ty ->
      JCPEinstanceof (term t, Type.Composite.(compinfo_cname (of_typ_exn @@ pointed_type ty)))

    | Psubtype ({term_node = Ttype ty1}, {term_node = Ttype ty2})
      when not (isPointerType ty1) || not (isPointerType ty2) ->
      Console.unsupported "Subtyping relation (<:) is only suported for pointer types"

    | Psubtype (_, { term_node = Ttype ty })
    | Psubtype ({ term_node = Ttype ty }, _)
      when not (isPointerType ty) ->
      Console.unsupported "Subtyping relation (<:) is only suported for pointer types (here: \\type(%a))" Printer.pp_typ ty

    | Psubtype (t1, t2) ->
      JCPEsubtype (tag t1, tag t2)

    | Pseparated (_seps) -> Console.unsupported "\\separated predicate is unsupported"

    | Pdangling _ -> Console.unsupported "\\dangling predicate is unsupported"

    | Pinitialized _ -> Console.unsupported "\\initialized predicate is unsupported"
  in
  let enode =
    match default_label, enode with
    | `Force _, JCPEat _ -> enode
    | `Force l, _ -> JCPEat (mkexpr enode p.pred_loc, logic_label l)
    | _ -> enode
  in
  mkexpr enode p.pred_loc

let terms ?(default_label=Logic_const.here_label) = terms ~default_label:(`Use default_label)

let term ?(default_label=Logic_const.here_label) = term ~default_label:(`Use default_label)

let pred ?(default_label=Logic_const.here_label) = pred ~default_label:(`Use default_label)

(* Keep names associated to predicate *)
let named_pred ?(default_label=Logic_const.here_label) p =
  List.fold_right (fun lab p -> mkexpr (JCPElabel(lab,p)) p#pos) p.pred_name (pred ~default_label p)

let conjunct ?(default_label=Logic_const.here_label) pos pl =
  mkconjunct (List.map (pred ~default_label % Logic_const.pred_of_id_pred) pl) pos

let zone ?(default_label=Logic_const.here_label) (tset, _) =
  terms ~default_label ~in_zone:true tset.it_content

(* Distinguish between:
 * - no assign, which is the empty list in Cil and None in Jessie
 * - assigns nothing, which is [Nothing] in Cil and the Some[] in Jessie
*)
let assigns =
  function
  | WritesAny -> None
  | Writes assign_list ->
    let assign_list =
      List.filter
        (function out,_ -> not (Logic_utils.is_result out.it_content))
        assign_list
    in
    let assign_list = List.flatten (List.map zone assign_list) in
    Some (Why_loc.dummy_position, assign_list)

let allocates a =
  match a with
  | FreeAllocAny -> None
  | FreeAlloc (frees, allocs) ->
    let frees =
      List.map
        (fun t -> Logic_const.({ t with it_content = tat ~loc:t.it_content.term_loc (t.it_content, old_label) }))
        frees
    in
    let allocs, frees = map_pair (List.fold_left (fun acc out -> (out, 1) :: acc) []) (allocs, frees) in
    let result =
      List.flatten @@ List.map zone allocs @ List.map (zone ~default_label:Logic_const.old_label) frees
    in
    Some (Why_loc.dummy_position, result)

let spec _fname funspec =
  let is_normal_postcond =
    function
    |  Normal, _ -> true
    | (Exits | Returns | Breaks | Continues), _ -> false
  in
  let behavior b =
    if List.exists (not % is_normal_postcond) b.b_post_cond then
      Console.warn_once "abrupt clause(s) ignored";
    let name =
      if b.b_name = Cil.default_behavior_name then
        Name.Behavior.default
      else if b.b_name = Name.Behavior.default then
        Name.Behavior.default ^ "_jessie"
      else b.b_name
    in
    let loc =
      function
      | [] -> Why_loc.dummy_position
      | ip :: _ -> ip.ip_content.pred_loc
    in
    JCCbehavior(
      loc b.Cil_types.b_assumes,
      name,
      None, (* throws *)
      Some (conjunct (loc b.Cil_types.b_assumes) b.Cil_types.b_assumes),
      None, (* requires *)
      assigns b.Cil_types.b_assigns,
      allocates b.b_allocation,
      locate
        (conjunct (loc @@ List.map snd b.b_post_cond)
           (Extlib.filter_map
              (function (Normal,_) -> true
                 | (Exits | Returns | Breaks | Continues),_ -> false)
              snd b.b_post_cond)))
  in
  let behaviors = List.map behavior funspec.spec_behavior in
  let requires =
    List.fold_right
      (fun b acc ->
         let ass, reqs =
           map_pair (List.map (locate % pred % Logic_const.pred_of_id_pred)) (b.Cil_types.b_assumes, b.b_requires)
         in
         JCCrequires (mkimplies ass reqs Why_loc.dummy_position) :: acc)
      funspec.spec_behavior
      []
  in

  let complete_behaviors_assertions : Jc.Ast.pexpr list =
    List.map
      (fun bnames ->
         mkdisjunct
             (List.fold_left
                (fun acc b ->
                   match b with
                   | JCCbehavior(_,name,_,Some a,_,_,_,_) ->
                     if (bnames = [] && name <> Name.Behavior.default)
                     || List.mem name bnames
                     then
                       a :: acc
                     else
                       acc
                   | _ -> assert false)
                []
                behaviors)
             Why_loc.dummy_position)
      funspec.spec_complete_behaviors
  in
  let disjoint_behaviors_assertions  : Jc.Ast.pexpr list =
    List.fold_left
      (fun acc bnames ->
         let all_assumes =
           List.fold_left
             (fun acc b ->
                match b with
                  | JCCbehavior(_,name,_,Some a,_,_,_,_) ->
                    if (bnames = [] &&
                        name <> Name.Behavior.default) ||
                       List.mem name bnames
                    then a :: acc
                    else acc
                  | _ -> assert false)
             []
             behaviors
         in
         let rec aux assumes prevs acc =
           match assumes with
           | [] -> acc
           | b :: rem ->
             let acc =
               List.fold_left
                 (fun acc a ->
                    (mkexpr (JCPEunary(`Unot,
                                       mkconjunct [b;a] Why_loc.dummy_position))
                       Why_loc.dummy_position)
                        :: acc)
                 acc prevs
             in
             aux rem (b :: prevs) acc
         in
         aux all_assumes [] acc)
      []
      funspec.spec_disjoint_behaviors
  in

  let decreases =
    match funspec.spec_variant with
    | None -> []
    | Some (t, None) ->
      [JCCdecreases (locate (term t), None)]
    | Some (t, Some id) ->
      [JCCdecreases (locate (term t), Some (new identifier id))]
  in

  (* TODO: translate terminates clauses *)
  if funspec.spec_terminates <> None then
    Console.warn_once "Termination condition(s) ignored" ;

  (requires @ decreases @ behaviors),
  complete_behaviors_assertions,
  disjoint_behaviors_assertions

let built_behavior_ids = function
  | [] -> [new identifier Name.Behavior.default]
  | l ->
    List.map
      (fun i ->
         new identifier
           (if i = Name.Behavior.default then
              Name.Behavior.default ^ "_jessie"
            else
              i))
      l

let code_annot ?e pos ((acc_assert_before, contract) as acc) a =
  let push s = s :: acc_assert_before, contract in
  match a.annot_content with
  | AAssert (behav,p) ->
    let behav = built_behavior_ids behav in
    let asrt =
      Option.map_default
        ~default:Aassert
        ~f:(fun e -> if Emitter.equal e Emitters.jessie_assume then Aassume else Aassert)
        e
    in (* [VP] Needs to retrieve exact status *)
    push
      (mkexpr
         (JCPEassert (behav, asrt, locate ~pos (named_pred p))) pos)
  | AInvariant (_behav, is_loop_inv, _p) ->
    if is_loop_inv then acc (* should be handled elsewhere *)
    else Console.unsupported "general code invariant"
  | APragma (Jessie_pragma (JPexpr t)) ->
    begin match t.term_node with
    | TCoerce (t, typ) ->
      let from_type =
        match t.term_type with
        | Ctype t -> t
        | ty -> Console.unsupported "reinterpretation from a logic term %a of type %a"
                  Printer.pp_term t Printer.pp_logic_type ty
      in
      let check_supported_type s t =
        let integral_struct_name t =
          match unrollType t with
          | TComp ({ cname; cfields = [fi] }, _, _) when isIntegralType fi.ftype ->
            Some cname
          | _ -> None
        in
        let t = if isArrayType t then TPtr (element_type t, []) else t in
        match isPointerType t, lazy (integral_struct_name @@ pointed_type t) with
        | false, _ | true, lazy None ->
          Console.unsupported "reinterpretation %s what is not a pointer to an integer (%a)" s Printer.pp_typ t
        | true, lazy (Some s) -> s
      in
      let _, typ = map_pair (Fn.uncurry @@ check_supported_type) (("from", from_type), ("to", typ)) in
      if typ = wrapper_name voidType then Console.unsupported "reinterpretation to void *"
      else push @@ locate (PExpr.mkreinterpret ~expr:(term t) ~typ ~pos ())
    | _ ->
      Console.unsupported
        "unrecognized term in Jessie pragma (only :> is recognized):@ %a@. Note that :> binds tighter than typecasts."
        Printer.pp_term t
    end
  | APragma _ -> acc (* just ignored *)
  | AAssigns (_, _) -> acc (* should be handled elsewhere *)
  | AAllocation _ -> acc (* should be handled elsewhere *)
  | AVariant _ -> acc (* should be handled elsewhere *)
  | AStmtSpec ([], s) -> (* TODO: handle case of for *)
    begin  match contract with
    | None -> (acc_assert_before,Some s)
    | Some _ -> assert false
    end
  | AStmtSpec _ ->
    Console.unsupported "statement contract for a specific behavior"
  | AExtended _ ->
    Console.unsupported "code annotation extension"

(*****************************************************************************)
(* Cil to Jessie translation of coding constructs                            *)
(*****************************************************************************)

let set_curFundec, get_curFundec =
  let cf = ref None in
  ((fun f -> cf := Some f),
   (fun () ->
      match !cf with
          None ->
            let res = emptyFunction "@empty@" in cf := Some res; res
        | Some res -> res))

let rec expr e =

  let enode =
    let e = stripInfo e in
    match e.enode with
    | Info _ -> assert false

    | Const c -> const e.eloc c

    | Lval lv -> (lval e.eloc lv)#node

    | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->
        assert false (* Should be removed by constant folding *)

    | UnOp(_op,_e,ty) when isIntegralType ty ->
        (integral_expr e)#node

    | UnOp(op,e,_ty) ->
        let e =
          locate (mkexpr (JCPEunary(unop op,expr e)) e.eloc)
        in
        e#node

    | BinOp(_op,_e1,_e2,ty) when isIntegralType ty ->
        (integral_expr e)#node

    | BinOp(op,e1,e2,_ty) ->
        let e =
          locate (mkexpr (JCPEbinary(expr e1,binop op,expr e2)) e.eloc)
        in
        e#node

    | CastE (ty, _, e')
        when isIntegralType ty && isFloatingType (typeOf e') ->
        let e1 =
          locate (mkexpr (JCPEcast(expr e',mktype (JCPTnative Treal))) e.eloc)
        in
        let e =
          locate (mkexpr (JCPEapp("\\truncate_real_to_int",[],[e1])) e.eloc)
        in e#node

    | CastE (ty, _, e') when isIntegralType ty && isArithmeticType (typeOf e') ->
        (integral_expr e)#node

    | CastE(ty, _, e') when isFloatingType ty && isArithmeticType (typeOf e') ->
        let e = locate (mkexpr (JCPEcast(expr e',ctype ty)) e.eloc) in
        e#node

    | CastE (ty, _, e') when isIntegralType ty && isPointerType (typeOf e') ->
      Console.unsupported "Casting from type %a to type %a not allowed"
        Printer.pp_typ (typeOf e') Printer.pp_typ ty

    | CastE (ptrty, _, _e1) when isPointerType ptrty ->
      let rec strip_cast_and_infos ?(cast=true) e =
        match e.enode with
        | Info (e, _) -> strip_cast_and_infos e
        | CastE (_, _, e) when cast -> strip_cast_and_infos ~cast:false e
        | CastE (_, _, e) when isConstant (stripCastsAndInfo e) -> e
        | _ -> e
      in
      let e = strip_cast_and_infos e in
      let is_struct_pointer ty =
        (isPointerType ty || isArrayType ty) && Type.Composite.Struct.is_struct (pointed_type ty)
      in
      begin match e.enode with
      | Const c
        when is_integral_const c
             && Integer.equal (value_of_integral_const c) Integer.zero ->
        JCPEconst JCCnull
      | _ ->
        let ety = typeOf e in
        if isIntegralType ety then
          Console.unsupported "Casting from type %a to type %a not allowed"
            Printer.pp_typ (typeOf e) Printer.pp_typ ptrty
        else if is_struct_pointer ety && is_struct_pointer ptrty then
          let enode = JCPEcast (expr e, ctype ptrty) in
          let e = locate (mkexpr enode e.eloc) in
          e#node
        else
          Console.unsupported "Casting from type %a to type %a not allowed"
            Printer.pp_typ (typeOf e) Printer.pp_typ ptrty
      end

    | CastE (ty, _, e') ->
        (* TODO: support other casts in Jessie as well, through low-level
         * memory model
         *)
        Console.unsupported "Casting from type %a to type %a not allowed in %a with size %Ld and %Ld"
          Printer.pp_typ (typeOf e') Printer.pp_typ ty Printer.pp_exp e
          (Type.size_in_bits_exn ty) (Type.size_in_bits_exn (typeOf e'))


    | AddrOf _lv -> assert false (* Should have been rewritten *)

    | StartOf lv -> (lval e.eloc lv)#node
  in
  mkexpr enode e.eloc

(* Function called when expecting a boolean in Jessie, i.e. when translating
   a test or a sub-expression of an "or" or "and".
*)
and boolean_expr ?(to_locate=false) e =
  let boolean_node_from_expr ty e' =
    if isPointerType ty then JCPEbinary (e', `Bneq, null_expr)
    else if isArithmeticType ty then
      let cast = let ty = ctype ty in fun e' -> mkexpr (JCPEcast (e', ty)) e.eloc in
      JCPEbinary (cast e', `Bneq, cast zero_expr)
    else
      assert false
  in

  let enode = match (stripInfo e).enode with
    | Info _ -> assert false

    | Const c -> JCPEconst(boolean_const c)

    | UnOp(LNot,e,_typ) -> JCPEunary(unop LNot,boolean_expr e)

    | BinOp((LAnd | LOr) as op,e1,e2,_typ) ->
        JCPEbinary (boolean_expr ~to_locate:true e1, binop op, boolean_expr ~to_locate:true e2)

    | BinOp((Eq | Ne) as op,e1,e2,_typ) ->
        JCPEbinary(expr e1,binop op,expr e2)

    | BinOp((Lt | Gt | Le | Ge) as op,e1,e2,_typ) ->
        let ty = typeOf e1 in
        if isArithmeticType ty then
          JCPEbinary(expr e1,binop op,expr e2)
        else
          (* Pointer comparison is translated as subtraction + same_block *)
          pointer_comparison ~safe:true ~loc:e.eloc (expr e1) (binop op) (expr e2)

    | _ -> boolean_node_from_expr (typeOf e) (expr e)
  in
  let e' = mkexpr enode e.eloc in
  if to_locate then locate e' else e'

(* Function called instead of plain [expr] when the evaluation result should
 * fit in a C integral type.
 *)
and integral_expr e =

  let rec int_expr e =
    let node_from_boolean_expr e = JCPEif (e, one_expr, zero_expr) in
    let expr_shift_precast ~t1 e2 =
      let e2' = expr e2 in
      let t2 = typeOf e2 in
      if bitsSizeOf t1 <> bitsSizeOf t2 || isSignedInteger t1 <> isSignedInteger t2 then
        mkexpr (JCPEcast (e2', ctype ~bitsize:(bitsSizeOf t1) t1)) e2.eloc
      else
        e2'
    in

    let enode = match e.enode with
      | UnOp(LNot,e',_ty) ->
          let e = mkexpr (JCPEunary (unop LNot, boolean_expr e')) e.eloc in
          node_from_boolean_expr e

      | UnOp(op,e',_ty) ->
          let e =
            locate (mkexpr (JCPEunary (unop op, expr e')) e.eloc)
          in
          e#node

      | BinOp((LAnd | LOr) as op,e1,e2,_ty) ->
          let e =
            mkexpr (JCPEbinary (boolean_expr e1, binop op, boolean_expr e2)) e.eloc
          in
          node_from_boolean_expr e

      | BinOp((Lt | Gt | Le | Ge as op),e1,e2,_ty)
          when isPointerType (typeOf e1) ->
          (* Pointer comparison is translated as subtraction + same_block *)
          let e' = pointer_comparison ~safe:true ~loc:e.eloc (expr e1) (binop op) (expr e2) in
          node_from_boolean_expr (mkexpr e' e.eloc)

(*       | BinOp((Eq | Ne as op),e1,e2,_ty) *)
(*           when isPointerType (typeOf e1) && *)
(*             not (is_null_expr e2 || is_null_expr e1) -> *)
(*           (\* Pointer (dis-)equality is translated as subtraction *\) *)
(*           let sube = mkexpr (JCPEbinary(expr e1,`Bsub,expr e2)) pos in *)
(*           let e = mkexpr (JCPEbinary(sube,binop op,zero_expr)) pos in *)
(*           node_from_boolean_expr e *)

      | BinOp((Eq | Ne) as op,e1,e2,_ty) ->
          let e = mkexpr (JCPEbinary(expr e1,binop op,expr e2)) e.eloc in
          node_from_boolean_expr e

      | BinOp((Lt | Gt | Le | Ge) as op,e1,e2,_ty) ->
          let e = mkexpr (JCPEbinary(expr e1,binop op,expr e2)) e.eloc in
          node_from_boolean_expr e

      | BinOp (Shiftrt, e1, e2, _ty) ->
        let e =
          let t1 = typeOf e1 in
          let op =
            if isSignedInteger t1 then `Barith_shift_right
            else `Blogical_shift_right
          in
          locate (mkexpr (JCPEbinary(expr e1,op,expr_shift_precast ~t1 e2)) e.eloc)
        in
        e#node

      | BinOp (Shiftlt _ as op, e1, e2, _ty) ->
        let e =
          let t1 = typeOf e1 in
          locate (mkexpr (JCPEbinary(expr e1,binop op,expr_shift_precast ~t1 e2)) e.eloc)
        in
        e#node

      | BinOp(op,e1,e2,_ty) ->
          let e =
            locate (mkexpr (JCPEbinary(expr e1,binop op,expr e2)) e.eloc)
          in
          e#node

      | CastE (ty, _, e1) when isFloatingType (typeOf e1) ->
          let e1' = locate (mkexpr (JCPEcast(expr e1,ltype Linteger)) e.eloc) in
          let e2' = locate (mkexpr (JCPEcast(e1',ctype ty)) e.eloc) in
          e2'#node

      | CastE (ty, oft, e1) when isIntegralType (typeOf e1) ->
        let cast =
          match oft with
          | Check -> JCPEcast (int_expr e1, ctype ty)
          | Modulo -> JCPEcast_mod (int_expr e1, ctype ty)
        in
        let e = locate (mkexpr cast e.eloc) in
        e#node

      | _ -> (expr e)#node
    in
    mkexpr enode e.eloc
  in

  match e.enode with
    | CastE _ -> int_expr e
    | _ -> int_expr (new_exp ~loc:e.eloc (CastE (typeOf e, Check, e)))

and lval pos = function
  | Var v, NoOffset -> mkexpr (JCPEvar v.vname) pos

  | Var _v, _off -> assert false (* Should have been rewritten *)

  | Mem _e, NoOffset -> assert false (* Should have been rewritten *)

  | Mem e, Field(fi,off) ->
      assert (off = NoOffset); (* Others should have been rewritten *)
      let e = expr e in
      if not fi.fcomp.cstruct then (* field of union *)
        locate (mkexpr (JCPEcast(e,ctype fi.ftype)) pos)
      else
        let repfi = Retype.FieldUF.repr fi in
        let e,fi =
          if Fieldinfo.equal fi repfi then
            e,fi
          else
            let caste =
              locate
                (mkexpr
                   (JCPEcast(e,
                             ctype (TPtr(TComp(repfi.fcomp,
                                               empty_size_cache (),[]),[]))))
                   pos)
            in
            caste,repfi
        in
        locate (mkexpr (JCPEderef(e,fi.fname)) pos)

  | Mem e, Index(ie,Field(fi,off)) ->
      assert (off = NoOffset); (* Others should have been rewritten *)
      (* Normalization made it equivalent to simple add *)
      let e = mkexpr (JCPEbinary(expr e,`Badd,expr ie)) pos in
      if not fi.fcomp.cstruct then (* field of union *)
        locate (mkexpr (JCPEcast(e,ctype fi.ftype)) pos)
      else
        let repfi = Retype.FieldUF.repr fi in
        let e,fi =
          if Fieldinfo.equal fi repfi then
            e,fi
          else
            let caste =
              locate
                (mkexpr
                   (JCPEcast(e,
                             ctype (TPtr(TComp(repfi.fcomp,
                                               empty_size_cache (),[]),[]))))
                   pos)
            in
            caste,repfi
        in
        locate (mkexpr (JCPEderef(e,fi.fname)) pos)

  | Mem _e, Index _ as lv ->
      Jessie_options.fatal
        ~current:true "Unexpected lval %a" Printer.pp_lval lv

let keep_only_declared_nb_of_arguments vi l =
  let _,args,is_variadic, _ = splitFunctionTypeVI vi in
  if args=None then
    (Console.warning "skipping all arguments of implicit prototype %s" vi.vname;
     [])
  else if is_variadic then Console.unsupported "unsupported variadic functions"
  else l

let adjust_rvalue_to_bitfield ~lv ~typ e =
  match lastOffset (snd lv) with
  | Field (fi, NoOffset)
    when isArithmeticType typ && the fi.fsize_in_bits <> bitsSizeOf typ ->
    mkexpr (JCPEcast (e, ctype ~bitsize:(the fi.fsize_in_bits) fi.ftype)) e#pos
  | _ -> e

let instruction = function
  | Local_init _     -> assert false
  | Set (lv, e, pos) ->
    let e =
      begin match unrollType (typeOfLval lv) with
      | TEnum _ as newt ->
        begin match unrollType (typeOf e) with
        | TInt _ -> mkCast ~force:true ~overflow:Check ~e ~newt
        | _ -> e
        end
      | _ -> e
      end |>
      expr |>
      adjust_rvalue_to_bitfield ~lv ~typ:(typeOf e)
    in
    let enode = JCPEassign (lval pos lv, e) in
    (locate (mkexpr enode pos))#node

  | Call (None, { enode = Lval (Var v, NoOffset) }, eargs, pos) ->
    begin match Ast.Vi.Function.of_varinfo v with
    | Some v ->
      let open Ast.Vi.Function in
      if is_assert v then
        JCPEassert ([new identifier Name.Behavior.default],
                    Aassert, locate (boolean_expr (as_singleton eargs)))
      else
        let enode =
          if is_free v || is_kfree v || is_kzfree v then
            let arg = as_singleton eargs in
            let subarg = Ast.Exp.strip_casts_to (TPtr ((Type.Composite.Struct.void () :> typ), [])) arg in
            let arg = if isPointerType (typeOf subarg) then subarg else arg in
            JCPEfree(expr arg)
          else
            JCPEapp ((v :> varinfo).vname,
                     [],
                     keep_only_declared_nb_of_arguments
                       (v : _ Ast.Vi.t :> varinfo)
                       (List.map expr eargs))
        in
        (locate (mkexpr enode pos))#node
    | None -> Console.unsupported "Undefined function call: %a" Printer.pp_varinfo v
    end
  | Call (Some lv, { enode = Lval (Var v, NoOffset) }, eargs, pos) ->
    begin match Ast.Vi.Function.of_varinfo v with
    | Some v ->
      let open Ast.Vi.Function in
      let enode =
        let lv_size lv_type =
          let r = Type.size_in_bits_exn lv_type lsr 3 in
          Integer.(if r = 0L then one else of_int64 r)
        in
        if is_malloc v || is_memdup v || is_kmalloc v || is_kmemdup v || is_realloc v then
          let lvtyp = pointed_type (typeOfLval lv) in
          let lvtyp =
            let void = (Common.Type.Composite.Struct.void () :> typ) in
            if (is_kmemdup v || is_memdup v) && (isVoidType lvtyp || not @@ need_cast void lvtyp)
            then pointed_type @@ typeOf @@ Ast.Exp.strip_casts_to (TPtr (void, [])) @@ List.hd eargs
            else lvtyp
          in
          let lvsiz = lv_size lvtyp in
          let arg =
            try
              if is_malloc v then as_singleton eargs
              else if is_memdup v then
                match eargs with [ _; arg ] -> arg | _ -> raise Exit
              else if is_kmalloc v then
                match eargs with [ arg; _ ] -> arg | _ -> raise Exit
              else if is_kmemdup v then
                match eargs with [ _; arg; _ ] -> arg | _ -> raise Exit
              else (* realloc *)
                match eargs with [ _; arg ] -> arg | _ -> raise Exit
            with
            | Invalid_argument _
            | Exit ->
              Console.unsupported "incorrect arguments for Jessie builtin allocation function %s" (v :> varinfo).vname
          in
          let arg = stripInfo arg in
          let loc = arg.eloc in
          let ty,arg = match arg.enode with
            | Info _ -> assert false
            | Const c when is_integral_const c ->
                let allocsiz = Integer.div (value_of_integral_expr arg) lvsiz in
                let siznode = JCPEconst (JCCinteger (Integer.to_string allocsiz)) in
                lvtyp, mkexpr siznode pos
            | BinOp (Mult oft, arg, nelem, _ty)
              when possible_value_of_integral_expr arg <> None || possible_value_of_integral_expr nelem <> None ->
                let arg, nelem = if possible_value_of_integral_expr arg <> None then arg, nelem else nelem, arg in
                let factor = Integer.div (value_of_integral_expr arg) lvsiz in
                let siz =
                  if Integer.equal factor Integer.one then expr nelem
                  else
                    let factor = Ast.Exp.const factor in
                    expr (mkBinOp ~loc (Mult oft) nelem factor)
                in
                lvtyp, siz
            | _ ->
                if Integer.equal lvsiz Integer.one then lvtyp, expr arg
                else
                  let esiz = constant_expr ~loc lvsiz in
                  lvtyp, expr (mkBinOp ~loc (Div Check) arg esiz)
          in
          let name_of_type = match unrollType ty with
            | TComp(compinfo,_,_) -> compinfo.cname
            | _ -> assert false
          in
          let alloc = JCPEalloc (arg, name_of_type) in
          if is_kmalloc v then
            let cond =
              let zero_expr =
                mkexpr (JCPEcast (zero_expr, mktype @@ JCPTidentifier ("int32", []))) pos
              in
              mkexpr
                (JCPEbinary (mkexpr (JCPEapp (Name.Logic_function.nondet_int, [], [])) pos, `Bneq, zero_expr))
                pos
            in
            JCPEif (cond, mkexpr alloc pos, null_expr)
          else
            alloc (* Unconditionally successful allocation *)
        else if is_calloc v then
          let nelem, elsize =
            match eargs with
            | [nelem; elsize] -> nelem, elsize
            | _ -> assert false
          in
          let arg = stripInfo elsize in
          let loc = arg.eloc in
          let ty, arg =
            match arg.enode with
            | Info _ -> assert false
            | Const c when is_integral_const c ->
                let lvtyp = pointed_type (typeOfLval lv) in
                let lvsiz = lv_size lvtyp in
                let factor = Integer.div (value_of_integral_expr arg) lvsiz in
                let siz =
                  if Integer.equal factor Integer.one then
                    expr nelem
                  else
                    let factor = constant_expr ~loc factor in
                    expr (mkBinOp ~loc (Mult Check) nelem factor)
                in
                lvtyp, siz
            | _ ->
                let lvtyp = pointed_type (typeOfLval lv) in
                let lvsiz = lv_size lvtyp in
                let esiz = constant_expr ~loc lvsiz in
                lvtyp,
                expr (mkBinOp ~loc (Div Check) (mkBinOp ~loc (Mult Check) nelem elsize) esiz)
          in
          let name_of_type = match unrollType ty with
            | TComp(compinfo,_,_) -> compinfo.cname
            | _ -> assert false
          in
          JCPEalloc(arg,name_of_type)
        else
          JCPEapp((v :> varinfo).vname,[],
                  keep_only_declared_nb_of_arguments
                    (v : _ Ast.Vi.t :> varinfo)
                    (List.map expr eargs))
      in
      let lvty = typeOfLval lv in
      let rety = getReturnType (v :> varinfo).vtype in
      let call = locate (adjust_rvalue_to_bitfield ~lv ~typ:rety @@ mkexpr enode pos) in
      let enode =
        if Typ.equal lvty rety
          || is_malloc v
          || is_memdup v
          || is_realloc v
          || is_calloc v
        then
          JCPEassign(lval pos lv,call)
        else
          let tmpv = makeTempVar (get_curFundec()) (getReturnType (v : _ Ast.Vi.t :> varinfo).vtype) in
          let tmplv = Var tmpv, NoOffset in
          let cast =
            new_exp ~loc:pos (CastE (lvty, Check, new_exp ~loc:pos (Lval tmplv)))
          in
          let tmpassign = JCPEassign(lval pos lv,expr cast) in
          JCPElet(None,tmpv.vname,Some call,locate (mkexpr tmpassign pos))
      in
      (locate (mkexpr enode pos))#node
    | None -> Console.unsupported "Undefined function call: %a" Printer.pp_varinfo v
    end
  | Call _ -> Console.unsupported ~current:true "function pointers"

  | Asm _ -> Console.unsupported ~current:true "inline assembly"

  | Skip _pos -> JCPEconst JCCvoid

  | Code_annot ({ annot_content = APragma (Jessie_pragma _) } as ca, loc) ->
    (locate (List.hd @@ fst @@ code_annot loc ([], None) ca))#node

  | Code_annot _ -> Console.unsupported ~current:true "code annotation"

let rec statement s =
  let pos = Stmt.loc s in
  CurrentLoc.set pos;

  let assert_before, contract =
    Annotations.fold_code_annot
      (fun e ca acc -> code_annot ~e pos acc ca) s ([],None)
  in
  let snode = match s.skind with
    | Instr i -> instruction i

    | Return(Some e,_) -> JCPEreturn(expr e)

    | Return(None,_pos) ->
        JCPEreturn(mkexpr (JCPEconst JCCvoid) pos)

    | Goto(sref,_pos) ->
        (* Pick the first non-case label in the list of labels associated to
         * the target statement
         *)
        let labels = filter_out is_case_label !sref.labels in
        assert (not (labels = []));
        JCPEgoto(label (List.hd labels))

    | Break _pos ->
        assert false (* Should not occur after [prepareCFG] *)

    | Continue _pos ->
        assert false (* Should not occur after [prepareCFG] *)

    | If(e,bl1,bl2,_) ->
        JCPEif(boolean_expr ~to_locate:true e, block bl1, block bl2)

    | Switch(e,bl,slist,pos) ->
        let case_blocks stat_list case_list =
          let rec next_case curr_list final_list stat_list case_list =
            match stat_list,case_list with
              | curr_stat :: rest_stat, curr_case :: rest_case ->
                  if curr_case.sid = curr_stat.sid then
                    (* Beginning of a new case. Add previous case to list
                       if not empty. *)
                    let add_to_list cond e l = if cond e then e::l else l in
                    let not_empty_list = function [] -> false | _ -> true in
                    let final_list =
                      add_to_list not_empty_list (List.rev curr_list) final_list
                    in
                    let curr_list = [curr_stat] in
                    next_case curr_list final_list rest_stat rest_case
                  else
                    let curr_list = curr_stat :: curr_list in
                    next_case curr_list final_list rest_stat case_list
              | [], [] ->
                  if List.length curr_list <> 0 then
                    List.rev curr_list :: final_list
                  else
                    final_list
              | [], _ ->
                  (* More cases than available. *)
                  assert false
              | stat_list, [] ->
                  (List.rev_append curr_list stat_list) :: final_list
          in
          List.rev (next_case [] [] stat_list case_list)
        in
        let switch_label = function
          | Label _ -> assert false
          | Case(e,_) -> Some (locate (expr e))
          | Default _ -> None
        in
        let case = function
          | [] -> assert false
          | case_stmt :: _ as slist ->
              let switch_labels = List.filter is_case_label case_stmt.labels in
              let labs = List.map switch_label switch_labels in
              let slist = mkexpr (JCPEblock(statement_list slist)) pos in
              labs, slist
        in
        let rec flatten s =
          List.flatten @@
          List.map
            (fun s ->
              match s.skind with
              | Block b ->(let ss = flatten b.bstmts in
                           may (fun s' -> s'.labels <- s.labels @ s'.labels; s.labels <- []) (List.nth_opt ss 0);
                           ss)
              | _       -> [s])
            s
        in
        let rec push s =
          match s.skind with
          | Block b -> may_map push ~dft:s @@ List.nth_opt b.bstmts 0
          | _       -> s
        in
        let case_list = List.map case (case_blocks (flatten bl.bstmts) (List.map push slist)) in
        JCPEswitch(expr e,case_list)

    | Loop (_,bl,_pos,_continue_stmt,_break_stmt) ->
        let treat_loop_annot _ annot (beh,var as acc) =
          match annot.annot_content with
            | AVariant(v,rel) ->
                begin
                  match var with
                    | None ->
                        begin
                          match rel with
                            | Some r ->
                                (beh, Some (locate (term v),
                                            Some (new identifier r)) )
                            | None ->
                                (beh,Some (locate (term v) ,None ))
                        end
                    | Some _ -> assert false (* At most one variant *)
                end
            | AInvariant(ids,true,inv) ->
                ((ids,[locate (pred inv)],WritesAny)::beh,var)
            | AAssigns(ids,assign) ->
                ((ids,[],assign)::beh,var)
            | APragma _ -> (* ignored *) acc
            | AAllocation _ -> (* Ignored *) acc
            (* No loop annotation. *)
            | AAssert _ | AStmtSpec _ | AInvariant _ | AExtended _-> acc
        in
        let behs,variant =
          Annotations.fold_code_annot treat_loop_annot s ([],None)
        in
        (* Locate the beginning of the loop, to serve as location for generated
         * invariants and variants.
         *)
        (*         let lab = reg_pos pos in *)
        (* TODO: add loop-assigns to Jessie *)
        (* PARTIALLY DONE: added them as new jessie loop behaviors *)
        let behs = List.map
          (fun (beh_names,invs,ass) ->
             let beh_names = built_behavior_ids beh_names in
             let inv =
               match invs with
                 | [] -> None
                 | _ -> Some (mkconjunct invs pos)
             in
             let ass = assigns ass in
             (beh_names,inv,ass))
          behs
        in
        JCPEwhile(true_expr,behs,variant,block bl)

    | Block blk ->
      let inlined_stmt =
        match blk.bstmts with
        | [] -> None
        | [ { skind = Instr _ | Return _ | Goto _ | Break _ | Continue _ | Block _ } as s' ] ->
          begin match blk.bstmts, blk.battrs, blk.blocals with
          | _ :: _ :: _, _, _ | _, _, _ :: _ | _, _ :: _, _ -> None
          | _, _, _ when not (Annotations.has_code_annot s) ->
            s'.labels <- s.labels @ s'.labels;
            Some s'
          | _ -> None
          end
        | _ -> None
      in
      begin match inlined_stmt with
      | None -> JCPEblock (statement_list blk.bstmts)
      | Some s -> (statement s)#node
      end

    | UnspecifiedSequence seq ->
      (* [VP] TODO:
         take into account undefined behavior tied to the effects of the statements... *)
      JCPEblock (statement_list (List.map (fun (x, _, _, _, _) -> x) seq))

    | TryFinally _ | TryExcept _ | Throw _ | TryCatch _ | AsmGoto _ -> assert false
  in
  (* Prefix statement by all non-case labels *)
  let labels = filter_out is_case_label s.labels in
  let s = mkexpr snode pos in
  let s =
    match contract with
      | None -> s
      | Some sp ->
          let sp,_cba,_dba = spec "statement contract" sp in
          let requires, decreases, behaviors =
            List.fold_left
              (fun (r,d,b) c ->
                 match c with
                   | JCCrequires p ->
                       begin match r with
                         | None -> (Some p,d,b)
                         | Some _ -> Console.unsupported "multiple requires on statement contract"
                       end
                   | JCCdecreases(v,p) ->
                       begin match d with
                         | None -> (r,Some(v,p),b)
                         | Some _ -> Console.unsupported "multiple decreases on statement contract"
                       end
                   | JCCbehavior be -> (r,d,be::b))
              (None,None,[])
              sp
          in
          mkexpr
            (JCPEcontract(requires, decreases, behaviors, s))
            pos
  in
  let s = match assert_before @ [s] with
    | [s] -> s
    | slist -> mkexpr (JCPEblock slist) pos
  in
  List.fold_left (fun s lab -> mkexpr (JCPElabel(label lab,s)) pos) s labels

and statement_list slist =
  let rec rev_map ?(accu = []) =
    let rec has_last_return =
      function
      | [] -> false
      | [{ skind = Return _ }] -> true
      | [{ skind = Block { bstmts }}] -> has_last_return bstmts
      | _ :: l -> has_last_return l
    in
    function
    | [] -> accu
    | [{ skind = Block { bstmts }} as s] when has_last_return bstmts ->
      let start = List.hd bstmts in
      start.labels <- s.labels @ start.labels;
      rev_map ~accu bstmts
    | a :: l -> rev_map ~accu:(statement a :: accu) l
  in
  List.rev (rev_map slist)

and block bl =
  match bl.bstmts with
    | [] -> mkexpr (JCPEconst JCCvoid) Why_loc.dummy_position
    | [s] -> statement s
    | slist -> mkexpr (JCPEblock(statement_list slist)) Why_loc.dummy_position


(*****************************************************************************)
(* Cil to Jessie translation of global declarations                          *)
(*****************************************************************************)

let drop_on_unsupported_feature = false

let try_builtin_fun_or_pred ltyp_opt name labels params body f =
  let open Pervasives in
  let u = "\\(u?\\)" in
  let int = "int" in
  let compl = "complement_to_u" in
  let bits = "\\(8\\|16\\|32\\|64\\)" in
  let int_from_bitsize_u x = (Type.Integral.of_bitsize_u x :> typ) in
  let matches, group = Str.((fun r -> string_match r name 0), fun n -> matched_group n name) in
  let equal_int_types t1 t2 =
    let open Logic_utils in
    if map_pair (isLogicType @@ fun _ -> true) (t1, t2) = (true, true)
    then
      let t1, t2 = map_pair logicCType (t1, t2) in
      isIntegralType t1 && isIntegralType t2 &&
      let have_eq f = f t1 = f t2 in
      have_eq isSignedInteger &&
      have_eq bitsSizeOf
    else false
  in
  if matches @@ Str.regexp @@ u ^ int ^ bits ^ "_as_" ^ u ^ int ^ bits then
    let from_unsigned, to_unsigned = map_pair ((<>) "" % group) (1, 3) in
    let from_bitsize, to_bitsize = map_pair (int_of_string % group) (2, 4) in
    let from_type, to_type = map_pair int_from_bitsize_u ((from_bitsize, from_unsigned), (to_bitsize, to_unsigned)) in
    let part_type, whole_type =
      if (from_bitsize, not from_unsigned) < (to_bitsize, not to_unsigned)
      then from_type, to_type
      else to_type, from_type
    in
    match ltyp_opt, labels, params, body with
    | None, [], { lv_type = whole_type' } :: ps, JCnone
      when
      equal_int_types whole_type' (Ctype whole_type) &&
      List.for_all (fun lv -> equal_int_types lv.lv_type @@ Ctype part_type) ps ->
      []
    | _ -> Console.unsupported "builtin logic predicate %s redefinition or redeclaration with incompatible type" name
  else if matches @@ Str.regexp @@ compl ^ int ^ bits then
    let signed_type, unsigned_type =
      map_pair (fun u -> int_from_bitsize_u (int_of_string @@ group 1, u)) (false, true)
    in
    match ltyp_opt, labels, params, body with
    | Some ret_type, [], [{ lv_type }], JCnone
      when equal_int_types ret_type (Ctype unsigned_type) && equal_int_types lv_type (Ctype signed_type) ->
      []
    | _ -> Console.unsupported "builtin logic function %s redefinition or redeclaration with incompatible type" name
  else f()

let logic_variable v =
  let name = Extlib.may_map (fun v -> v.vname) ~dft:v.lv_name v.lv_origin in
  ltype v.lv_type, name

let rec annotation is_axiomatic annot =
  let default_label labs =
    match labs with
    | [] -> None
    | l :: _ -> Some l
  in
  match annot with
  | Dfun_or_pred (info,pos) ->
      let pred' = pred in
      let term, terms, pred =
        let default_label = default_label info.l_labels in
        term ?default_label, terms ?default_label, pred ?default_label
      in
      CurrentLoc.set pos;
      begin
        try
        let params = List.map logic_variable info.l_profile in
        let body =
          match info.l_body with
          | LBnone -> JCnone
          | LBreads reads_tsets ->
              let reads =
                List.flatten
                  (List.map (fun x -> terms x.it_content) reads_tsets)
              in
              JCreads reads
          | LBpred p -> JCexpr(pred p)
          | LBinductive indcases ->
              let l =
                List.map
                  (fun (id,labs,_poly,p) ->
                     let pred = pred' ?default_label:(default_label labs) in
                     (new identifier id,logic_labels labs,pred p))
                  indcases
              in
              JCinductive l
          | LBterm t ->
            let t =
              if info.l_type = Some Linteger && t.term_type <> Linteger then
                Logic_const.term (TLogic_coerce (Linteger, t)) Linteger
              else
                t
            in
            JCexpr(term t)
        in
        let name =
          try
            let _ = Hashtbl.find jessie_builtins info.l_var_info.lv_name in
            info.l_var_info.lv_name
        with Not_found ->
          translated_name info []
        in
        try_builtin_fun_or_pred info.l_type name info.l_labels info.l_profile body @@
          fun () ->
             match info.l_type, info.l_labels, params with
               Some t, [], [] ->
                 let def = match body with
                   | JCnone | JCreads _ | JCinductive _ -> None
                   | JCexpr t -> Some t
                 in
                 [JCDlogic_var (ltype t, name,def)]
             | _ ->
                 [JCDlogic(Option.map ltype info.l_type,
                           name,[],
                           logic_labels info.l_labels,
                           params,body)]
      with (Unsupported _ | Log.FeatureRequest _)
        when drop_on_unsupported_feature ->
          Console.warning "Dropping declaration of predicate %s@."
            info.l_var_info.lv_name ;
          []
      end

  | Dlemma (name, is_axiom, labels, _poly, property, _, pos) ->
      let pred = pred ?default_label:(default_label labels) in
      CurrentLoc.set pos;
      ignore
        (reg_position ~id:name
           ~name:("Lemma " ^ name) pos);
      begin try
        [JCDlemma (name, is_axiom, [], logic_labels labels, locate ~pos @@ pred property)]
      with (Unsupported _ | Log.FeatureRequest _)
          when drop_on_unsupported_feature ->
            Console.warning "Dropping lemma %s@." name; []
      end

  | Dinvariant (property,pos) ->
      begin try
        CurrentLoc.set pos;
        let n = translated_name property [] in
        [JCDglobal_inv(n,pred (Logic_utils.get_pred_body property))]
      with (Unsupported _ | Log.FeatureRequest _)
          when drop_on_unsupported_feature ->
            Console.warning "Dropping invariant %s@." property.l_var_info.lv_name ;
            []
      end

  | Dtype_annot (annot,pos) ->
      begin try
        CurrentLoc.set pos;
        let n = translated_name annot [] in
        [JCDlogic(
           None,n, [],logic_labels annot.l_labels,
           List.map logic_variable annot.l_profile,
           JCexpr(pred (Logic_utils.get_pred_body annot)))]
      with (Unsupported _ | Log.FeatureRequest _)
          when drop_on_unsupported_feature ->
            Console.warning "Dropping type invariant %s@." annot.l_var_info.lv_name;
            []
      end

  | Dtype (info,pos) when info.lt_params=[] ->
      CurrentLoc.set pos;
      let myself = mktype (JCPTidentifier (info.lt_name,[])) in
      let mydecl = JCDlogic_type (info.lt_name,[]) in
      let axiomatic ctors =
        let cons = List.map
          (fun x ->
             let prms = ref (-1) in
             let make_params t =
               incr prms;
               ltype t, Printf.sprintf "x%d" !prms  (*TODO: give unique name*)
             in
             match x.ctor_params with
               [] -> JCDlogic_var(myself,x.ctor_name,None)
             | l ->
                 let params = List.map make_params l in
                 JCDlogic(Some myself,x.ctor_name,[],[],params,
                          JCreads []
                            (*(List.map (fun (_,x) ->
                              mkexpr (JCPEvar x) pos) params)*)))
          ctors
        in
        let tag_fun = JCDlogic (Some (mktype (JCPTnative Tinteger)),
                                info.lt_name ^ "_tag",[],[],[myself,"x"],
                                JCreads[])
        in
        let tag_axiom cons (i,axioms) =
          let prms = ref(-1) in
          let param t =
            incr prms;
            let prms_name = Printf.sprintf "x%d" !prms in
            (* TODO: give unique name *)
            (fun x ->
               mkexpr (JCPEquantifier(Forall,ltype t,
                                      [new identifier prms_name], [],x)) pos),
            mkexpr (JCPEvar prms_name) pos
          in
          let (quant,args) =
            List.fold_right
              (fun arg (quants,args) ->
                 let quant,arg = param arg in
                 ((fun x -> quant(quants x)), arg::args))
              cons.ctor_params ((fun x -> x),[])
          in
          let expr = match cons.ctor_params with
              [] -> JCPEvar cons.ctor_name
            | _ -> JCPEapp(cons.ctor_name,[],args)
          in
          let pred =
            quant
              (mkexpr
                 (JCPEbinary
                    (mkexpr (JCPEapp (info.lt_name ^ "_tag",[],
                                      [mkexpr expr pos])) pos,
                     `Beq,
                     mkexpr(JCPEconst(JCCinteger (Int64.to_string i))) pos))
                 pos)
          in
          (i+one,
           JCDlemma(cons.ctor_name ^ "_tag_val",true,[],[], pred)
           ::axioms)
        in
        let (_,axioms) = List.fold_right tag_axiom ctors (zero,[]) in
        let xvar = mkexpr (JCPEvar "x") pos in (* TODO: give unique name *)
        let one_case cons =
          let prms = ref(-1) in
          let param t =
            incr prms;
            let prms_name = Printf.sprintf "x%d" !prms in
            (* TODO: give unique name *)
            ((fun x ->
                mkexpr (JCPEquantifier(Exists,ltype t,
                                       [new identifier prms_name], [],x)) pos),
             mkexpr (JCPEvar prms_name) pos)
          in let (quant,args) =
            List.fold_right
              (fun arg (quants,args) ->
                 let quant,arg = param arg in
                 ((fun x -> quant(quants x)), arg::args))
              cons.ctor_params ((fun x -> x),[])
          in
          quant
            (mkexpr
               (JCPEbinary(xvar,`Beq,
                           mkexpr (JCPEapp(cons.ctor_name,[],args)) pos)) pos)
        in
        match ctors with
          [] -> cons
        | [x] ->
            cons @
              [JCDlemma(info.lt_name ^ "_inductive", true, [], [],
                        (mkexpr (JCPEquantifier
                                   (Forall,myself,
                                    [new identifier "x"], [],one_case x)) pos))]
        | x::l ->
            tag_fun :: cons @ axioms @
              [JCDlemma(info.lt_name ^ "_inductive", true, [], [],
                        mkexpr
                          (JCPEquantifier(
                             Forall,myself,
                             [new identifier "x"], [],
                             List.fold_right
                               (fun cons case ->
                                  mkexpr (JCPEbinary(case,`Blor,
                                                     one_case cons)) pos)
                               l (one_case x))) pos)]
      in
      (*NB: axioms stating that two values beginning with different
        symbols are different are not generated. *)
      let axiomatic = match info.lt_def with
          None -> [mydecl]
        | Some (LTsum cons) -> mydecl::axiomatic cons
        | Some (LTsyn _) -> [] (* We'll expand the type anyway *)
      in
      (match axiomatic with
           [] -> []
         | _ when is_axiomatic -> axiomatic
         | _ ->
             [JCDaxiomatic (info.lt_name ^ "_axiomatic",
                            List.map (fun x -> mkdecl x pos) axiomatic)])

  | Dtype _ -> Console.unsupported "type definitions"
  | Dvolatile _ -> Console.unsupported "volatile variables"
  | Dmodel_annot _ ->
      (* already handled in norm.ml *)
      []
  | Dcustom_annot _ -> Console.unsupported "custom annotation"
  | Daxiomatic(id,l,_,pos) ->
    if not (Filename.basename (fst pos).Lexing.pos_fname = Name.File.blockfuns_include) then begin
      CurrentLoc.set pos;
      let l = List.fold_left (fun acc d -> (annotation true d)@acc) [] l in
      if l <> [] then
        [JCDaxiomatic (id, List.map (fun d -> mkdecl  d pos) @@ List.rev l)]
      else
        []
    end else
      []

let default_field_modifiers = (false, false)

let global vardefs g =
  let pos = Global.loc g in
  CurrentLoc.set pos;
  let dnodes =
    match g with
    | GType _ -> [] (* No typedef in Jessie *)

    | GCompTag (compinfo, pos) when compinfo.cstruct -> (* struct type *)
      let field fi =
        let add_padding size acc =
          if Pervasives.(size > 0) then
            acc @ [default_field_modifiers, type_of_padding, Name.unique "padding", size]
          else
            acc
        in
        if hasAttribute Name.Attr.padding fi.fattr then
          opt_fold add_padding fi.fsize_in_bits [] |>
          opt_fold add_padding fi.fpadding_in_bits
        else
          opt_fold add_padding fi.fpadding_in_bits @@
          [default_field_modifiers,
           ctype ?bitsize:fi.fsize_in_bits fi.ftype,
           fi.fname,
           Option.value_fatal ~in_:"global:field" fi.fsize_in_bits]
      in
      let model_field mi =
        default_field_modifiers,
        ltype mi.mi_field_type,
        mi.mi_name,
        0
      in
      let ty = TComp (compinfo, empty_size_cache (), []) in
      let fields =
        List.fold_right
          (fun fi acc ->
             let repfi = Retype.FieldUF.repr fi in
             let is_embedded_padding =
               (* Padding fields (always at the end) are not taken into account in inheritance relation,
                  therefore they are representants of themselves anyway *)
               hasAttribute Name.Attr.embedded fi.fattr && hasAttribute Name.Attr.padding fi.fattr
             in
             let parentty = Retype.parent_type ty in
             if Fieldinfo.equal fi repfi && (not is_embedded_padding || not @@ has_some parentty)
             then
               field fi @ acc
             else
               acc)
          compinfo.cfields
          []
      in
      let fields =
        List.fold_right
          (fun mi acc -> model_field mi :: acc)
          (Norm.model_fields compinfo)
          fields
      in
      begin match Retype.parent_type ty with
      | Some parentty ->
        let parent = Type.Composite.(compinfo_cname @@ of_typ_exn parentty) in
        [JCDtag (compinfo.cname, [], Some (parent, []), fields, [])]
      | None ->
        try
          ignore (Typ.Hashtbl.find Norm.generated_union_types ty);
          [JCDtag (compinfo.cname, [], None, fields, [])]
        with Not_found ->
          let id = mkidentifier compinfo.cname pos in
          [JCDtag (compinfo.cname, [], None, fields, []);
           JCDvariant_type (compinfo.cname, [id])]
      end

    | GCompTag (compinfo, pos) -> (* union type *)
        assert (not compinfo.cstruct);
        let field fi =
          let ty = pointed_type fi.ftype in
          mkidentifier (Type.Composite.(compinfo_cname @@ of_typ_exn ty)) pos
        in
        let union_id = mkidentifier compinfo.cname pos in
        let union_size = match compinfo.cfields with
          | [] -> 0
          | fi::_ ->
              Pervasives.(+) (the fi.fsize_in_bits) (the fi.fpadding_in_bits)
        in
        let padding =
          if union_size = 0 then [] else
            [default_field_modifiers,
             type_of_padding, Name.unique "padding", union_size]
        in
        let union_tag = JCDtag (compinfo.cname, [], None, padding, []) in
        let fields = List.map field (Type.Composite.Ci.proper_fields compinfo) in
        [JCDvariant_type (compinfo.cname, union_id :: fields); union_tag]

    | GCompTagDecl _ -> [] (* No struct/union declaration in Jessie *)

    | GEnumTag (enuminfo, _pos) ->
      assert (not (enuminfo.eitems = []));
      let enums =
        List.map
          (fun {eival = enum} -> value_of_integral_expr enum) enuminfo.eitems
      in
      let emin =
        List.fold_left (fun acc enum ->
          if Integer.lt acc enum then acc else enum)
          (List.hd enums)
          enums
      in
      let min = Num.num_of_string (Integer.to_string emin) in
      let emax =
        List.fold_left (fun acc enum ->
          if Integer.gt acc enum then acc else enum)
          (List.hd enums)
          enums
      in
      let max = Num.num_of_string (Integer.to_string emax) in
      [JCDenum_type(enuminfo.ename,min,max)]

    | GEnumTagDecl _ -> [] (* No enumeration declaration in Jessie *)

    | GVarDecl (v, pos)
    | GFunDecl (_, v, pos) ->
      let excluded_function_names =
        Name.
          [Predicate.valid_string;
           Predicate.valid_wstring;
           Function.assert_;
           Function.free;
           Function.kfree;
           Function.malloc;
           Function.memdup;
           Function.kmalloc;
           Function.kzalloc;
           Function.kmemdup;
           Function.calloc;
           Function.realloc]
        in
        let has_specialization vi =
          try
            ignore @@ Globals.Functions.find_by_name (vi.vname ^ "__type");
            true
          with Not_found -> false
        in
        let is_specialization_template vi =
          Filename.basename (fst vi.vdecl).Lexing.pos_fname = Name.File.blockfuns_include
        in
        (* Keep only declarations for which there is no definition *)
        if List.mem v vardefs ||
           (isFunctionType v.vtype &&
             (List.mem v.vname excluded_function_names ||
              is_specialization_template v ||
              has_specialization v))
        then []
        else if isFunctionType v.vtype then
          let rtyp = match unrollType v.vtype with
            | TFun(rt,_,_,_) -> rt
            | _ -> assert false
          in
          let id = mkidentifier v.vname pos in
          let kf = Globals.Functions.get v in
          Jessie_options.debug
            "Getting spec of %s" (Kernel_function.get_name kf);
          let funspec = Annotations.funspec kf in
          Jessie_options.debug "OK";
          let params = Globals.Functions.get_params kf in
          let formal v = true, ctype v.vtype, Name.unique_if_empty v.vname in
          let formals = List.map formal params in
          let s,_cba,_dba = spec v.vname funspec in
          [JCDfun(ctype rtyp,id,formals,s,None)]
        else
          [JCDvar(ctype v.vtype,v.vname,None)]

    | GVar(v,{init=None},_pos) ->
        [JCDvar(ctype v.vtype,v.vname,None)]

    | GVar(_v,_iinfo,_pos) ->
        (* Initialization should have been rewritten as code in an
         * initialization function, that is called by the main function in
         * global analyses and ignored otherwise.
         *)
        assert false

    | GFun(f,pos) ->
        set_curFundec f;
        if f.svar.vname = Name.Function.assert_
          || f.svar.vname = Name.Function.free then []
        else
          let rty =
            match unrollType f.svar.vtype with
            | TFun(ty,_,_,_) -> ty
            | _ -> assert false
          in
          let formal v = true, ctype v.vtype, v.vname in
          let formals = List.map formal f.sformals in
          let id = mkidentifier f.svar.vname f.svar.vdecl in
          let funspec =
            Annotations.funspec (Globals.Functions.get f.svar)
          in
          begin try
            let local v =
              mkexpr (JCPEdecl(ctype v.vtype,v.vname,None)) v.vdecl
            in
            let locals = List.rev (List.rev_map local f.slocals) in
            let body = mkexpr (JCPEblock(statement_list f.sbody.bstmts)) pos in
            let s,cba,dba = spec f.svar.vname funspec in
            let body =
              List.fold_left
                (fun acc a ->
                   (mkexpr
                      (JCPEassert([],
                                  Acheck,
                                  mkexpr
                                    (JCPElabel("complete_behaviors",a))
                                    a#pos))
                      a#pos)
                   :: acc)
                (locals @ [body]) cba
            in
            let body =
              List.fold_left
                (fun acc a ->
                   (mkexpr
                      (JCPEassert([],
                                  Acheck,
                                  mkexpr
                                    (JCPElabel("disjoint_behaviors",a))
                                    a#pos))
                      a#pos)
                   :: acc)
                body dba
            in
            let body = mkexpr (JCPEblock body) pos in
            ignore
              (reg_position ~id:f.svar.vname
                 ~name:("Function " ^ f.svar.vname) f.svar.vdecl);
            [JCDfun(ctype rty,id,formals,s,Some body)]
          with (Unsupported _ | Log.FeatureRequest _)
              when drop_on_unsupported_feature ->
                Console.warning "Dropping definition of function %s@." f.svar.vname ;
                let s,_cba,_dba = spec f.svar.vname funspec in
                [JCDfun(ctype rty,id,formals,s,None)]
          end

    | GAsm _ ->
        Console.unsupported "assembly code"

    | GPragma _ -> [] (* Pragmas treated separately *)

    | GText _ -> [] (* Ignore text in Jessie *)

    | GAnnot(la,_) -> annotation false la

  in
  List.map (fun dnode -> mkdecl dnode pos) dnodes

let integral_type name ty bitsize =
  let conv = Num.num_of_string % Integer.to_string in
  let min = conv (Type.Integral.min_value ?bitsize ty) in
  let max = conv (Type.Integral.max_value ?bitsize ty) in
  mkdecl (JCDenum_type (name, min, max)) Why_loc.dummy_position

let integral_types () =
  Type.Integral.fold_all
    (fun name (ty, bitsize) acc ->
       match unrollType (ty : Type.Integral.t :> typ) with
       | TInt (ik, _)
         when ik <> IBool &&
              Option.map_default
                ~default:true
                ~f:Pervasives.((=) @@ Type.Integral.IKind.size_in_bytes ik * 8) bitsize ->
         acc
       | _ -> integral_type name ty bitsize :: acc)
    []

let type_conversions () =
  let typconv_axiom ty1 ty1_to_ty2 ty2_to_ty1 =
    let x = PExpr.mkvar ~name:"x" () in
    let app1 = PExpr.mkapp ~fun_name:ty1_to_ty2 ~args:[x] () in
    let app2 = PExpr.mkapp ~fun_name:ty2_to_ty1 ~args:[app1] () in
    let eq = PExpr.mkeq ~expr1:x ~expr2:app2 () in
    let forall =
      PExpr.mkforall ~typ:(ctype ty1)
        ~vars:[new identifier "x"] ~body:eq ()
    in
    PDecl.mklemma_def ~name:(Name.Logic.unique (ty1_to_ty2 ^ "_axiom")) ~axiom:true
      ~body:forall ()
  in
  Hashtbl.fold
    (fun _ (ty1,ty2,ty1_to_ty2,ty2_to_ty1) acc ->
       [
         PDecl.mklogic_def ~typ:(ctype ty2) ~name:ty1_to_ty2
           ~params:[ctype ty1, "x"] ~reads:[] ();
         PDecl.mklogic_def ~typ:(ctype ty1) ~name:ty2_to_ty1
           ~params:[ctype ty2, "x"] ~reads:[] ();
         typconv_axiom ty1 ty1_to_ty2 ty2_to_ty1;
         typconv_axiom ty2 ty2_to_ty1 ty1_to_ty2
       ] @ acc
    ) type_conversion_table []

let get_compinfo globals =
  let module H = Datatype.String.Hashtbl in
  let cis = H.create 10 in
  List.iter
    (function GCompTag (ci, _) when ci.cstruct -> H.add cis ci.cname ci | _ -> ())
    globals;
  fun t ->
  try
    Some (H.find cis (wrapper_name t))
  with
  | Not_found -> None

(* Produces two axiomatics for every pair of integral types whose structures are voidP subtags.
   The first aximatic specifies pointer type (i.e. jessie "tag") reinterpretation constraints.
   We can regard a pointer p as having some type B * for integral type B if it has type A * for some integral type A
   and is valid in range 0..(bit_size_of(B)/bit_size_of(A)). Such reinterpretation can only be done immediately
   between the two control points specified by the predicate reinterpret_cast{L1, L2}(p).
   The second axiomatic specifies contraints on the pointed memory re-interpreted as the value of the new pointed type.
 *)
let memory_reinterpretation_predicates get_compinfo () =
  let open! Pervasives in
  (* Returns a pair of lists containing axiom and predicate definitions for the two axiomatics.
     Should be called for each pair of possible types to collect all necessary definitions. *)
  let memory_reinterpretation_predicates =
    (* The hashtable is used to ensure that predicate for each type conversion is defined only once.
       This is useful for signed types as they require the corresponding predicates for the unsigned counterparts. *)
    let val_cast_pred_memo = Hashtbl.create 16 in
    fun ((name1, type1, bitsize1), (name2, type2, bitsize2)) ->

    let (part_name, part_bitsize), (whole_name, whole_bitsize) =
      let pair1 = name1, bitsize1 and pair2 = name2, bitsize2 in
      if (bitsize1, Type.Integral.is_signed type1) < (bitsize2, Type.Integral.is_signed type2)
      then pair1, pair2
      else pair2, pair1
    in

    let open! PExpr in
    let var name = mkvar ~name (), new identifier name in
    let tinteger = mktype (JCPTnative Tinteger) in
    let mkeq expr1 expr2 = mkeq ~expr1 ~expr2 () in

    let v = whole_bitsize / part_bitsize in
    let d, w =
      map_pair
        (fun n -> mkint ~valuestr:Integer.(to_string @@ two_power_of_int n) ())
        (part_bitsize, whole_bitsize)
    in
    let integral_type name = mktype (JCPTidentifier (name, [])) in
    let add_u, del_u =
      let ensure_result f s = let s = f s in Type.Integral.add_by_name s; s in
      let add_u s = if s.[0] <> 'u' then "u" ^ s else s in
      let del_u s = if s.[0] = 'u' then Str.string_after s 1 else s in
      ensure_result add_u, ensure_result del_u
    in
    let guard_declarations ~name bodies =
      if Hashtbl.mem val_cast_pred_memo name then (name, [])
      else (
        Hashtbl.replace val_cast_pred_memo name ();
        name, bodies ()
      )
    in
    (* Predicates for integral type conversions *)
    let endian_map = List.(if theMachine.theMachine.little_endian then rev_map else map) in
    let conjunct_bw_pred name params body =
      mkand ~expr1:body ~expr2:(mkapp ~fun_name:("\\" ^ name) ~args:(List.map (fst % var % snd) params) ()) ()
    in
    let unsigned_split_pred () =
      let whole_name, part_name = map_pair add_u (whole_name, part_name) in
      let name = whole_name ^ "_as_" ^ part_name in
      guard_declarations ~name @@ fun () ->
        let svars =
          List.range (v - 1) `Downto 0 |>
          List.map @@ fun i -> Printf.(sprintf "a%d" i, sprintf "d%d" i)
        in
        let vars = List.map (map_pair @@ fst % var) svars in
        let body =
          let (an, dn), vars = List.(fdup2 hd tl vars) in
          let (_, sdn), svars = List.(fdup2 hd tl svars) in
          fst @@ ListLabels.fold_left2 vars svars
            ~init:(mkeq an dn, sdn)
            ~f:(fun (body, var) (ai, di) (_, sdi) ->
                  let expr1 = mkeq ai @@ mkbinary ~expr1:di ~op:`Bmod ~expr2:d () in
                  let expr2 = mklet_nodecl ~var ~init:(mkbinary ~expr1:di ~op:`Bdiv ~expr2:d ()) ~body () in
                  mkand ~expr1 ~expr2 (), sdi)
        in
        let whole_type, part_type = map_pair integral_type (whole_name, part_name) in
        [let params = (whole_type, snd (last svars)) :: endian_map (fun (v, _) -> part_type, v) svars in
         PDecl.mklogic_def
           ~name
           ~params
           ~body:(conjunct_bw_pred name params body)
           ()]
    in
    let unsigned_merge_pred () =
      let whole_name, part_name = map_pair add_u (whole_name, part_name) in
      let name = part_name ^ "_as_" ^ whole_name in
      guard_declarations ~name @@ fun () ->
        let svars = List.map ((^) "a" % string_of_int) @@ List.range (v - 1) `Downto 0 in
        let vars = List.map (fst % var) svars in
        let d0 = "d0" in
        let body =
          let n =
            ListLabels.(fold_left (tl vars)
              ~init:(hd vars)
              ~f:(fun body expr2 ->
                    let expr1 = mkbinary ~expr1:body ~op:`Bmul ~expr2:d () in
                    mkbinary ~expr1 ~op:`Badd ~expr2 ()))
          in
          mkeq (fst @@ var d0) n
        in
        let whole_type, part_type = map_pair integral_type (whole_name, part_name) in
        [let params = (whole_type, d0) :: endian_map (fun v -> part_type, v) svars in
         PDecl.mklogic_def
           ~name
           ~params
           ~body:(conjunct_bw_pred name params body)
           ()]
    in
    let complement what =
      let t, max = match what with `Whole -> add_u whole_name, w | `Part -> add_u part_name, d in
      let name = "complement_to_" ^ t in
      guard_declarations ~name @@ fun () ->
        let typ = integral_type t in
        let sv = "v" in
        let v = fst @@ var sv in
        [PDecl.mklogic_def
           ~typ
           ~name
           ~params:[integral_type @@ del_u t, sv]
           ~body:(
              mkif
                ~condition:(mkbinary ~expr1:v ~op:`Bge ~expr2:zero_expr ())
                ~expr_then:(mkcast ~expr:v ~typ ())
                ~expr_else:(mkcast ~expr:(mkbinary ~expr1:(mkcast ~expr:v ~typ:tinteger ()) ~op:`Badd ~expr2:max ())
                                   ~typ ())
                ())
           ()]
    in
    let signed_pred what =
      let whole_name, part_name = del_u whole_name, add_u part_name in
      let from, _to, unsigned_pred =
        match what with
        | `Split -> whole_name, part_name, unsigned_split_pred
        | `Merge -> part_name, whole_name, unsigned_merge_pred
      in
      let name = from ^ "_as_" ^ _to in
      guard_declarations ~name @@ fun () ->
        let fun_name, unsigned_pred_defs = unsigned_pred () in
        let complement_name, complement_def = complement `Whole in
        let svars = List.map ((^) "a" % string_of_int) @@ List.range (v - 1) `Downto 0 in
        let d0 = "d0" in
        let body =
          let whole = mkapp ~fun_name:complement_name ~args:[fst @@ var d0] () in
          mkapp ~fun_name ~args:(whole :: List.map (fst % var) svars) ()
        in
        let whole_type, part_type = map_pair integral_type (whole_name, part_name) in
        unsigned_pred_defs @
        complement_def @
        [let params = (whole_type, d0) :: List.map (fun v -> part_type, v) svars in
         PDecl.mklogic_def
           ~name
           ~params
           ~body:(conjunct_bw_pred name params body)
           ()]
    in
    let preds =
      let is_u s = s.[0] = 'u' in
      let (split_name, split_defs), (merge_name, merge_defs) =
        if is_u whole_name then unsigned_split_pred (), unsigned_merge_pred ()
                           else signed_pred `Split, signed_pred `Merge
      in
      merge_defs @ split_defs @
      if is_u part_name then []
      else
        let complement_name, complement_def = complement `Part in
        let d0 = "d0" in
        let svars = List.map ((^) "a" % string_of_int) @@ List.range (v - 1) `Downto 0 in
        let args =
          fst (var d0) ::
          List.map (fun sv -> mkapp ~fun_name:complement_name ~args:[fst @@ var sv] ()) svars
        in
        let bodies = List.map (fun fun_name -> mkapp ~fun_name ~args ()) [merge_name; split_name] in
        let names = [part_name ^ "_as_" ^ whole_name; whole_name ^ "_as_" ^ part_name] in
        let whole_type, part_type = map_pair integral_type (whole_name, part_name) in
        complement_def @
        List.map2
          (fun name body ->
             let params = (whole_type, d0) :: List.map (fun v -> part_type, v) svars in
             PDecl.mklogic_def
               ~name
               ~params
               ~body:(conjunct_bw_pred name params body)
               ())
          names bodies
    in
    preds
  in
  let pairwise lst =
    let rec loop r = function
      | _ :: (_ :: xs as xxs), [] -> loop r (xxs, xs)
      | _, [] -> r
      | x :: _ as xxs, y :: ys -> loop ((x, y) :: r) (xxs, ys)
      | _ -> raise (Invalid_argument "pairwise")
    in
    loop [] (lst, try List.tl lst with Failure _ -> [])
  in
  let pairs =
    let rec handle_type name (ty, bitsize) acc =
      let is_void_subtype =
        let ci_opt = get_compinfo ty in
        has_some ci_opt &&
        match Retype.parent_type @@ TComp (the ci_opt, empty_size_cache (), []) with
        | Some parentty -> Type.Composite.(compinfo_cname @@ of_typ_exn parentty) = wrapper_name voidType
        | None -> false
      in
      let acc =
        match is_void_subtype, bitsize with
        | true, Some b when b mod 8 = 0 -> (name, ty, the bitsize) :: acc
        | _ -> acc
      in
      let { sizeof_short; sizeof_int; sizeof_long } = theMachine.theMachine in
      match (ty : Type.Integral.t :> typ) with
      | TInt (IInt | IUInt as ikind, attrs) when sizeof_int = sizeof_short ->
        handle_type
          name
          (Type.Integral.int ~attrs (if isSigned ikind then IShort else IUShort), bitsize)
          acc
      | TInt (IInt | IUInt as ikind, attrs) when sizeof_int = sizeof_long ->
        handle_type
          name
          (Type.Integral.int ~attrs (if isSigned ikind then ILong else IULong), bitsize)
          acc
      | _ -> acc
    in
    pairwise @@ Type.Integral.fold_all handle_type []
  in
  let decls = List.(flatten @@ map memory_reinterpretation_predicates pairs) in
  if pairs <> [] then
    [PDecl.mkaxiomatic ~name:"Jessie_memory_reinterpretation_predicates" ~decls ()]
  else
    []

let file f =
  let filter_defined = function GFun _ | GVar _ -> true | _ -> false in
  let defined_var =
    function GFun(f,_) -> f.svar | GVar(vi,_,_) -> vi | _ -> assert false
  in
  let is_needed =
    function
      | GFunDecl(_,v,_) when Cil.hasAttribute "FC_BUILTIN" v.vattr ->
          v.vreferenced
      | _ -> true
  in
  let globals =
    List.filter is_needed f.globals
  in
  let vardefs =
    List.rev (List.rev_map defined_var (List.filter filter_defined globals))
  in
  (* Compute translation of [globals] before [integral_types] so that types
     used are known *)
  let globals' =
    List.flatten (List.rev (List.rev_map (global vardefs) globals))
  in
  let get_compinfo = get_compinfo globals in
  mkdecl (JCDaxiomatic("Padding",
                       [mkdecl (JCDlogic_type (Name.Logic_type.padding, []))
                          Why_loc.dummy_position]))
    Why_loc.dummy_position
  ::
  (* This predicate generator has a side effect, i.e. it can add new (unsigned) integral types as used. *)
  (* So we call it before translating the integral types. *)
  let reinterpretation_predicates =
    if has_some (get_compinfo voidType)
    then memory_reinterpretation_predicates (get_compinfo : typ -> _ :> 'a Type.t -> _) ()
    else []
  in
  (* Define all integral types as enumerated types in Jessie *)
  integral_types ()
  (* Define conversion functions and identity axiom for back
     and forth conversion *)
  @ type_conversions ()
  @ reinterpretation_predicates
  @ globals'

(* Translate pragmas separately as their is no declaration for pragmas in
 * the parsed AST of Jessie, only in its types AST.
 *)
let pragma =
  function
  | GPragma (Attr (name, [AStr arg]), _)
  | GPragma (Attr (name, [ACons (arg, [])]), _) ->
    begin match name with
    | "JessieFloatModel" ->
      begin match String.lowercase_ascii arg with
      | "math" -> float_model := `Math;
        [Jc.Print.JCfloat_model Jc.Env.FMmath]
      | "defensive" ->
        float_model := `Defensive;
        [Jc.Print.JCfloat_model Jc.Env.FMdefensive]
      | "full" ->
        float_model := `Full;
        [Jc.Print.JCfloat_model Jc.Env.FMfull]
      | "multirounding" ->
        float_model := `Multirounding;
        [Jc.Print.JCfloat_model Jc.Env.FMmultirounding]
      | s ->
        Console.warning
          "pragma %s: identifier %s is not a valid value (ignored)."
          name s; []
      end;
    | "JessieFloatRoundingMode" ->
      begin match String.lowercase_ascii arg with
      | "nearesteven" ->
        (* float_rounding_mode := `NearestEven; *)
        [Jc.Print.JCfloat_rounding_mode Jc.Env.FRMNearestEven]
      | "down" ->
        (* float_rounding_mode := `Downward; *)
        [Jc.Print.JCfloat_rounding_mode Jc.Env.FRMDown]
      | "up" ->
        (* float_rounding_mode := `Upward; *)
        [Jc.Print.JCfloat_rounding_mode Jc.Env.FRMUp]
      | "tozero" ->
        (* float_rounding_mode := `Towardzero; *)
        [Jc.Print.JCfloat_rounding_mode Jc.Env.FRMToZero]
      | "nearestaway" ->
        (* float_rounding_mode := `Towardawayzero; *)
        [Jc.Print.JCfloat_rounding_mode Jc.Env.FRMNearestAway]
      | s ->
        Console.warning
          "pragma %s: identifier %s is not a valid value (ignored)" name s; []
      end
    | "JessieFloatInstructionSet" ->
      begin match String.lowercase_ascii arg with
      | "x87" ->
        [Jc.Print.JCfloat_instruction_set "x87"]
      | "ieee754" ->
        [Jc.Print.JCfloat_instruction_set "ieee754"]
      | s ->
        Console.warning
          "pragma %s: identifier %s is not a valid value (ignored)" name s; []
      end
    | _ ->
      Console.warning
        "pragma %s is ignored by Jessie." name;
      []
    end
  | GPragma (Attr ("JessieBuiltin", [ACons (acsl, []); AStr jessie]), _) ->
    Hashtbl.add jessie_builtins acsl jessie;
    []
  | GPragma _ -> []
  | _ -> []

let pragmas f = List.(flatten @@ map pragma f.globals)

(*
Local Variables:
compile-command: "make"
End:
*)
