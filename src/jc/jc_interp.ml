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
(*  Jessie2 fork:                                                         *)
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
open Effect
open Fenv

open Name
open Constructors
open Common
open Separation
open Struct_tools
open Interp_misc
(*open Invariants
  open Pattern*)

open Output_ast

open Format
open Num
open Why_pp

module O = Output

let unsupported = Typing.typing_error

(******************************************************************************)
(*                            source positioning                              *)
(******************************************************************************)

let lookup_pos e =
  let open Stdlib in
  try
    let f, l, b, e, _, _ = Hashtbl.find Options.pos_table e#mark in
    Position.of_loc (f, l, b, e)
  with
  | Not_found -> Position.of_pos e#pos

module T =
struct
  let locate ~t = O.T.positioned (lookup_pos t)
end

module P =
struct
  let locate ~p = O.P.positioned (lookup_pos p)
end

module E =
struct
  let locate ~e = O.E.positioned (lookup_pos e)
end

(******************************************************************************)
(*                                 Operators                                  *)
(******************************************************************************)

type unary = Unary : ('a * unit, 'a) func * 'a ty -> unary

let un_op ~e : expr_unary_op -> _ =
  let return f t = Unary (f, Numeric t) in
  function
  | `Uminus, `Integer ->
    return (U_int_op `Neg) (Integral Integer)
  | `Ubw_not, `Enum { ei_type = Int (r, b); _ } ->
    let i : _ integer = Int (r, b) in
    return (U_bint_bop (`Compl, i)) (Integral i)
  | `Uminus, `Enum { ei_type = Int (r, b); _ } ->
    let i : _ integer = Int (r, b) in
    return (U_bint_op (`Neg, i, false)) (Integral i)
  | `Uminus, `Enum { ei_type = Enum e; _ } ->
    let i = Enum e in
    return (U_bint_op (`Neg, i, false)) (Integral i)
  | `Uminus_mod, `Enum { ei_type = Int (r, b); _ } ->
    let i : _ integer = Int (r, b) in
    return (U_bint_op (`Neg, i, true)) (Integral i)
  | `Uminus_mod, `Enum { ei_type = Enum e; _ } ->
    let i = Enum e in
    return (U_bint_op (`Neg, i, true)) (Integral i)
  | `Unot, `Boolean ->
    Unary (O.F.bool "notb", Bool)
  | `Uminus, `Float ->
    return (O.F.single "(-_)") (Real (Float Single))
  | `Uminus, `Double ->
    return (O.F.double "(-_)") (Real (Float Double))
  | `Uminus, `Real ->
    return (O.F.real "(-_)") (Real Real)
  | op, op_ty ->
    unsupported
      ~loc:e#pos
      "unary_op: no unary operation `%s' for type `%s'"
      (string_of_op op)
      (string_of_op_type op_ty)

let float_model_has_safe_functions () =
  match !Options.float_model with
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

type ('a, 'b, 'ax, 'bx) form =
  | Term : ('a, 'b, 'a term, 'b term) form
  | Expr : ('a, 'b, 'a expr, 'b expr) form

let current_rounding_mode : type a ax. (a, a, ax, ax) form -> ax =
  fun form ->
  let var v : ax =
    match form with
    | Term -> O.T.var v
    | Expr -> O.E.var v
  in
  match !Options.current_rounding_mode with
  | FRMNearestEven -> var "nearest_even"
  | FRMDown -> var "down"
  | FRMUp -> var "up"
  | FRMToZero -> var "to_zero"
  | FRMNearestAway -> var "nearest_away"

type binary =
  | Op : ('a * ('a * unit), 'a) func * ('a, 'b) ty_opt -> binary
  | Rel : ('a * ('a * unit), boolean) func * ('a, 'b) ty_opt -> binary

let bin_op ~e : [< bin_op] * operator_type -> _ =
  let op f t = Op (f, Ty (Numeric t)) in
  let rel f t = Rel (f, Ty (Numeric t)) in
  let r =
    function
    | `Bgt -> `Gt
    | `Blt -> `Lt
    | `Bge -> `Ge
    | `Ble -> `Le
    | `Beq -> `Eq
    | `Bneq -> `Ne
  in
  let o =
    function
    | `Badd -> `Add
    | `Bsub -> `Sub
    | `Bmul -> `Mul
    | `Bdiv -> `Div
    | `Bmod -> `Mod
    | `Badd_mod -> `Add
    | `Bsub_mod -> `Sub
    | `Bdiv_mod -> `Div
  in
  function
  (* integers *)
  | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq |
    `Badd | `Bsub | `Bmul | `Bdiv | `Bmod as op',
    `Integer ->
    let int = Integral Integer in
    let rel r = rel (B_num_pred (r, int)) int in
    let op o = op (B_int_op o) int in
    begin match op' with
    | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq as op' -> rel (r op')
    | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod as op' -> op (o op')
    end
  (* ints *)
  | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq |
    `Badd | `Bsub | `Bmul | `Bdiv | `Bmod |
    `Badd_mod | `Bsub_mod | `Bdiv_mod |
    `Bbw_and | `Bbw_or | `Bbw_xor |
    `Bshift_left | `Bshift_left_mod | `Blogical_shift_right | `Barith_shift_right as op',
    `Enum { ei_type = Int (repr, b) } ->
    let t : _ integer = Int (repr, b) in
    let it = Integral t in
    let rel, bop, mop, bwop =
      (fun r -> rel (B_num_pred (r, it)) it),
      (fun o -> op (B_bint_op (o, t, false)) it),
      (fun o -> op (B_bint_op (o, t, true)) it),
      fun o -> op (B_bint_bop (o, t)) it
    in
    begin match op' with
    | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq as op' -> rel (r op')
    | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod as op' -> bop (o op')
    | `Badd_mod | `Bsub_mod | `Bdiv_mod as op' -> mop (o op')
    | `Bbw_and -> bwop `And
    | `Bbw_or -> bwop `Or
    | `Bbw_xor -> bwop `Xor
    | `Blogical_shift_right -> bwop `Lsr
    | `Barith_shift_right -> bwop `Asr
    | `Bshift_left -> op (Lsl_bint (t, false)) it
    | `Bshift_left_mod -> op (Lsl_bint (t, true)) it
    end
  (* enums *)
  | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq |
    `Badd | `Bsub | `Bmul | `Bdiv | `Bmod |
    `Badd_mod | `Bsub_mod | `Bdiv_mod as op',
    `Enum { ei_type = Enum e } ->
    let t : _ integer = Enum e in
    let it = Integral t in
    let rel, op, mop =
      (fun r -> rel (B_num_pred (r, it)) it),
      (fun o -> op (B_bint_op (o, t, false)) it),
      fun o -> op (B_bint_op (o, t, true)) it
    in
    begin match op' with
    | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq as op' -> rel (r op')
    | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod as op' -> op (o op')
    | `Badd_mod | `Bsub_mod | `Bdiv_mod as op' -> mop (o op')
    end
  (* pointers *)
  | `Beq | `Bneq | `Bsub as op', `Pointer ->
    begin match op' with
    | `Beq -> Rel (Poly `Eq, Any)
    | `Bneq -> Rel (Poly `Eq, Any)
    | `Bsub -> Op (O.F.jc "sub_pointer", Any)
    end
  (* reals *)
  | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq |
    `Badd | `Bsub | `Bmul | `Bdiv | `Bmod as op',
    (`Real | `Double | `Float as t) ->
    let rel, op =
      let return t f =
        (fun r -> rel (B_num_pred (r, t)) t), fun o -> op (f o) t
      in
      match t with
      | `Real ->
        return (Real Real) O.F.real
      | `Double ->
        return (Real (Float Single)) O.F.real
      | `Float ->
        return (Real (Float Double)) O.F.real
    in
    begin match op' with
    | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq as op' -> rel (r op')
    | `Badd -> op "(+)"
    | `Bsub -> op "(-)"
    | `Bmul -> op "(*)"
    | `Bdiv -> op "(/)"
    | `Bmod -> op "(%)"
    end
  (* bool *)
  | `Beq | `Bneq | `Blor | `Bland | `Biff | `Bimplies as op', `Boolean ->
    let op o = Op (O.F.bool o, Ty Bool) in
    begin match op' with
    | `Beq -> Rel (Poly `Eq, Ty Bool)
    | `Bneq -> Rel (Poly `Neq, Ty Bool)
    | `Blor -> op "orb"
    | `Bland -> op "andb"
    | `Biff -> op "iffb"
    | `Bimplies -> op "implb"
    end
  | `Bconcat, _ -> Op (O.F.jc "string_concat", Any)
  | `Beq, `Logic -> Rel (Poly `Eq, Any)
  | `Bneq, `Logic -> Rel (Poly `Neq, Any)
  | `Beq, `Unit -> Rel (Poly `Eq, Ty Void)
  | `Bneq, `Unit -> Rel (Poly `Neq, Ty Void)
  | #bin_op as op, op_ty ->
    unsupported
      ~loc:e#pos
      "bin_op: no binary operation `%s' for type `%s'"
      (string_of_op op)
      (string_of_op_type op_ty)

(******************************************************************************)
(*                                 Coercions                                  *)
(******************************************************************************)

let float_of_real (type a) (f : a precision) x =
  (* TODO: Mpfr.settofr etc *)
  if Str.string_match (Str.regexp "\\([0-9]+\\)\\.0*$") x 0 then
    let s = Str.matched_group 1 x in
    match f with
    | Single ->
      if String.length s <= 7 (* x < 10^7 < 2^24 *) then x
      else raise Not_found
    | Double ->
       if String.length s <= 15 (* x < 10^15 < 2^53 *) then x
       else raise Not_found
  else
    match f, x with
    | _ , "0.5" -> x
    | Single, "0.1" -> "0x1.99999ap-4"
    | Double, "0.1" -> "0x1.999999999999ap-4"
    | _ -> raise Not_found

let rec coerce :
  type a b ax bx c d. (b, c) ty_opt -> (a, d) ty_opt -> (a, b, ax, bx) form -> e:_ -> e1:_ -> ax -> bx =
  fun ty_dst ty_src form ->
    let apply : (a * unit, b) func -> ax -> bx =
      fun f e ->
      match form with
      | Term -> O.T.(f $. e)
      | Expr -> O.E.(f $. e)
    in
    let return (e : ax) : bx =
      match form, ty_dst, ty_src with
      | Term, Any, Any -> O.T.return Any e
      | Expr, Any, Any -> O.E.return Any e
      | Term, Ty t1, Ty t2 ->
        let O.Ty.Eq = O.Ty.eq t1 t2 in e
      | Expr, Ty t1, Ty t2 ->
        let O.Ty.Eq = O.Ty.eq t1 t2 in e
      | _ -> assert false
    in
    let rec same a b =
      match a, b with
      | JCTlogic (t, tl), JCTlogic (u, ul) when t = u -> List.for_all2 same tl ul
      | JCTtype_var _, JCTtype_var _ -> true (*jc_typing takes care of that*)
      | JCTtype_var _, _ | _, JCTtype_var _ -> true
      | JCTpointer (JCroot rt1, _, _), JCTpointer (JCroot rt2, _, _) -> rt1 == rt2
      | _ -> false
    in
    fun ~e ~e1 e' ->
      let apply' f = apply f e' in
      let return = return e' in
      match ty_src, ty_dst with
      | Any, Any when
        (match e#typ, e1#typ with
        (* identity *)
        | JCTnative t, JCTnative u when t = u -> true
        | (JCTlogic _ | JCTtype_var _ as t1), (JCTlogic _ | JCTtype_var _ as t2) when same t1 t2 -> true
        | JCTtype_var _, JCTpointer _ -> true
        | JCTpointer _, JCTnull -> true
        | JCTpointer _ as t1, (JCTpointer _ as t2) when same t1 t2 -> true
        | JCTpointer (pc1, _, _), JCTpointer (JCtag (st2, _), _, _) when Typing.substruct st2 pc1 -> true
        | JCTany, JCTany -> true
        | _ -> false) -> return
      (* between integer/enum and real *)
      | Ty (Numeric (Integral Integer)), Ty (Numeric (Real Real)) ->
        begin match form, e' with
        | Term, Const (Int n) ->
          O.T.(real P.(n ^ ".0"))
        | Expr, { expr_node = Const (Int n) } ->
          O.E.(real P.(n ^ ".0"))
        | _ -> apply' @@ O.F.real "from_int"
        end
      | Ty (Numeric (Real (Float _ as f))), Ty (Numeric (Real Real)) ->
        begin match form, e' with
        | Term, App (User (_, _, "of_real_exact"), Cons (Const (Real _) as c, Nil)) -> c
        | Expr, { expr_node = App (User (_, _, "of_real_exact"), Cons ({ expr_node = Const (Real _) } as c, Nil), _) }
          -> c
        | _ -> apply' @@ Of_float f
        end
      | Ty (Numeric (Real Real)), Ty (Numeric (Real (Float f))) ->
        begin try
          match form, e' with
          | Term, Const (Real n) ->
            apply ((match f with Single -> O.F.single | Double -> O.F.double) "of_real_exact")
              (Const (Real (float_of_real f n)))
          | _ -> raise Not_found
        with
        | Not_found -> apply' @@ To_float (Float f)
        end
      (* between enums and integer *)
      | Ty (Numeric (Integral (Enum (module E1)))), Ty (Numeric (Integral (Enum (module E2))))
        when (match E1.E with E2.E -> true | _ -> false) ->
        begin match E1.E with E2.E -> return | _ -> assert false end
      | Ty (Numeric (Integral Integer)), Ty (Numeric (Integral (Int _ as i))) ->
        apply' @@ Of_int (i, false)
      | Ty (Numeric (Integral (Int _ as i))), Ty (Numeric (Integral Integer))  ->
        apply' @@ To_int i
      | Ty t1, Ty t2 ->
        begin try
          match O.Ty.eq t1 t2 with O.Ty.Eq -> return
        with
        | Failure _ ->
          unsupported
            ~loc:e#pos
            "can't coerce type %s to type %s"
            (O.Ty.to_string t1) (O.Ty.to_string t2)
        end
      | _, Any -> return
      | Any, Ty t ->
        unsupported
          ~loc:e#pos
          "can't coerce type %a to type %s"
          print_type e1#typ (O.Ty.to_string t)

(******************************************************************************)
(*                                   terms                                    *)
(******************************************************************************)

let rec term :
  type a b. (a, b) ty_opt -> ?subst:_ -> type_safe:_ -> global_assertion:_ -> relocate:_ -> _ -> _ -> _ -> a term =
  fun typ ?(subst=VarMap.empty) ~type_safe ~global_assertion ~relocate lab oldlab t ->
  let ft typ = term typ ~subst ~type_safe ~global_assertion ~relocate lab oldlab in
  let un_op = un_op ~e:t in
  let bin_op = bin_op ~e:t in
  let coerce = coerce ~e:t in
  let return t = O.T.return typ t in
  let t' =
    match t#node with
    | JCTconst JCCnull -> O.T.(check typ (var "null"))
    | JCTvar v ->
      begin try
        let (Term t : some_term) = VarMap.find v subst in
        return t
      with
      | Not_found ->
        return (tvar ~label_in_name:global_assertion lab v)
      end
    | JCTconst c -> Const (const typ c)
    | JCTunary (op, t1) ->
      let Unary (f, ty') = un_op op in
      return O.T.(f $. ft (Ty ty') t1)
    | JCTbinary (t1, op, t2) ->
      begin match bin_op op with
      | Op (f, ty_opt) -> return O.T.(f $ ft ty_opt t1 ^. ft ty_opt t2)
      | Rel (f, ty_opt) -> return O.T.(f $ ft ty_opt t1 ^. ft ty_opt t2)
      end
    | JCTshift (t1, t2) ->
      return O.T.(O.F.jc "shift" $ ft Any t1 ^. ft (Ty O.Ty.integer) t2)
    | JCTif (t1, t2, t3) ->
      return @@
        O.T.if_
          (ft (Ty Bool) t1)
          (ft typ t2)
          (ft typ t3)
    | JCTlet (vi, t1, t2) ->
      let Typ typ' = ty t1#typ in
      return @@ O.T.let_ vi.vi_final_name (ft typ' t1) (fun _ -> ft typ t2)
    | JCToffset (k, t1, st) ->
      let ac = tderef_alloc_class ~type_safe t1 in
      let _, alloc = talloc_table_var ~label_in_name:global_assertion lab (ac, t1#region) in
      begin match ac with
      | JCalloc_root _ ->
        let f =
          match k with
          | Offset_min -> "offset_min"
          | Offset_max -> "offset_max"
        in
        return @@ O.T.(F.jc f $ alloc ^. ft Any t1)
      | JCalloc_bitvector ->
        let f =
          match k with
          | Offset_min -> "offset_min_bytes"
          | Offset_max -> "offset_max_bytes"
        in
        let s = string_of_int (struct_size_in_bytes st) in
        return @@ O.T.(F.jc f $ alloc ^ ft Any t1 ^. Const (Int s))
      end
    | JCTaddress (Addr_absolute, t1) ->
      return @@ O.T.(F.jc "absolute_address" $. ft Any t1)
    | JCTaddress (Addr_pointer, t1) ->
      return @@ O.T.(O.F.jc "address" $. ft Any t1)
    | JCTbase_block t1 ->
      let t1' = ft Any t1 in
      let _, alloc =
        let ac = tderef_alloc_class ~type_safe t1 in
        talloc_table_var ~label_in_name:global_assertion lab (ac, t1#region)
      in
      return @@ O.T.(F.jc "shift" $ t1' ^. (F.jc "offset_min" $ alloc ^. t1'))
    | JCTinstanceof (t1, lab', st) ->
      let lab = if relocate && lab' = LabelHere then lab else lab' in
      let _, tag = ttag_table_var ~label_in_name:global_assertion lab (struct_root st, t1#region) in
      O.T.(O.F.jc "instanceof" $ tag ^ ft Any t1 ^. var (Name.tag st))
    | JCTcast (t1, lab', st) ->
      if struct_of_union st
      then ft Any t1
      else
        let lab = if relocate && lab' = LabelHere then lab else lab' in
        let _, tag = ttag_table_var ~label_in_name:global_assertion lab (struct_root st, t1#region) in
        O.T.(F.jc "downcast" $ tag ^ ft Any t1 ^. var (Name.tag st))
    | JCTrange_cast (t1, ei_opt) ->
      let Typ typ, Typ typ' =
        let to_type = Option.map_default ~f:(fun e -> JCTenum e) ~default:(JCTnative Tinteger) ei_opt in
        ty t1#typ, ty to_type
      in
      return @@ coerce typ' typ Term ~e1:t1 @@ ft typ t1
    | JCTrange_cast_mod (t1, ei) ->
      let t1 = ft (Ty (Numeric (Integral Integer))) t1 in
      let return i = return O.T.(Of_int (i, true) $. t1) in
      begin match ei.ei_type with
        | Enum e -> return (Enum e)
        | Int (r, b) -> return (Int (r, b))
      end
    | JCTreal_cast (t1, _rc) ->
      let Typ typ' = ty t1#typ in
      let t1' = ft typ' t1 in
      coerce typ typ' Term ~e1:t1 t1'
    | JCTderef (t1, lab', fi) ->
      let lab = if relocate && lab' = LabelHere then lab else lab' in
      let mc, _ufi_opt = tderef_mem_class ~type_safe t1 fi in
      begin match mc with
      | JCmem_field fi' ->
        assert (fi.fi_tag = fi'.fi_tag);
        let mem = tmemory_var ~label_in_name:global_assertion lab (JCmem_field fi, t1#region) in
        return O.T.(O.F.jc "select" $ mem ^. ft Any t1)
      | JCmem_plain_union vi ->
        let t1, off = tdestruct_union_access t1 (Some fi) in
        (* Retrieve bitvector *)
        let t1' = ft Any t1 in
        let mem = tmemory_var ~label_in_name:global_assertion lab (JCmem_plain_union vi, t1#region) in
        let e' = O.T.(O.F.jc "select" $ mem ^. t1') in
        (* Retrieve subpart of bitvector for specific subfield *)
        let off =
          match off with
          | Int_offset s -> s
          | _ -> failwith "term: unsupported bitvector offset" (* TODO *)
        in
        let size =
          match fi.fi_bitsize with
          | Some x -> x / 8
          | None -> failwith "term: field without bitsize in bv region"
        in
        let off = string_of_int off and size = string_of_int size in
        let _e' =
          O.T.(F.jc "extract_bytes" $ e' ^ Const (Int off) ^. Const (Int size))
        in
        (* Convert bitvector into appropriate type *)
        begin match fi.fi_type with
        | JCTenum _
        | JCTnative Tinteger
        | JCTnative _
        | JCTtype_var _
        | JCTpointer (_, _, _)
        | JCTlogic _
        | JCTany
        | JCTnull -> Options.jc_error t#pos "Unsupported bv type conversion"
        end
      | JCmem_bitvector ->
        (* Retrieve bitvector *)
        let t1' = ft Any t1 in
        let mem = tmemory_var ~label_in_name:global_assertion lab (JCmem_bitvector, t1#region) in
        let off =
          match field_offset_in_bytes fi with
          | Some x -> x
          | None -> failwith "term: field without bitsize in bv region"
        in
        let size =
          match fi.fi_bitsize with
          | Some x -> x / 8
          | None -> failwith "term: field without bitsize in bv region"
        in
        let off = string_of_int off and size = string_of_int size in
        let _e' = O.T.(F.jc "select_bytes" $ mem ^ t1' ^ Const (Int off) ^. Const (Int size)) in
        (* Convert bitvector into appropriate type *)
        begin match fi.fi_type with
        | JCTenum _
        | _ -> Options.jc_error t#pos "Unsupported bv type conversion" (* TODO *)
        end
      end
    | JCTapp app ->
      let f = app.app_fun in
      let args =
        List.fold_right2
          (fun vi arg acc -> let Typ typ = ty vi.vi_type in (Term (ft typ arg) : some_term) :: acc)
          f.li_parameters
          app.app_args
          []
      in
      let relab (lab1, lab2) = (lab1, if lab2 = LabelHere then lab else lab2) in
      let label_assoc =
        if relocate
        then (LabelHere, lab) :: List.map relab app.app_label_assoc
        else app.app_label_assoc
      in
      logic_fun_call
        ~label_in_name:global_assertion
        ~region_assoc:app.app_region_assoc
        ~label_assoc
        f args
    | JCTold t1 ->
      let lab = if relocate && oldlab = LabelHere then lab else oldlab in
      term typ ~type_safe ~global_assertion ~relocate lab oldlab t1
    | JCTat (t1, lab') ->
      let lab = if relocate && lab' = LabelHere then lab else lab' in
      term typ ~type_safe ~global_assertion ~relocate lab oldlab t1
    | JCTrange (_t1,_t2) ->
      unsupported ~loc:t#pos "Unsupported range in term, sorry" (* TODO ? *)
    | JCTmatch (t, _ptl) ->
      let Typ typ' = ty t#typ in
      let _t' = ft typ' t in
      (* TODO: use a temporary variable for t' *)
      (* if the pattern-matching is incomplete, default value is true *)
      (*let ptl', lets = pattern_list_term ft t' t#typ ptl @@ LConst (Prim_bool true) in
      concat_pattern_lets lets;
        ptl'*)
      assert false
  in
  if t#mark <> ""
  then T.locate t t'
  else t'
and some_term ?subst ~type_safe ~global_assertion ~relocate lab oldlab t =
  let Typ typ = ty t#typ in
  O.T.some @@ term typ ?subst ~type_safe ~global_assertion ~relocate lab oldlab t

let () = Interp_misc.term.term <- term

let named_term typ ~type_safe ~global_assertion ~relocate lab oldlab t =
  let t' = term typ ~type_safe ~global_assertion ~relocate lab oldlab t in
  match t' with
  | (Labeled _ : _ term) -> t'
  | _ -> T.locate t t'


(******************************************************************************)
(*                                assertions                                  *)
(******************************************************************************)

(*
(* [pattern_lets] is a list of (id, value), which should be binded
 * at the assertion level. *)
let pattern_lets = ref []
let concat_pattern_lets lets = pattern_lets := lets @ !pattern_lets
let bind_pattern_lets body =
  let binds =
    List.fold_left
      (fun body bind ->
         match bind with
         | `Forall (id, Logic_type ty) -> O.forall id ty (fun _ -> body)
         | `Let (id, (Term value : some_term)) -> O.let_ id ~equal:value ~in_:(fun _ -> body))
      body
      (List.rev !pattern_lets)
  in
  pattern_lets := [];
  binds
*)

let is_base_block t =
  match t#node with
  | JCTbase_block _ -> true
  | _ -> false

let tag ~type_safe ~global_assertion ~relocate lab oldlab tag =
  match tag#node with
  | JCTtag st -> O.T.(var (Name.tag st))
  | JCTbottom -> O.T.(var "bottom_tag")
  | JCTtypeof (t, st) ->
    let t' = term Any ~type_safe ~global_assertion ~relocate lab oldlab t in
    let _, tag = ttag_table_var ~label_in_name:global_assertion lab (struct_root st, t#region) in
    O.T.(F.jc "typeof" $ tag ^. t')

let rec predicate ~type_safe ~global_assertion ~relocate lab oldlab p =
  let f f = f ~type_safe ~global_assertion ~relocate lab oldlab in
  let fp = f predicate
  and ft t = f (term t ?subst:None)
  and ftag = f tag
  in
  let bin_op = bin_op ~e:p in
  let triggers trigs =
    let pat =
      function
      | JCAPatT t -> let Typ typ = ty t#typ in (Term (ft typ t) : trigger)
      | JCAPatP p -> Pred (fp p)
    in
    List.map (List.map pat) trigs
  in
  let p' =
    match p#node with
    | JCAtrue -> True
    | JCAfalse -> False
    | JCAif (t1, pt, pe) ->
      O.P.if_
        (ft (Ty Bool) t1)
        (fp pt)
        (fp pe)
    | JCAand ps -> O.P.conj (List.map fp ps)
    | JCAor ps -> O.P.disj (List.map fp ps)
    | JCAimplies (p1, p2) -> O.P.impl (fp p1) (fp p2)
    | JCAiff (p1, p2) -> O.P.iff (fp p1) (fp p2)
    | JCAnot p1 -> O.P.not (fp p1)
    | JCArelation (t1, ((`Beq | `Bneq as op), _), t2)
      when is_base_block t1 && is_base_block t2 ->
      let base_block t = match t#node with JCTbase_block t -> t | _ -> assert false in
      let t1, t2 = Pair.map base_block (t1, t2) in
      let p = O.P.(F.jc "same_block" $ ft Any t1 ^. ft Any t2) in
      begin match op with
      | `Beq -> p
      | `Bneq -> O.P.not p
      end
    | JCArelation (t1, op, t2) ->
      begin match bin_op op with
      | Rel (f, typ) -> O.P.(f $ ft typ t1 ^. ft typ t2)
      | Op (f, typ) -> O.P.(F.check (Ty Bool) f $ ft typ t2 ^. ft typ t2)
      end
    | JCAapp app ->
      let f = app.app_fun in
      let args =
        List.fold_right2
          (fun v arg ->
             let Typ typ = ty v.vi_type in
             List.cons (Term (ft typ arg) : some_term))
          f.li_parameters
          app.app_args
          []
      in
      let label_assoc =
        if relocate
        then
          let relab (lab1, lab2) = lab1, if lab2 = LabelHere then lab else lab2 in
          (LabelHere, lab) :: List.map relab app.app_label_assoc
        else
          app.app_label_assoc
      in
      logic_pred_call
        ~label_in_name:global_assertion
        ~region_assoc:app.app_region_assoc
        ~label_assoc
        f args
      |>
      Fn.on
        (IntHashtblIter.mem Typing.global_invariants_table app.app_fun.li_tag) @@
        P.locate ~p ?behavior:None ~kind:(JCVCglobal_invariant app.app_fun.li_name)
    | JCAquantifier (Forall | Exists as q, v, trigs, p1) ->
      let Logic_type lt = some_var_logic_type v in
      (match q with Forall -> O.P.forall | Exists -> O.P.exists)
        v.vi_final_name
        lt
        ~trigs:(fun _ -> triggers trigs)
        (fun _ -> fp p1)
    | JCAold a1 ->
      let lab = if relocate && oldlab = LabelHere then lab else oldlab in
      predicate ~type_safe ~global_assertion ~relocate lab oldlab a1
    | JCAat (a1, lab') ->
      let lab = if relocate && lab' = LabelHere then lab else lab' in
      predicate ~type_safe ~global_assertion ~relocate lab oldlab a1
    | JCAfresh t1 ->
      let ac = tderef_alloc_class ~type_safe t1 in
      let lab = if relocate && oldlab = LabelHere then lab else oldlab in
      let _, alloc = talloc_table_var ~label_in_name:global_assertion lab (ac, t1#region) in
      O.P.(F.jc "allocable" $ alloc ^. ft Any t1)
    | JCAbool_term t1 ->
      App (Poly `Eq, O.T.(ft (Ty Bool) t1 ^. Const (Bool true)))
    | JCAinstanceof (t1, lab', st) ->
      let lab = if relocate && lab' = LabelHere then lab else lab' in
      let _, tag = ttag_table_var ~label_in_name:global_assertion lab (struct_root st, t1#region) in
      O.P.(F.jc "instanceof" $ tag ^ ft Any t1 ^. T.var (Name.tag st))
    | JCAmutable (_te, _st, _ta) -> assert false
      (*let te' = ft te in
      let tag = ftag ta in
      let mutable_field = LVar (mutable_name (JCtag(st, []))) in
        LPred ("eq", [LApp ("select", [mutable_field; te']); tag])*)
    | JCAeqtype (tag1, tag2, _st_opt) ->
      O.P.(Poly `Eq $ ftag tag1 ^. ftag tag2)
    | JCAsubtype (tag1, tag2, _st_opt) ->
      O.P.(F.jc "subtag" $ ftag tag1 ^. ftag tag2)
    | JCAlet (vi, t, p) ->
      let Typ typ = ty t#typ in
      O.P.let_ vi.vi_final_name (ft typ t) (fun _ -> fp p)
    | JCAmatch (_arg, _pal) ->
      assert false
      (*let arg' = ft arg in
      (* TODO: use a temporary variable for arg' *)
      let pal', _ = pattern_list_assertion fa arg' arg#typ pal LTrue in
        pal'*)
  in
  (*let a' = bind_pattern_lets a' in*)
  if p#mark = ""
  then p'
  else P.locate p p'

let rec mark_predicate ?(recursively=true) ~e ?kind p =
  let mark_predicate' =
    function
    | (Labeled ({ l_kind; l_pos } as l, p) : pred) ->
      (Labeled ({ l with
                  l_kind = if l_kind = None then kind else l_kind;
                  l_pos = if Position.is_dummy l_pos then lookup_pos e else l_pos },
                p) : pred)
    | p -> P.locate ~p:e ?kind p
  in
  if not recursively then mark_predicate' p
  else
    let mark_predicate = mark_predicate ~e ?kind in
    match p with
    | (And (p1, p2) : pred) ->
      mark_predicate' (And (mark_predicate p1, mark_predicate p2))
    | Let (v, p1, p2) ->
      Let (v, p1, mark_predicate p2)
    | Labeled (l, (And _ as p)) | Labeled (l, (Let _ as p)) ->
      mark_predicate' (Labeled (l, mark_predicate p))
    | Labeled (_, (Labeled _ as p)) ->
      mark_predicate p
    | _ ->
      mark_predicate' p

let named_predicate ~type_safe ~global_assertion ?kind ?mark_recursively ~relocate lab oldlab a =
  mark_predicate ?recursively:mark_recursively ~e:a ?kind @@
    predicate ~type_safe ~global_assertion ~relocate lab oldlab a


(******************************************************************************)
(*                                  Locations                                 *)
(******************************************************************************)

let rec pset : type a b. (a, b) ty_opt -> type_safe:_ -> global_assertion:_ -> _ -> _ -> a term =
  fun t ~type_safe ~global_assertion before loc ->
  let f f = f ~type_safe ~global_assertion before in
  let fpset loc : some_term =
    let Typ typ = ty loc#typ in
    Term (f (pset typ) loc)
  and ft t : some_term =
    let Typ typ = ty t#typ in
    Term (f (term typ ?subst:None ~relocate:false) before t)
  in
  let f' t name args =
    let open O.T in
    let Hlist args = hlist_of_list args in
    return t (F.jc name $ args)
  in
  let f = f' t and f' f t : some_term = Term (f' Any f t) in
  match loc#node with
  | JCLSderef (locs, lab, fi, _r) ->
    let m = tmemory_var ~label_in_name:global_assertion lab (JCmem_field fi, locs#region) in
    f "pset_deref" [Term m; fpset locs]
  | JCLSvar vi ->
    let m = tvar ~label_in_name:global_assertion before vi in
    f "pset_singleton" [Term m]
  | JCLSrange (ls, None, None) ->
    f "pset_all" [fpset ls]
  | JCLSrange (ls, None, Some b) ->
    f "pset_range_left" [fpset ls; ft b]
  | JCLSrange (ls, Some a, None) ->
    f "pset_range_right" [fpset ls; ft a]
  | JCLSrange (ls, Some a, Some b) ->
    f "pset_range" [fpset ls; ft a; ft b]
  | JCLSrange_term (ls, None, None) ->
    f "pset_all" [f' "pset_singleton" [ft ls]]
  | JCLSrange_term (ls, None, Some b) ->
    f "pset_range_left" [f' "pset_singleton" [ft ls]; ft b]
  | JCLSrange_term (ls, Some a, None) ->
    f "pset_range_right" [f' "pset_singleton" [ft ls]; ft a]
  | JCLSrange_term (ls, Some a, Some b) ->
    f "pset_range" [f' "pset_singleton" [ft ls]; ft a; ft b]
  | JCLSat (locs, _) -> let Term t' = fpset locs in O.T.return t t'

let rec collect_locations ~type_safe ~global_assertion ~in_clause before loc (refs, mems) =
  let ef = Effect.location ~in_clause empty_fun_effect loc in
  match loc#node with
  | JCLderef (e, lab, fi, _fr) ->
    let iloc = pset Any ~type_safe ~global_assertion lab e in
    (* ...?  if field_of_union fi then FVvariant (union_of_field fi) else *)
    let mcr = JCmem_field fi, location_set_region e in
    refs, MemoryMap.add_merge (@) mcr [iloc, ef] mems
  | JCLderef_term (t1, fi) ->
    let Typ typ = ty t1#typ in
    let t1' = term typ ~type_safe ~global_assertion ~relocate:false before before t1 in
    let iloc = O.T.(F.jc "pset_singleton" $. t1') in
    let mcr = JCmem_field fi, t1#region in
    refs, MemoryMap.add_merge (@) mcr [iloc, ef] mems
  | JCLvar vi ->
    let var = vi.vi_final_name in
    StringMap.add var true refs, mems
  | JCLat (loc, _lab) ->
    collect_locations ~type_safe ~global_assertion ~in_clause before loc (refs, mems)

let rec collect_pset_locations t ~type_safe ~global_assertion lab loc =
  let ft lab lab' t : some_term =
    let Typ typ = ty t#typ in
    Term (term typ ~type_safe ~global_assertion ~relocate:false lab lab' t)
  in
  let f f args =
    let open O.T in
    let Hlist args = hlist_of_list args in
    return t O.T.(F.jc f $ args)
  in
  match loc#node with
  | JCLderef (e, lab, fi, _fr) ->
    let m = tmemory_var ~label_in_name:global_assertion lab (JCmem_field fi, e#region) in
    f "pset_deref" [Term m; Term (pset Any ~type_safe ~global_assertion lab e)]
  | JCLderef_term (t1, fi) ->
    let lab = match t1#label with Some l -> l | None -> lab in
    let m = tmemory_var ~label_in_name:global_assertion lab (JCmem_field fi, t1#region) in
    f "pset_deref" [Term m; Term (f "pset_singleton" [ft lab lab t1])]
  | JCLvar ({ vi_type = JCTpointer _ } as vi)  ->
    f "pset_singleton" [Term (tvar ~label_in_name:global_assertion lab vi)]
  | JCLvar vi ->
    Options.jc_warning loc#pos "Non-pointer variable `%s' found as location in pointer-set context, ignoring"
      vi.vi_name;
    O.T.var "pset_empty"
  | JCLat (loc, lab) ->
    collect_pset_locations t ~type_safe ~global_assertion lab loc

let external_region ?region_list (_, r) =
  (* More exact apprixmation (at least fixes both previously encountered bugs): *)
  (* generate not_assigns for parameters and constant (i.e. global) memories (tables). *)
  (* Also generate not_assigns always when in SepNone sparation mode. *)
  !Options.separation_sem = SepNone || (* no regions used at all *)
  (* constant memory, alloc- or tag table, not passed as argument, but counted as effect (global) *)
  not (Region.polymorphic r) ||
  (* passed as argument and counted as effect *)
  Option.map_default ~f:(RegionList.mem r) ~default:true region_list

let assigns ~type_safe ?region_list before ef =
  function
  | None -> True
  | Some (pos, locs) ->
    let p = (new assertion ~pos JCAtrue :> < mark : _; pos : _ > ) in
    (VarMap.fold
       (fun v _labs m -> StringMap.add v.vi_final_name false m)
       ef.fe_writes.e_globals
       StringMap.empty,
     MemoryMap.(
       fold
         (fun fir _labs ->
            Fn.on
              (external_region ?region_list fir)
              (add fir []))
         ef.fe_writes.e_memories
         empty))
    |>
    List.fold_right
      (collect_locations ~type_safe ~in_clause:`Assigns ~global_assertion:false before)
      locs
    |> fun (refs, mems) ->
    True |>
    StringMap.fold
      (fun v const ->
         Fn.on'
           (not const) @@
         fun () -> O.P.(&&) @@
           let at' = lvar ~constant:false ~label_in_name:false in
           P.locate ~p ~kind:JCVCassigns @@ O.P.(Poly `Eq $ at' LabelHere v ^. at' before v))
      refs
    |>
    MemoryMap.fold
      (fun (mc, r) pes acc ->
         let O.T.Hlist args =
           let mem = memory_name (mc, r) in
           let at = Name.alloc_table (alloc_class_of_mem_class mc, r) in
           let lvar_at lab v : some_term = Term (lvar ~constant:false ~label_in_name:false lab v) in
           let ps, _ = List.split pes in
           O.T.hlist_of_list
             [lvar_at before at;
              lvar_at LabelHere at;
              lvar_at before mem;
              lvar_at LabelHere mem;
              Term (pset_union_of_list ps)]
         in
         let mem_assigns = P.locate ~p ~kind:JCVCassigns @@ App (O.F.jc "not_assigns", args) in
         O.P.(acc && mem_assigns))
      mems

let loop_assigns ~type_safe ?region_list before ef =
  Option.map_default
    ~default:True
    ~f:(fun locs -> assigns ~type_safe ?region_list before ef @@ Some (Why_loc.dummy_position, locs))

let reads ~type_safe ~global_assertion locs (mc, r) =
  (StringMap.empty, MemoryMap.empty) |>
  List.fold_right
    (collect_locations ~type_safe ~global_assertion ~in_clause:`Reads LabelOld)
    locs
  |> fun (_, mems) ->
  let ps, _efs = List.split @@ MemoryMap.find_or_default (mc, r) [] mems in
  pset_union_of_list ps


(******************************************************************************)
(*                                Expressions                                 *)
(******************************************************************************)

let bounded lb rb s =
  let n = Num.num_of_int s in Num.le_num lb n && Num.le_num n rb

let lbounded lb s =
  let n = Num.num_of_int s in Num.le_num lb n

let rbounded rb s =
  let n = Num.num_of_int s in Num.le_num n rb

let normalize ei n =
  ei.ei_min +/ Num.mod_num (n -/ ei.ei_min) (ei.ei_max -/ ei.ei_min +/ Int 1)

let rec const_int_term t =
  match t#node with
  | JCTconst (JCCinteger s) -> Some (Numconst.integer s)
  | JCTvar vi ->
    begin try
      let _, init =
        Stdlib.Hashtbl.find
          Typing.logic_constants_table
          vi.vi_tag
      in
      const_int_term init
    with
    | Not_found -> None
    end
  | JCTapp app ->
    begin try
      let _, init =
        Stdlib.Hashtbl.find
          Typing.logic_constants_table
          app.app_fun.li_tag
      in
      const_int_term init
    with
    | Not_found -> None
    end
  | JCTunary (uop, t) ->
    let no = const_int_term t in
    Option.fold_right'
      ~f:(fun n _ -> match uop with
        | `Uminus, `Integer -> Some (Num.minus_num n)
        | _ -> None)
      no
      None
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
  | JCTrange_cast_mod (t, ei) -> Option.map (normalize ei) (const_int_term t)
  | JCTconst _ | JCTshift _ | JCTderef _
  | JCTold _ | JCTat _
  | JCToffset _ | JCTaddress _ | JCTinstanceof _ | JCTbase_block _
  | JCTreal_cast _ | JCTif _ | JCTrange _
  | JCTcast _ | JCTmatch _ | JCTlet _ ->
    assert false

let rec const_int_expr e =
  match e # node with
  | JCEconst (JCCinteger s) -> Some (Numconst.integer s)
  | JCEvar vi ->
    begin try
      let _, init =
        Stdlib.Hashtbl.find
          Typing.logic_constants_table
          vi.vi_tag
      in
      const_int_term init
    with
    | Not_found -> None
    end
  | JCEapp call ->
    begin match call.call_fun with
    | JClogic_fun li ->
      begin try
        let _, init =
          Stdlib.Hashtbl.find
            Typing.logic_constants_table
            li.li_tag
        in
        const_int_term init
      with
      | Not_found -> None
      end
    | JCfun _ -> None
    end
  | JCErange_cast (e, _) -> const_int_expr e
  | JCErange_cast_mod (e, ei) -> Option.map (normalize ei) (const_int_expr e)
  | JCEunary (uop, e) ->
    let no = const_int_expr e in
    Option.fold_right'
      ~f:(fun n _ -> match uop with
        | `Uminus, `Integer -> Some (Num.minus_num n)
        | _ -> None)
      no
      None
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
  | JCEfresh _ ->
    assert false

let destruct_pointer e =
  let ptre, off =
    match e # node with
    | JCEshift (e1, e2) ->
      e1,
      (match const_int_expr e2 with
       | Some n -> Int_offset (Num.int_of_num n)
       | None -> Expr_offset e2)
    | _ -> e, Int_offset 0
  in
  match ptre#typ with
  | JCTpointer (_, lb, rb) -> ptre, off, lb, rb
  | _ -> assert false

let rec make_lets l e =
  match l with
  | [] -> e
  | (tmp, (Expr e' : some_expr)) :: l -> O.E.let_ tmp e' (fun _ -> make_lets l e)

let old_to_pre =
  function
  | LabelOld -> LabelPre
  | lab -> lab

let old_to_pre_term =
  Iterators.map_term
    (fun t ->
       match t#node with
       | JCTold t'
       | JCTat (t', LabelOld) ->
         new term_with ~node:(JCTat (t', LabelPre)) t
       | JCTderef (t', LabelOld, fi) ->
         new term_with ~node:(JCTderef (t', LabelPre, fi)) t
       | _ -> t)

let rec old_to_pre_lset lset =
  match lset#node with
  | JCLSvar _ -> lset
  | JCLSderef (lset, lab, fi, region) ->
    new location_set_with
      ~typ:lset#typ
      ~node:(JCLSderef (old_to_pre_lset lset, old_to_pre lab, fi, region))
      lset
  | JCLSrange (lset, t1, t2) ->
    new location_set_with
      ~typ:lset#typ
      ~node:(JCLSrange
               (old_to_pre_lset lset,
                Option.map old_to_pre_term t1,
                Option.map old_to_pre_term t2))
      lset
  | JCLSrange_term (lset, t1, t2) ->
    new location_set_with
      ~typ:lset#typ
      ~node:(JCLSrange_term
               (old_to_pre_term lset,
                Option.map old_to_pre_term t1,
                Option.map old_to_pre_term t2))
      lset
  | JCLSat (lset, lab) ->
    new location_set_with
      ~typ:lset#typ
      ~node:(JCLSat (old_to_pre_lset lset, old_to_pre lab))
      lset

let rec old_to_pre_loc loc =
  match loc#node with
  | JCLvar _ -> loc
  | JCLat (l, lab) ->
    new location_with
      ~typ:loc#typ
      ~node:(JCLat (old_to_pre_loc l, old_to_pre lab))
      loc
  | JCLderef (lset, lab, fi, region) ->
    new location_with
      ~typ:loc#typ
      ~node:(JCLderef (old_to_pre_lset lset, old_to_pre lab, fi, region))
      loc
  | JCLderef_term (t1, fi) ->
    new location_with
      ~typ:loc#typ
      ~node:(JCLderef_term (old_to_pre_term t1, fi))
      loc

let assumption al a' =
  let ef = List.fold_left Effect.assertion empty_effects al in
  let read_effects = local_read_effects ~callee_reads:ef ~callee_writes:empty_effects in
  O.E.mk (Black_box (Annot (True, O.Wt.void, read_effects, [], a', [])))

let check al a' =
  let ef = List.fold_left Effect.assertion empty_effects al in
  let read_effects = local_read_effects ~callee_reads:ef ~callee_writes:empty_effects in
  O.E.mk (Black_box (Annot (a', O.Wt.void, read_effects, [], True, [])))

(* decreases clauses: stored in global table for later use at each call sites *)

let decreases_clause_table = Hashtbl.create 17

let term_zero = new term ~typ:integer_type (JCTconst (JCCinteger "0"))

let dummy_measure = (term_zero, None)

let get_measure_for f =
  match !Options.termination_policy with
  | TPalways ->
    begin try
       Hashtbl.find decreases_clause_table (f.fun_tag)
     with
     | Not_found ->
       Hashtbl.add decreases_clause_table (f.fun_tag) dummy_measure;
       eprintf
            "Warning: generating dummy decrease variant for recursive \
             function %s. Please provide a real variant or set \
             termination policy to user or never\n%!" f.fun_name;
       dummy_measure
    end
  | TPuser ->
    begin try
      Hashtbl.find decreases_clause_table (f.fun_tag)
    with
    | Not_found -> raise Exit
    end
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

let rec make_upd_simple ~e e1 fi tmp2 =
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
  let p' = expr Any p in
  let i' = offset off in
  let shift, upd =
    let open O.E in
    if safety_checking () then
      let tag = tag_table_var (struct_root fi.fi_struct, e1#region) in
      let tag_id = var (Name.tag fi.fi_struct) in
      let typesafe = (pointer_struct e1#typ).si_final in
      (if P.(off = Int_offset 0) then
         var tmpp
       else if not typesafe then
         E.locate ~e ~kind:JCVCpointer_shift (O.F.jc_val "shift_" $ tag ^ var tmpp ^ tag_id ^. var tmpi)
       else
         O.F.jc_val "safe_shift_" $ var tmpp ^. var tmpi),

      if P.(off = Int_offset 0) then
        E.locate ~e ~kind:JCVCpointer_deref (O.F.jc_val "upd_" $ alloc ^ var mem ^ var tmpp ^. var tmp2)
      else if not typesafe then
        E.locate ~e ~kind:JCVCpointer_deref
          (O.F.jc_val "offset_upd_" $ alloc ^ tag ^ var mem ^ var tmpp ^ tag_id ^ var tmpi ^. var tmp2)
      else
        E.locate ~e ~kind:JCVCpointer_deref
          (O.F.jc_val "offset_typesafe_upd_" $ alloc ^ var mem ^ var tmpp ^ var tmpi ^. var tmp2)
    else
      O.F.jc_val "safe_shift_" $ var tmpp ^. var tmpi,
      O.F.jc_val "safe_upd_" $ var mem ^ var tmp1 ^. var tmp2
  in
  let letspi = O.E.[tmpp, some p'; tmpi, some i'; tmp1, some shift] in
  tmp1, letspi, upd

and make_upd_union ~e:_ _off _e1 _fi _tmp2 = assert false
  (*let e1' = expr e1 in
  (* Convert value assigned into bitvector *)
  let e2' =
    match fi.fi_type with
    | JCTenum ri -> make_app (logic_bitvector_of_enum_name ri) [mk_var tmp2]
    | JCTnative Tinteger -> make_app logic_bitvector_of_integer_name [mk_var tmp2]
    | JCTnative _
    | JCTtype_var _
    | JCTpointer (_, _, _)
    | JCTlogic _
    | JCTany
    | JCTnull ->
      Options.jc_error e1#pos "Unsupported bv type conversion" (* TODO ? *)
  in
  (* Temporary variables to avoid duplicating code *)
  let tmp1 = tmp_var_name () in
  let tmp2 = tmp_var_name () in
  let v1 = Common.var e1#typ tmp1 in
  let e1 = new expr_with ~node:(JCEvar v1) e1 in
  let size =
    match fi.fi_bitsize with
    | Some x -> x / 8
    | None -> failwith "make_upd_union: field without bitsize in bv region"
  in
  let union_size = (union_type e1#typ).ri_union_size_in_bytes in
  let e2' =
    if size = union_size then
      (* TODO: deal with offset which should be null *)
      e2'
    else
      (* Retrieve bitvector for access to union *)
      let deref = make_deref_simple ~e e1 fi in
      (* Replace subpart of bitvector for specific subfield *)
      let off =
        match off with
        | Int_offset s -> s
        | _ -> Options.jc_error e1#pos "Unsupported offset in expression" (* TODO *)
      in
      let off = string_of_int off and size = string_of_int size in
      make_app "replace_bytes"
        [deref; mk_expr (Cte (Prim_int off)); mk_expr (Cte (Prim_int size)); e2']
  in
  let lets = [tmp1, e1'; tmp2, e2'] in
  let tmp1, lets', e' = make_upd_simple ~e e1 fi tmp2 in
  tmp1, lets @ lets', e'*)

and make_upd_bytes ~e:_ _e1 _fi _tmp2 = assert false
  (*let e1' = expr e1 in
  (* Convert value assigned into bitvector *)
  let e2' =
    match fi.fi_type with
    | JCTenum ri -> make_app (logic_bitvector_of_enum_name ri) [mk_var tmp2]
    | _ty -> Options.jc_error e#pos "Unsupported field type in bv update" (* TODO *)
  in
  (* Temporary variables to avoid duplicating code *)
  let tmp1 = tmp_var_name () in
  let v1 = Common.var e1#typ tmp1 in
  let e1 = new expr_with ~node:(JCEvar v1) e1 in
  (* Define memory and allocation table *)
  let mem = plain_memory_var (JCmem_bitvector,e1#region) in
  let alloc = alloc_table_var (JCalloc_bitvector,e1#region) in
  (* Store bitvector *)
  let off =
    match field_offset_in_bytes fi with
    | Some x -> x
    | None -> failwith "make_upd_bytes: field without offset in bytes in bv region"
  in
  let size =
    match fi.fi_bitsize with
    | Some x ->  x / 8
    | None -> failwith "make_upd_bytes: field without bitsize in bv region"
  in
  let off = string_of_int off and size = string_of_int size in
  let e' =
    if safety_checking () then
      make_vc_app_e ~e  ~kind:JCVCpointer_deref "upd_bytes_" @@
        [alloc; mem; mk_var tmp1;
         mk_expr (Cte (Prim_int off)); mk_expr (Cte (Prim_int size));
         mk_var tmp2]
    else
      make_app "safe_upd_bytes_"
        [mem; mk_var tmp1; mk_expr @@ Cte (Prim_int off);
          mk_expr @@ Cte (Prim_int size); mk_var tmp2]
  in
  let lets = [tmp1, e1'; tmp2, e2'] in
    tmp1, lets, e'*)

and make_upd ~e e1 fi e2 =
  (* Value assigned stored in temporary at that point *)
  let v2 = match e2#node with JCEvar v2 -> v2 | _ -> invalid_arg "make_upd" in
  let tmp2 = v2.vi_name in
  (* Dispatch depending on kind of memory *)
  let mc, ufi_opt = deref_mem_class ~type_safe:false e1 fi in
  match mc, ufi_opt with
  | JCmem_field fi', None ->
    assert (fi.fi_tag = fi'.fi_tag);
    make_upd_simple ~e e1 fi tmp2
  | JCmem_field fi', Some ufi ->
    assert (fi.fi_tag = fi'.fi_tag);
    let tmp1, lets, e1' = make_upd_simple ~e e1 fi tmp2 in
    let mems = overlapping_union_memories ufi in
    let ef =
      List.fold_left
        (fun ef mc -> add_memory_effect LabelHere ef (mc, e1#region))
        empty_effects
        mems
    in
    let write_effects = local_write_effects ~callee_reads:empty_effects ~callee_writes:ef in
    let e2' = O.E.mk (Black_box (Annot (True, O.Wt.void, [], write_effects, True, []))) in
    tmp1, lets, O.E.(e1' ^^ e2')
  | JCmem_plain_union _vi, _ ->
    let e1, off = destruct_union_access e1 (Some fi) in
    make_upd_union ~e off e1 fi tmp2
  | JCmem_bitvector, _ ->
    make_upd_bytes ~e e1 fi tmp2

(* Translate the heap access `e.fi'

   special cases are considered to avoid statically known safety properties:
   if e1 has the form p + i then we build an access that depends on the
   type of p and the value of i
*)
and make_deref_simple ~e e1 fi =
  (* Define memory and allocation table *)
  let mc, _ufi_opt = deref_mem_class ~type_safe:false e1 fi in
  let mem = memory_var (mc, e1#region) in
  let ac = alloc_class_of_mem_class mc in
  let alloc = alloc_table_var (ac, e1#region) in
  let open O.E in
  if safety_checking () then
    let tag = tag_table_var (struct_root fi.fi_struct, e1#region) in
    let tag_id = var (Name.tag fi.fi_struct) in
    let expr = expr Any in
    match destruct_pointer e1, (pointer_struct e1#typ).si_final with
    | (_, (Int_offset s as off), Some lb, Some rb), false when bounded lb rb s ->
      E.locate ~e ~kind:JCVCpointer_deref
        (O.F.jc_val "safe_acc_requires_" $ tag ^ mem ^ expr e1 ^ tag_id ^. offset off)
    | (_, Int_offset s, Some lb, Some rb),        true when bounded lb rb s ->
      E.locate ~e ~kind:JCVCpointer_deref
        (O.F.jc_val "safe_typesafe_acc_requires_" $ mem ^. expr e1)
    | (p, (Int_offset s as off), Some lb, _), false when lbounded lb s ->
      E.locate ~e ~kind:JCVCpointer_deref_bounds
        (O.F.jc_val "lsafe_lbound_acc_" $ tag ^ alloc ^ mem ^ expr p ^ tag_id ^. offset off)
    | (p, (Int_offset s as off), Some lb, _), true when lbounded lb s ->
      E.locate ~e ~kind:JCVCpointer_deref_bounds
        (O.F.jc_val "lsafe_lbound_typesafe_acc_" $ alloc ^ mem ^ expr p ^. offset off)
    | (p, (Int_offset s as off), _, Some rb), false when rbounded rb s ->
      E.locate ~e ~kind:JCVCpointer_deref_bounds
        (O.F.jc_val "rsafe_rbound_acc_" $ tag ^ alloc ^ mem ^ expr p ^ tag_id ^. offset off)
    | (p, (Int_offset s as off), _, Some rb), true when rbounded rb s ->
      E.locate ~e ~kind:JCVCpointer_deref_bounds
        (O.F.jc_val "rsafe_rbound_typesafe_acc_" $ tag ^ alloc ^ mem ^ expr p ^ tag_id ^. offset off)
    | (p, Int_offset 0, None, None), _ ->
      E.locate ~e ~kind:JCVCpointer_deref
        (O.F.jc_val "acc_"  $ alloc ^ mem ^. expr p)
    | (p, off, _, _), false ->
      E.locate ~e ~kind:JCVCpointer_deref
        (O.F.jc_val "offset_acc_" $ alloc ^ tag ^ mem ^ expr p ^ tag_id ^. offset off)
    | (p, off, _, _), true ->
      E.locate ~e ~kind:JCVCpointer_deref
        (O.F.jc_val "offset_typesafe_acc_" $ alloc ^ mem ^ expr p ^. offset off)
  else
    O.F.jc_val "safe_acc_" $ mem ^. expr Any e1

and make_deref_union ~e:_ _off _e1 _fi = assert false
  (*(* Retrieve bitvector *)
  let e' = make_deref_simple ~e e1 fi in
  (* Retrieve subpart of bitvector for specific subfield *)
  let off =
    match off with
    | Int_offset s -> s
    | _ -> Options.jc_error e#pos "Usnupported offset" (* TODO *)
  in
  let size =
    match fi.fi_bitsize with
      | Some x -> x / 8
      | None -> failwith "make_deref_union: field without bitsize in bv region"
  in
  let off = string_of_int off and size = string_of_int size in
  let e' = make_app "extract_bytes" [e'; mk_expr @@ Cte (Prim_int off); mk_expr @@ Cte (Prim_int size)] in
  (* Convert bitvector into appropriate type *)
  match fi.fi_type with
  | JCTenum ri -> make_app (logic_enum_of_bitvector_name ri) [e']
  | _ty -> Options.jc_error e#pos "Unsupported field type in bv update" (* TODO *)*)

and make_deref_bytes ~_e _e1 _fi = assert false
  (*(* Define memory and allocation table *)
  let mem = memory_var (JCmem_bitvector, e1#region) in
  let alloc = alloc_table_var (JCalloc_bitvector, e1#region) in
  (* Retrieve bitvector *)
  let off =
    match field_offset_in_bytes fi with
    | Some x -> x
    | None -> failwith "make_upd_bytes: field without offset in bv region"
  in
  let size =
    match fi.fi_bitsize with
    | Some x ->  x / 8
    | None -> failwith "make_upd_bytes: field without bitsize in bv region"
  in
  let off = string_of_int off and size = string_of_int size in
  let e' =
    if safety_checking () then
      make_vc_app_e ~e ~kind:JCVCpointer_deref "acc_bytes_"
        [alloc; mem; expr e1; mk_expr @@ Cte (Prim_int off); mk_expr @@ Cte (Prim_int size)]
    else
      make_app "safe_acc_bytes_"
        [mem; expr e1; mk_expr @@ Cte (Prim_int off); mk_expr @@ Cte (Prim_int size)]
  in
  (* Convert bitvector into appropriate type *)
  match fi.fi_type with
  | JCTenum ri -> make_app (logic_enum_of_bitvector_name ri) [e']
  | JCTnative t ->
    begin match t with
      | Treal  -> unsupported e#pos "bit-dependent cast over real numbers"
      | Tgenfloat _ -> unsupported e#pos "bit-dependent cast over floating-point values"
      | Tstring -> unsupported e#pos "bit-dependent cast over strings"
      | Tinteger -> unsupported e#pos "bit-dependent cast over integers"
      | Tboolean -> unsupported e#pos "bit-dependent cast over booleans"
      | Tunit  -> unsupported e#pos "bit-dependent cast over type unit"
    end
  | JCTtype_var _
  | JCTpointer (_, _, _)
  | JCTlogic _
  | JCTany
  | JCTnull -> unsupported e#pos "Unsupported type in bit-dependent cast" (* TODO *)*)

and make_deref ~e e1 fi =
  (* Dispatch depending on kind of memory *)
  let mc, _uif_opt = deref_mem_class ~type_safe:false e1 fi in
  match mc with
  | JCmem_field _ -> make_deref_simple ~e e1 fi
  | JCmem_plain_union _vi -> assert false
    (*let e1, off = destruct_union_access e1 (Some fi) in
      make_deref_union ~e off e1 fi*)
  | JCmem_bitvector -> assert false
    (*make_deref_bytes ~e e1 fi*)

and offset =
  function
  | Int_offset s -> O.E.mk (Const (Int (string_of_int s)))
  | Expr_offset e -> expr (Ty (O.Ty.integer)) e
  | Term_offset _ -> invalid_arg "offset"

and type_assert  tmp ty' e =
  let offset k e1 ty tmp =
    let ac = deref_alloc_class ~type_safe:false e1 in
    let _, alloc = talloc_table_var ~label_in_name:false LabelHere (ac, e1#region) in
    match ac with
    | JCalloc_root _ ->
      let f =
        match k with
        | Offset_min -> "offset_min"
        | Offset_max -> "offset_max"
      in
      O.T.(O.F.jc f $ alloc ^. var tmp)
    | JCalloc_bitvector ->
      let st = pointer_struct ty in
      let f =
        match k with
        | Offset_min -> "offset_min_bytes"
        | Offset_max -> "offset_max_bytes"
      in
      let s = string_of_int (struct_size_in_bytes st) in
      O.T.(F.jc f $ alloc ^ var tmp ^. Const (Int s))
  in
  let a =
    match ty' with
    | JCTpointer(_pc,n1o,n2o) ->
      let offset_mina n =
        O.P.(F.jc "le_int" $ offset Offset_min e ty' tmp ^. Const (Int (string_of_num n)))
      in
      let offset_maxa n =
        O.P.(F.jc "ge_int" $ offset Offset_max e ty' tmp ^. Const (Int (string_of_num n)))
      in
      begin match e#typ with
      | JCTpointer (_si', n1o', n2o') ->
        begin match n1o, n2o with
        | None, None -> True
        | Some n, None ->
          begin match n1o' with
          | Some n'
            when n' <=/ n && not Options.verify_all_offsets -> True
          | _ -> offset_mina n
          end
        | None, Some n ->
          begin match n2o' with
          | Some n'
            when n' >=/ n && not Options.verify_all_offsets -> True
          | _ -> offset_maxa n
          end
        | Some n1, Some n2 ->
          begin match n1o', n2o' with
          | None, None -> O.P.(offset_mina n1 && offset_maxa n2)
          | Some n1', None ->
            if n1' <=/ n1 && not Options.verify_all_offsets
            then offset_maxa n2
            else O.P.(offset_mina n1 && offset_maxa n2)
          | None, Some n2' ->
            if n2' >=/ n2 && not Options.verify_all_offsets
            then offset_mina n1
            else O.P.(offset_mina n1 && offset_maxa n2)
          | Some n1', Some n2' ->
            if Options.verify_all_offsets
            then O.P.(offset_mina n1 && offset_maxa n2)
            else if n1' <=/ n1 then
              if n2' >=/ n2
              then True
              else offset_maxa n2
            else if n2' >=/ n2
            then offset_mina n1
            else O.P.(offset_mina n1 && offset_maxa n2)
          end
        end
      | JCTnull ->
        begin match n1o, n2o with
        | None, None -> True
        | Some n, None -> offset_mina n
        | None, Some n -> offset_maxa n
        | Some n1, Some n2 -> O.P.(offset_mina n1 && offset_maxa n2)
        end
      | _ -> True
      end
    | _ -> True
  in
  a

and list_type_assert vi e (lets, params) =
  let ty' = vi.vi_type in
  let tmp = tmp_var_name () (* vi.vi_name *) in
  let a = type_assert tmp ty' e in
  (tmp, some_expr e, a) :: lets, O.E.(some @@ var tmp) :: params

and value_assigned ~e ty' e1 =
  let Typ typ = ty ty' in
  let tmp = tmp_var_name () in
  let a = P.locate ~p:e ~kind:JCVCindex_bounds @@ type_assert tmp ty' e1 in
  let e = expr typ e1 in
  if a <> True && safety_checking ()
  then (Expr (O.E.let_ tmp e O.E.(fun _ -> mk (Assert (`ASSERT, a)) ^^ var tmp)) : some_expr)
  else Expr e

and make_reinterpret ~e e1 st =
  let get_fi st =
    match st.si_fields with
    | [fi] -> fi
    | _ -> unsupported ~loc:e1#pos "reinterpretation for structure with several fields"
  in
  let s_from, fi_from = (* src. subtag & field info *)
    match e1#typ with
    | JCTpointer (JCtag (st, _), _, _) -> Name.tag st, get_fi st
    | _ -> unsupported ~loc:e1#pos "reinterpretation for a root pointer or a non-pointer"
  in
  let s_to, fi_to = Name.tag st, get_fi st in (* dest. subtag & field_info *)
  let ac = deref_alloc_class ~type_safe:false e1 in
  let mc_from, mc_to = Pair.map (fst % deref_mem_class ~type_safe:false e1) (fi_from, fi_to) in
  let before = fresh_reinterpret_label () in

  (* call to [safe]_reinterpret_parameter *)
  let call_parameter =
    let alloc = plain_alloc_table_var (ac, e1#region) in
    let tag = tag_table_var (struct_root st, e1#region) in
    let mem_to = plain_memory_var (mc_to, e1#region) in
    let open O.E in
    [before.lab_final_name] @:
    match P.(!Options.inv_sem) with
    | InvOwnership ->
      unsupported ~loc:e1#pos "reinterpret .. as construct is not supported when inv_sem = InvOwnership"
    | InvNone | InvArguments ->
      E.locate ~e
        (O.F.reinterpret ~safe:(safety_checking ()) $
         alloc ^ tag ^ var s_from ^ var s_to ^ mem_to ^. expr Any e1)
  in

  (* Let's now switch to terms and assume predicates instead of calling params... *)
  let before = LabelName before in
  let _, tag = ttag_table_var ~label_in_name:false LabelHere (struct_root st, e1#region) in
  let alloc = Name.alloc_table (ac, e1#region) in
  let at' = lvar ~constant:false ~label_in_name:false in
  (* reinterpretation kind (operation):
     merging (e.g. char -> int) / splitting (e.g. int -> char) / plain (e.g. int -> long) *)
  let op =
    let from_bitsize, to_bitsize =
      Pair.map
        (fi_from, fi_to)
        ~f:(function
         | { fi_bitsize = Some s } -> s
         | _ -> unsupported ~loc:e1#pos "reinterpretation for field with no bitsize specified")
    in
    match compare from_bitsize to_bitsize with
    | 0 -> `Retain
    | v when v > 0 -> `Split (from_bitsize / to_bitsize)
    | _ -> `Merge (to_bitsize / from_bitsize)
  in
  let e' =
    term
      Any
      ~type_safe:(safety_checking ())
      ~global_assertion:false
      ~relocate:false
      LabelHere
      before @@
        match term_of_expr e1 with
        | Some e -> e
        | None ->
          unsupported ~loc:e1#pos "the argument for reinterpret .. as should be an expression without side effects"
  in

  let alloc_assumption =
    let app l =
      O.P.(F.reinterpret_cast op $ tag ^ at' before alloc ^ at' LabelHere alloc ^ e' ^ T.var s_to ^ l)
    in
    match op with
    | `Retain -> app Nil
    | `Merge c | `Split c -> app O.T.(int c ^ Nil)
  in

  let mem =
    let old_mem, new_mem = Pair.map (fun mc -> memory_name (mc, e1#region)) (mc_from, mc_to) in
    function
    | `Old -> at' before old_mem
    | `New -> at' LabelHere new_mem
  in

  (* Assume reinterpretation predicates for all corresponingly shifted pointers *)
  let memory_assumption =
    let open O.P in
    let_ "p" e'
      (fun p ->
         let_ "ps" T.(F.jc "downcast" $ tag ^ e' ^. var s_to)
           (fun ps ->
              let omin_omax =
                let app f =
                  let open O.T in
                  function
                  | `Old -> O.F.jc f $ at' before alloc ^. p
                  | `New -> O.F.jc f $ at' LabelHere alloc ^. ps
                in
                (Fn.uncurry fdup2) @@ Pair.map app ("offset_min", "offset_max")
              in
              let deref (where, p) ?boff offs =
                let shift' t o1 o2 =
                  let open O.T in
                  match o1, o2 with
                  | None, None -> t
                  | Some o, None
                  | None, Some o -> shift t o
                  | Some o1, Some o2 -> shift t (o1 + o2)
                in
                O.T.(select (mem where) (shift' p boff @@ match offs with 0 -> None | o -> Some (int o)))
              in
              let pred_names =
                let enum_name =
                  function
                  | { fi_type = JCTenum { ei_type } } -> string_of_some_enum ei_type
                  | _ -> unsupported ~loc:e1#pos "reinterpretation for structure with a non-enum field"
                in
                let from_name, to_name = Pair.map enum_name (fi_from, fi_to) in
                P.[from_name ^ "_as_" ^ to_name; to_name ^ "_as_" ^ from_name]
              in
              let assumptions =
                let (dwhole, dpart), (omin, omax), c =
                  let ret ((w, _), _ as w_p) c = Pair.map deref w_p, omin_omax w, c in
                  let merge, split = fdup2 ret (ret % swap) ((`New, ps), (`Old, p)) in
                  match op with
                  | `Merge c -> merge c
                  | `Retain when P.((List.hd pred_names).[0] = 'u') -> merge 1
                  | `Retain -> split 1
                  | `Split c -> split c
                in
                let dparts boff = List.map (O.T.some % dpart ?boff) (List.range 0 `To (c - 1)) in
                ListLabels.map
                  pred_names
                  ~f:(fun pred_name ->
                    (("Jc_reinterpret", true), pred_name) $.. dwhole 0 ^.. dparts None &&
                    forall
                      "i"
                      O.Lt.integer
                      (fun i ->
                         let pred_app =
                           let imul = if P.(c > 1) then T.(i * int c) else i in
                           (("Jc_reinterpret", true), pred_name) $..
                           dwhole ~boff:i 0 ^.. dparts (Some imul)
                         in
                         if false (* change to enbale the antecedent (both ways are correct) *) then
                           impl (omin <= i && i <= omax) pred_app
                         else
                           pred_app))
              in
              conj assumptions))
  in

  let c =
    match op with
    | `Split c -> c
    | `Merge c -> -c
    | `Retain -> 1
  in

  let not_assigns_assumption =
    O.P.conj
      O.T.[F.jc "rmem" $. mem `Old = mem `New;
           F.jc "rfactor" $. mem `Old = int c;
           F.jc "rpointer_new" $ mem `Old ^. e' = (F.jc "downcast" $ tag ^ e' ^. var s_to)]
  in

  let cast_factor_assumption = O.T.(F.cast_factor () $ var s_from ^. var s_to = int c) in

  let ensures_assumption =
    let open O.E in
    assert_ `ASSUME alloc_assumption ^^
    assert_ `ASSUME memory_assumption ^^
    assert_ `ASSUME not_assigns_assumption
  in
  O.E.(assert_ `ASSUME cast_factor_assumption ^^ call_parameter ^^ ensures_assumption)

and expr : type a b. (a, b) ty_opt -> _ -> a expr = fun t e ->
  let infunction = get_current_function () in
  let return e = O.E.return t e in
  let e' =
    match e#node with
    | JCEconst JCCnull -> O.E.var "null"
    | JCEconst c -> O.E.mk (Const (const t c))
    | JCEvar v -> var v
    | JCEunary ((`Uminus, (`Double | `Float as format)), e2) ->
      let e2' = expr t e2 in
      if !Options.float_model <> FMmultirounding
      then
        E.locate ~e ~kind:JCVCfp_overflow O.E.(F.jc_val P.("neg_" ^ float_format format) $. e2')
      else
        E.locate
          ~e
          ~kind:JCVCfp_overflow
          O.E.(F.jc_val P.(float_operator `Uminus format) $ current_rounding_mode Expr ^. e2')
    | JCEunary (op, e1) ->
      let Unary (f, t) = un_op ~e op in
      return O.E.(f $. expr (Ty t) e1)
    | JCEbinary (e1, ((`Beq | `Bneq as o), `Pointer), e2) when safety_checking () ->
      let is_null e = e#node = JCEconst JCCnull in
      if is_null e1 && is_null e2 then
         return @@ O.E.mk @@ Const (Bool true)
      else
        let dummy e1 e2 = if is_null e1 then e2 else e1 in
        let e1, e1', e2, e2' = dummy e1 e2, expr Any e1, dummy e2 e1, expr Any e2 in
        let at1, at2 =
          let ac1, ac2 = Pair.map (deref_alloc_class ~type_safe:false) (e1, e2) in
          Pair.map alloc_table_var ((ac1, e1#region), (ac2, e2#region))
        in
        E.locate ~e @@
        O.E.(F.jc_val (match o with `Beq -> "eq_pointer" | `Bneq -> "neq_pointer") $ at1 ^ at2 ^ e1' ^. e2')
    | JCEbinary (e1, (_, (`Pointer | `Logic) as op), e2) ->
      begin match bin_op ~e op with
      | Op (f, t) -> return O.E.(f $ expr t e1 ^. expr t e2)
      | Rel (f, t) -> return O.E.(f $ expr t e1 ^. expr t e2)
      end
    | JCEbinary (e1, (`Bland, _), e2) ->
      return O.E.(E.locate ~e:e1 @@ expr (Ty Bool) e1 && E.locate ~e:e2 @@ expr (Ty Bool) e2)
    | JCEbinary (e1, (`Blor, _), e2) ->
      return O.E.(E.locate ~e:e1 @@ expr (Ty Bool) e1 || E.locate ~e:e2 @@ expr (Ty Bool) e2)
    | JCEbinary (e1, (#arithmetic_op as op, (`Double | `Float | `Binary80 as format)), e2) ->
      E.locate ~e ~kind:JCVCfp_overflow @@
      O.E.(F.jc_val (float_operator op format) $ current_rounding_mode Expr ^ expr t e1 ^. expr t e2)
    | JCEbinary (e1, op, e2) ->
      let return e' =
        match fst op with
        | `Bdiv | `Bmod -> return (E.locate ~e ?behavior:None ~kind:JCVCdiv_by_zero e')
        | _ -> return e'
      in
      begin match bin_op ~e op with
      | Op (f, t) -> return O.E.(f $ expr t e1 ^. expr t e2)
      | Rel (f, t) -> return O.E.(f $ expr t e1 ^. expr t e2)
      end
    | JCEshift (e1, e2) ->
      begin match
        match e1#typ with
        | JCTpointer (JCtag ({ si_final = true }, []), _, _) -> None
        | JCTpointer (JCtag (st, []), _, _) -> Some (tag_table_var (struct_root st, e1#region), O.E.var @@ Name.tag st)
        | _ -> None
      with
      | Some (tt, tag) ->
        O.E.(F.jc_val "shift_" $ tt ^ expr Any e1 ^ tag ^. expr (Ty O.Ty.integer) e2)
      | None ->
        O.E.(F.jc_val "safe_shift_" $ expr Any e1 ^. expr (Ty O.Ty.integer) e2)
      end
    | JCEif (e1, e2, e3) ->
      O.E.(if_ (E.locate ~e:e1 @@ expr (Ty Bool) e1) (expr t e2) (expr t e3))
    | JCEoffset (k, e1, st) ->
      let ac = deref_alloc_class ~type_safe:false e1 in
      let alloc = alloc_table_var (ac, e1#region) in
      begin match ac with
      | JCalloc_root _ ->
        let f =
          match k with
          | Offset_min -> "offset_min"
          | Offset_max -> "offset_max"
        in
        O.E.(F.jc f $ alloc ^. expr Any e1)
      | JCalloc_bitvector ->
        let f =
          match k with
          | Offset_min -> "offset_min_bytes"
          | Offset_max -> "offset_max_bytes"
        in
        let s = string_of_int (struct_size_in_bytes st) in
        O.E.(F.jc f $ alloc ^ expr Any e1 ^. mk (Const (Int s)))
      end
    | JCEaddress (Addr_absolute, e1) ->
      O.E.(F.jc "absolute_address" $. expr Any e1)
    | JCEaddress (Addr_pointer, e1) ->
      O.E.(F.jc "address" $. expr Any e1)
    | JCEbase_block e1 ->
      O.E.(F.jc "base_block" $. expr Any e1)
    | JCEfresh _ -> Options.jc_error e#pos "Unsupported \\fresh as expression"
    | JCEinstanceof (e1, st) ->
      let tag = tag_table_var (struct_root st, e1#region) in
      (* always safe *)
      O.E.(F.jc "instanceof_"  $ tag ^ expr Any e1 ^. var (Name.tag st))
    | JCEcast (e1, st) ->
      let tag = tag_table_var (struct_root st, e1#region) in
      if struct_of_union st
      then expr Any e1
      else
        O.E.((if safety_checking () then
                (fun args -> E.locate ~e ~kind:JCVCdowncast (F.jc "downcast_" $ args))
              else
                ($) (F.jc "safe_downcast_"))
               (tag ^ expr Any e1 ^. var (Name.tag st)))
    | JCErange_cast (e1, _ri) ->
      let Typ from_typ = ty e1#typ in
      coerce
        t
        from_typ
        Expr
        ~e
        ~e1
        (expr from_typ e1)
    | JCErange_cast_mod (e1, ei) ->
      let e1 = expr (Ty (Numeric (Integral Integer))) e1 in
      let return i = return O.E.(Of_int (i, true) $. e1) in
      begin match ei.ei_type with
        | Enum e -> return (Enum e)
        | Int (r, b) -> return (Int (r, b))
      end
    | JCEreal_cast (e1, rc) ->
      let Typ typ = ty e1#typ in
      let e1' = expr typ e1 in
      begin match rc with
      | Integer_to_real
      | Double_to_real
      | Float_to_real ->
        coerce
          t
          typ
          Expr
          ~e
          ~e1
          e1'
      | Round (_f, _rm) ->
        coerce
          t
          typ
          Expr
          ~e
          ~e1
          e1'
      end
    | JCEderef (e1, fi) -> return @@ make_deref ~e e1 fi
    | JCEalloc (e1, st) ->
      let e1' = expr Any e1 in
      let ac = deref_alloc_class ~type_safe:false e in
      let pc = JCtag (st, []) in
      if !Options.inv_sem = InvOwnership then
        assert false
      else
        begin match e1#node with
        | JCEconst JCCinteger s
          when (try let n = int_of_string s in n == 1 with Failure "int_of_string" -> false) ->
          Interp_struct.alloc ~arg:Singleton (ac, e#region) pc
        | _ ->
          E.locate
            ~e
            ~kind:JCVCalloc_size
            (Interp_struct.alloc ~arg:Range_0_n ~check_size:(safety_checking ()) (ac, e#region) pc e1')
        end
    | JCEfree e1 ->
      let e1' = expr Any e1 in
      let ac = deref_alloc_class ~type_safe:false e1 in
      let pc = pointer_class e1#typ in
      if !Options.inv_sem = InvOwnership then
        assert false
      else
        return @@
        E.locate ~e @@
        Interp_struct.free ~safe:(not @@ safety_checking ()) (ac, e1#region) pc e1'
    | JCEreinterpret (e1, st) -> return @@ make_reinterpret ~e e1 st
    | JCEapp call ->
      begin match call.call_fun with
      | JClogic_fun _f ->
        assert false
        (*let arg_types_asserts, args =
          match f.li_parameters with
          | [] -> [], []
          | params ->
            List.fold_right2 list_type_assert params call.call_args ([], [])
        in
        let param_assoc = List.map2 (fun param arg -> param, arg) f.li_parameters call.call_args in
        let with_body =
          try
            let _f, body = IntHashtblIter.find Typing.logic_functions_table f.li_tag in
            match body with
            | JCTerm _ -> true
            | JCNone | JCReads _ -> false
            | JCAssertion _ | JCInductive _ ->
              unsupported ~loc:e#pos "Explicit call of purely logic function in expression"
          with
          |Not_found -> false
        in
        let pre, fname, locals, prolog, epilog, args =
          make_arguments
            ~callee_reads: f.li_effects
            ~callee_writes: empty_effects
            ~region_assoc: call.call_region_assoc
            ~param_assoc
            ~with_globals:true
            ~with_body
            f.li_final_name args
        in
        assert (pre = True);
        assert (fname = f.li_final_name);
        make_logic_app fname args |>
        (let new_arg_types_assert = List.fold_right (fun (_tmp, _e, a) -> make_and a) arg_types_asserts LTrue in
         Fn.on (new_arg_types_assert <> LTrue && safety_checking ())
           (fun call -> mk_expr @@ Assert (`ASSERT, new_arg_types_assert, call)))
        |>
        List.fold_right (fun (tmp, e, _ass) c -> mk_expr @@ Let (tmp, e, c)) arg_types_asserts |>
        append prolog |>
        Fn.on (epilog.expr_node <> Void)
          (fun call ->
             let tmp = tmp_var_name () in
             mk_expr @@ Let (tmp, call, append epilog @@ mk_var tmp))
        |>
          define_locals ~writes:locals*)

      | JCfun f ->
        let arg_types_asserts, args =
          match f.fun_parameters with
          | [] -> [], []
          | params ->
            let params = List.map snd params in
            List.fold_right2 list_type_assert params call.call_args ([] ,[])
        in
        let param_assoc = List.map2 (fun (_, param) arg -> param, arg) f.fun_parameters call.call_args in
        let mod_ = f.fun_final_name ^ if safety_checking () then  "_requires" else "" in
        let fname = f.fun_final_name in
        let with_body =
          try
            let _f, _loc, _s, body = IntHashtblIter.find Typing.functions_table f.fun_tag in
            body <> None
          with
          | Not_found -> false
        in
        let args =
          match f.fun_builtin_treatment with
          | TreatNothing -> args
          | TreatGenFloat format ->
            O.E.(some (var (float_format format)) :: some (current_rounding_mode Expr) :: args)
        in
        let pre, fname, locals, _prolog, _epilog, new_args =
          make_arguments
            ~callee_reads:f.fun_effects.fe_reads
            ~callee_writes:f.fun_effects.fe_writes
            ~region_assoc:call.call_region_assoc
            ~param_assoc
            ~with_globals:false
            ~with_body
            fname
            args
        in
        E.locate ~e ~kind:(JCVCuser_call f.fun_name) O.E.(((mod_, true), fname) $.. new_args) |>
        (* decreases *)
        (let this_comp = f.fun_component in
         let current_comp = (get_current_function ()).fun_component in
         Fn.on'
           (safety_checking () && this_comp = current_comp) @@
         fun () ->
         try
           let cur_measure, cur_r = get_measure_for @@ get_current_function () in
           let cur_measure_why =
             term
               (Ty (O.Ty.integer))
               ~type_safe:true
               ~global_assertion:true
               ~relocate:false
               LabelPre LabelPre
               cur_measure
           in
           let this_measure, this_r = get_measure_for f in
           let subst =
             List.fold_left2
               (fun acc (_, vi) (tmp, _, _) -> VarMap.add vi O.T.(some @@ var tmp) acc)
               VarMap.empty
               f.fun_parameters
               arg_types_asserts
           in
           let this_measure_why =
             term
               (Ty (O.Ty.integer))
               ~subst
               ~type_safe:true
               ~global_assertion:true
               ~relocate:false
               LabelHere LabelHere
               this_measure
           in
           let r, _ty =
             assert (this_r = cur_r);
             match this_r with
             | None -> "zwf_zero", integer_type
             | Some li ->
               match li.li_parameters with
               | v1 :: _ -> li.li_name, v1.vi_type
               | _ ->
                 Options.jc_error
                   e#pos
                   "Can't generate termination condition: measure has no arguments (%s)"
                   li.li_name
           in
           let pre = O.P.(O.F.jc r $ this_measure_why ^. cur_measure_why) in
           fun call ->
             E.locate
               ~e
               ~kind:JCVCvar_decr
               O.E.(mk  (Assert (`CHECK, pre)) ^^ call)
         with
         | Exit -> Fn.id)
        |>
        (* separation assertions *)
        Fn.on
          (pre <> True && safety_checking ())
          (fun call ->
             E.locate
               ~e
               ~kind:JCVCseparation
               O.E.(mk (Assert (`ASSERT, pre)) ^^ call))
        |>
         (let arg_types_assert = List.fold_right (fun (_tmp, _e, a) -> O.P.(&&) a) arg_types_asserts True in
          Fn.on
            (arg_types_assert <> True && safety_checking())
            (fun call ->
               E.locate
                 ~e
                 ~kind:JCVCindex_bounds
                 O.E.(mk (Assert (`ASSERT, arg_types_assert)) ^^ call)))
        |>
        List.fold_right (fun (tmp, (Expr e : some_expr), _ass) c -> O.E.let_ tmp e (fun _ -> c)) arg_types_asserts |>
        define_locals ~writes:locals
      end
    | JCEassign_var (v, e1) ->
      let Expr e1 = value_assigned ~e v.vi_type e1 in
      let e' = O.E.(mk @@ Assign (v.vi_final_name, e1)) in
      if e#typ = Common.unit_type
      then return e'
      else return O.E.(e' ^^ var v.vi_final_name)
    | JCEassign_heap (e1, fi, e2) ->
      let e2' = value_assigned ~e fi.fi_type e2 in
      (* Define temporary variable for value assigned *)
      let tmp2 = tmp_var_name () in
      let v2 = Common.var fi.fi_type tmp2 in
      let e2 = new expr_with ~typ:fi.fi_type ~node:(JCEvar v2) e2 in
      (* Translate assignment *)
      let _tmp1, lets, e' = make_upd ~e e1 fi e2 in
      let e' =
        if (safety_checking()) && !Options.inv_sem = InvOwnership
        then assert false
        else e'
      in
      let lets = (tmp2, e2') :: lets in
      let e' =
        if e#typ = Common.unit_type
        then make_lets lets e'
        else make_lets lets O.E.(e' ^^ (var tmp2))
      in
      return e'

    | JCEblock el ->
      return O.E.(mk @@ Block (List.map (expr (Ty Void)) el, Void))
    | JCElet (v, e1, e2) ->
      let Typ typ = ty v.vi_type in
      let e1' =
        match e1 with
        | None -> nondet_value typ v.vi_type
        | Some e1 ->
          let Expr e = value_assigned ~e v.vi_type e1 in
          O.E.return typ e
      in
      let e2' = expr t e2 in
      if v.vi_assigned
      then O.E.(mk (Let_ref (v.vi_final_name, e1', e2')))
      else O.E.let_ v.vi_final_name e1' (fun _ -> e2')
    | JCEreturn_void -> O.E.mk (Raise (jessie_return_exception, None))
    | JCEreturn (ty, e1) ->
      let Expr e1' = value_assigned ~e ty e1 in
      let e' = O.E.(mk (Assign (jessie_return_variable, e1'))) in
      O.E.(e' ^^ (mk (Raise (jessie_return_exception, None))))
    | JCEunpack (_st, _e1, _as_st) -> assert false
    | JCEpack (_st, _e1, _from_st) -> assert false
    | JCEassert (b, asrt, a) ->
      let a' =
        let kind =
          match asrt with
          | Aassert | Ahint when in_current_behavior b ->
            Some (JCVCassertion (lookup_pos a))
          | Acheck when in_current_behavior b ->
            Some
              (JCVCcheck
                (match a#mark with
                | "disjoint_behaviors" -> "behavior disjointness"
                | "complete_behaviors" -> "behavior completeness"
                | _ -> ""))
          | _ -> None
        in
        named_predicate
          ~type_safe:false ~global_assertion:false ?kind ~relocate:false
          LabelHere LabelPre a
      in
      begin match asrt with
      | Aassert | Ahint when in_current_behavior b ->
        return @@ O.E.(mk (Assert (`ASSERT, a')) ^^ void)
      | Aassert | Ahint when in_default_behavior b ->
        return (assumption [a] a')
      | Aassert | Ahint -> return O.E.void
      | Aassume when in_current_behavior b || in_default_behavior b ->
        return (assumption [a]  a')
      | Aassume -> return O.E.void
      | Acheck when in_current_behavior b ->
        return O.E.(mk (Assert (`CHECK, a')))
      | Acheck -> return O.E.void
      end
    | JCEloop (la, e1) ->
        infunction.fun_may_diverge <- true;
        let inv, assume_from_inv =
          List.fold_left
            (fun ((invariants, assumes) as acc) (names, inv,_) ->
               match inv with
               | Some i ->
                 if in_current_behavior names
                 then
                   (i :: invariants, assumes)
                 else if List.exists (fun behav -> behav#name = "default") names then
                   (invariants, i :: assumes)
                 else
                   (invariants, assumes)
               | None -> acc)
            ([], [])
            la.loop_behaviors
        in
        let inv' =
          O.P.conj
            (List.map
               (named_predicate
                  ~type_safe:false ~global_assertion:false ~relocate:false
                  LabelHere LabelPre)
               inv)
        in
        let assume_from_inv' =
          O.P.conj
            (List.map
               (named_predicate
                  ~type_safe:false ~global_assertion:false ~relocate:false
                  LabelHere LabelPre)
               assume_from_inv)
        in
        (* free invariant: trusted or not *)
        let free_inv = la.loop_free_invariant in
        let free_inv' =
          named_predicate
            ~type_safe:false ~global_assertion:false ~relocate:false
            LabelHere LabelPre free_inv
        in
        let inv' = if Options.trust_ai then inv' else O.P.(inv' && free_inv') in
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
                 | Some (pos, loclist) ->
                   let loclist = List.map old_to_pre_loc loclist in
                   match acc with
                   | None -> Some (pos, loclist)
                   | Some (pos, loclist') -> Some (pos, loclist @ loclist')
               else acc)
            None
            (s.fs_default_behavior::s.fs_behavior)
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
        let locs =
          List.fold_left
            (fun acc (names, _inv, ass) ->
               match ass with
                 | Some i ->
                   if in_current_behavior names then
                     match acc with
                     | None -> Some i
                     | Some l -> Some (i @ l)
                   else
                     acc
                 | None -> acc)
            None
            la.loop_behaviors
        in

        let loop_label = fresh_loop_label() in

        let ass =
          loop_assigns
            ~type_safe:false
            (LabelName loop_label)
            infunction.fun_effects
            locs
        in

        let ass_from_fun =
          assigns
            ~type_safe:false
            LabelPre
            infunction.fun_effects
            loop_assigns_from_function
        in

        let inv' = O.P.(inv' && mark_predicate ~e ass && mark_predicate ~e ass_from_fun) in
        (* loop body *)
        let body = expr (Ty Void) e1 in
        let add_assume s =
          let s = O.E.(assumption assume_from_inv assume_from_inv' ^^ s) in
          if Options.trust_ai then O.E.(assumption [free_inv] free_inv' ^^ s)
          else s
        in
        let body = [ add_assume body ] in
        (* loop variant *)
        let loop_variant =
          match la.loop_variant with
            | Some (t,r) when variant_checking () &&
                !Options.termination_policy <> TPnever ->
                let variant =
                  named_term
                    (Ty O.Ty.integer)
                    ~type_safe:false ~global_assertion:false ~relocate:false
                    LabelHere LabelPre t
                in
                Some (variant, Option.map (fun r -> r.li_final_name) r)
            | None when variant_checking () &&
                !Options.termination_policy = TPalways ->
                eprintf
                  "Warning, generating a dummy variant for loop. \
                   Please provide a real variant or set termination policy \
                   to user or never\n%!";
                Some (Const (Int "0"), None)
            | _ -> None
        in
        return @@
        O.E.(
          [loop_label.lab_final_name] @:
          while_
            (mk (Const (Bool true)))
            inv'
            loop_variant
            body)

    | JCEcontract (req, dec, vi_result, behs, e) ->
      let Typ typ = ty e#typ in
      let r =
        match req with
        | Some a ->
          predicate
            ~type_safe:false ~global_assertion:false ~relocate:false
            LabelHere LabelPre a
        | _ -> True
      in
      assert (dec = None);
      let ef = Effect.expr Common.empty_fun_effect e in
      let before = fresh_statement_label () in
      begin match behs with
      | [_pos, id, b] ->
        assert (b.b_throws = None);
        assert (b.b_assumes = None);
        let a =
          predicate
            ~type_safe:false ~global_assertion:false ~relocate:false
            LabelHere (LabelName before) b.b_ensures
        in
        let post =
          O.P.(
            a &&
            assigns
              ~type_safe:false
              (LabelName before)
              ef (* infunction.fun_effects*)
              b.b_assigns)
        in
        let label e = O.E.(@:) [before.lab_final_name] e in
        if safety_checking () then begin
          return @@
          let open O.E in
          let tmp = tmp_var_name () in
          label @@
          let_ tmp
            (mk @@ Triple (true, r, expr typ e, True, []))
            (fun _ ->
               mk (Black_box (Annot (True, O.Wt.void, [], [], post, []))) ^^
               var tmp)
        end else if is_current_behavior id then
            if r = True
            then return @@ label @@ O.E.mk @@ Triple (true, True, expr typ e, post, [])
            else
              return @@
              O.E.(label (mk @@ Black_box (Annot (True, O.Wt.void, [], [], r, []))) ^^
                   mk @@ Triple (true, True, expr typ e, post, []))
        else
          let Why_type result_type = some_var_why_type vi_result in
          return @@
          O.E.(label (mk @@ Black_box (Annot (True, O.Wt.void, [], [], r, []))) ^^
               let tmp = tmp_var_name () in
               let_
                 tmp
                 (mk @@ Triple (true, True, expr typ e, True, []))
                 (fun _ -> mk @@ Black_box (Annot (True, result_type, [], [], post, []))))
        | _ -> assert false
        end
    | JCEthrow (exc, Some e1) ->
      let Expr e1' = some_expr e1 in
      O.E.(mk @@ Raise (Name.exception_ exc, Some e1'))
    | JCEthrow (exc, None) ->
      O.E.(mk @@ Raise (Name.exception_ exc, None))
    | JCEtry (s, catches, _finally) ->
      let Typ typ = ty s#typ in
      let catch (s, excs) (ei, v_opt, st) =
        if ExceptionSet.mem ei excs then
          O.E.(mk @@
               Try (s,
                    Name.exception_ ei,
                    Option.map (fun v -> v.vi_final_name) v_opt,
                    expr typ st),
           ExceptionSet.remove ei excs)
        else
          s, excs
      in
      let ef = Effect.expr empty_fun_effect s in
      return @@ fst @@ List.fold_left catch (expr typ s, ef.fe_raises) catches
    | JCEmatch (_e, _psl) -> assert false
    (*let tmp = tmp_var_name () in
      let body = pattern_list_expr expr (LVar tmp) e#region e#typ psl in
        mk_expr @@ Let (tmp, expr e, body) *)
  in
  (* Ideally, only labels used in logical annotations should be kept *)
  let lab = e#mark in
  (if lab = ""
   then e'
   else O.E.([e#mark] @: e'))
  |>
  Fn.on
    (e#typ = Common.unit_type &&
         match e#original_type with
         | JCTany | JCTnative Tunit -> false
         | _ -> true) @@
  (* Create dummy temporary *)
  fun e' ->
  let tmp = tmp_var_name () in
  return O.E.(let_ tmp e' (fun _ -> void))
and some_expr e =
  let Typ typ = ty e#typ in
  O.E.some @@ expr typ e

(*
(* NOTE: [~shifted] should contain the necessary type safety checks! *)
let make_old_style_update ~e ~at ~tt ~mem ~p ~i ~shifted ~lbound ~rbound ~tag ~typesafe ~v =
  if safety_checking () then
    match lbound, rbound, typesafe with
    | true, true, _ ->
      make_app "safe_upd_" [mem; shifted; v]
    | true, false, false ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref_bounds
        "lsafe_lbound_upd_"
        [at; tt; mem; p; tag; mk_expr (Cte i); v]
    | true, false, true ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref_bounds
        "lsafe_lbound_typesafe_upd_"
        [at; mem; p; mk_expr (Cte i); v]
    | false, true, false ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref_bounds
        "rsafe_rbound_upd_"
        [at; tt; mem; p; tag; mk_expr (Cte i); v]
    | false, true, true ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref_bounds
        "rsafe_rbound_typesafe_upd_"
        [at; mem; p; mk_expr (Cte i); v]
    | false, false, _ ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref
        "upd_"
        [at; mem; shifted; v]
  else
    make_app "safe_upd_" [mem; shifted; v]

let make_old_style_update_no_shift ~e ~at ~mem ~p ~lbound ~rbound ~v =
  if safety_checking () then
    match lbound, rbound with
    | true, true ->
      make_app "safe_upd_" [mem; p; v]
    | true, false ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref_bounds
        "lsafe_lbound_typesafe_upd_"
        [at; mem; p; mk_expr (Cte (Prim_int "0")); v]
    | false, true ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref_bounds
        "rsafe_rbound_typesafe_upd_"
        [at; mem; p; mk_expr (Cte (Prim_int "0")); v]
    | false, false ->
      make_vc_app_e
        ~e
        ~kind:JCVCpointer_deref
        "upd_"
        [at; mem; p; v]
  else
    make_app "safe_upd_" [mem; p; v]

let make_not_assigns mem t l =
  let l = List.map (fun (i, _, _, _) -> i) l in
  let l = List.sort Pervasives.compare l in
  let rec merge l acc =
    match l,acc with
    | [],_ -> acc
    | i :: r, [] -> merge r [(i,i)]
    | i :: r, (a, b) :: acc' ->
      if i = b + 1 then
        merge r ((a, i) :: acc')
      else
        merge r ((i, i) :: acc)
  in
  let i, l =
    match merge l [] with
    | [] -> failwith "make_not_assigns: got empty location list after merge"
    | i :: l -> i, l
  in
  let pset_of_interval (a, b) =
    if a = b then
      LApp ("pset_singleton",
            [LApp("shift", [LVar t; LConst (Prim_int (string_of_int a))])])
    else
      LApp("pset_range",
           [LApp("pset_singleton", [LVar t]);
             LConst(Prim_int (string_of_int a));
             LConst(Prim_int (string_of_int b))])
  in
  let pset =
    List.fold_left
    (fun acc i ->
       LApp("pset_union", [pset_of_interval i; acc]))
    (pset_of_interval i)
    l
  in
  LPred ("not_assigns", [LDerefAtLabel(mem, ""); LDeref mem; pset])
*)

(*****************************)
(* axioms, lemmas, goals     *)
(*****************************)

let axiom pos id ~is_axiom labels a =
  let lab = match labels with [lab] -> lab | _ -> LabelHere in
  (* Special (local) translation of effects for predicates with polymorphic memories.
     We first entirely exclude their effects from the assertion, then only restore the effects that
     are relevant in this axiom. So the effects from other axioms won't be translated. *)
  let ef = Effect.assertion empty_effects (restrict_poly_mems_in_assertion MemoryMap.empty a) in
  let a' =
    predicate ~type_safe:false ~global_assertion:true ~relocate:false lab lab @@
      restrict_poly_mems_in_assertion ef.e_memories a
  in
  let params = li_model_args_3 ~label_in_name:true ef in
  let name = get_unique_name id in
  let a' = List.fold_right (fun (n, _v, Logic_type ty') a' -> O.P.forall n ty' (fun _ -> a')) params a' in
  [O.Wd.mk
     ~name
     ~expl:((if is_axiom then "Axiom " else "Lemma ") ^ id)
     ~pos:(Position.of_pos pos)
     (Goal ((if is_axiom then KAxiom else KLemma), a'))]

let axiomatic_decl d =
  match d with
  | Typing.ABaxiom (loc, id, labels, p) ->
      axiom loc ~is_axiom:true id labels p

let logic_fun f ta =
  let lab = match f.li_labels with [lab] -> lab | _ -> LabelHere in
  let fp = predicate ~type_safe:false ~global_assertion:true ~relocate:false lab lab in
  let ft typ = term typ ~type_safe:false ~global_assertion:true ~relocate:false lab lab in
  let params =
    let lab =
      match f.li_labels with [lab] -> lab | _ -> LabelHere
    in
    let model_params = li_model_args_3 ~label_in_name:true f.li_effects in
    let usual_params = List.map (some_tparam ~label_in_name:true lab) f.li_parameters in
    List.map (fun (n, _v, ty') -> n, ty') @@ usual_params @ model_params
  in
  (* definition of the function *)
  let th = Name.Theory.axiomatic f in
  (* Function definition *)
  match f.li_result_type, ta with
  (* Predicate *)
  | None, JCAssertion a ->
    let body = fp a in
    [O.Wd.mk ~name:f.li_final_name @@ Predicate (params, body)]
  (* Function *)
  | Some ty', JCTerm t ->
    let Typ typ = ty ty' in
    let ty' = type_ typ ty' in
    let t' = ft typ t in
    if List.mem f f.li_calls then
      let logic = O.Wd.mk ~name:f.li_final_name @@ Logic (params, ty') in
      let axiom =
        let trig =
          let params = List.map O.(T.some % T.var % fst) params in
          O.T.((th, f.li_final_name) $.. params)
        in
        O.Wd.mk
          ~name:(f.li_final_name ^ "_definition")
          (Goal (KAxiom,
                 List.fold_right
                   (fun (v, Logic_type lty) acc -> O.P.(forall v lty ~trigs:(fun _ -> [[Term trig]]) @@ Fn.const acc))
                   params
                   O.P.(trig = t')))
      in
      [logic; axiom]
    else
      [O.Wd.mk ~name:f.li_final_name @@ Function (params, ty', t')]
  | ty', (JCNone | JCReads _) -> (* Logic *)
    let Logic_type ty' = Option.map_default ~default:O.Lt.(some bool) ~f:some_logic_type ty' in
    [O.Wd.mk ~name:f.li_final_name @@ Logic (params, ty')]
  | None, JCInductive l ->
    [O.Wd.mk
       ~name:f.li_final_name
       (Inductive
          (params,
           List.map
            (fun (id,_labels,a) ->
              let ef = Effect.assertion empty_effects a in
              let a' = fp a in
              let params = li_model_args_3 ~label_in_name:true ef in
              let a' =
                List.fold_right
                  (fun (n, _v, Logic_type ty') a' -> O.P.forall n ty' (Fn.const a'))
                  params
                  a'
               in
               get_unique_name id#name, a')
            l))]
  | Some _, JCInductive _
  | None, JCTerm _
  | Some _, JCAssertion _ -> assert false

let aximatic name data =
  let open Typing in
  let logics =
    List.map
      (fun li ->
          logic_fun li (snd @@ IntHashtblIter.find logic_functions_table li.li_tag))
      data.axiomatics_defined_ids
  in
  let goals = List.map axiomatic_decl data.axiomatics_decls in
  O.[Entry.some (Th.mk ~name @@ List.flatten @@ logics @ goals)]

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
           (Name.exception_ exc, True) :: acc
       | None -> (Name.exception_ exc, True) :: acc)
    excep_behaviors
    []

let fun_parameters params write_params read_params =
  let write_params = List.map (fun (n, Logic_type ty') -> (n, O.Wt.some @@ Ref (Logic ty'))) write_params in
  let read_params = List.map (fun (n, Logic_type ty') -> (n, O.Wt.some @@ Logic ty')) read_params in
  let params =
    List.map
      (fun v ->
         let n, Logic_type ty' = some_param v in
         n, O.Wt.some @@ Logic ty')
      params
  in
  let params = params @ write_params @ read_params in
  match params with
  | [] -> ["tt", O.Wt.(some void)]
  | _ -> params

let annot_fun_parameters params write_params read_params annot_type =
  let params = fun_parameters params write_params read_params in
  List.fold_right
    (fun (n, Why_type ty') (Why_type acc) -> O.Wt.some @@ Arrow (n, ty', acc))
    params
    annot_type

let function_body _f spec behavior_name body =
  set_current_behavior behavior_name;
  set_current_spec spec;
  let e' = some_expr body in
  reset_current_behavior ();
  reset_current_spec ();
  e'

(* Only used for internal function, hence type-safe parameter set to false *)
let assume_in_precondition b pre =
  match b.b_assumes with
  | None -> pre
  | Some a ->
    let a' =
      predicate ~type_safe:false ~global_assertion:false ~relocate:false
        LabelHere LabelHere a
    in
    O.P.(a' && pre)

(* Only used for external prototype, hence type-safe parameter set to true *)
let assume_in_postcondition b post =
  match b.b_assumes with
  | None -> post
  | Some a ->
    let a' =
      predicate ~type_safe:true ~global_assertion:false ~relocate:true
        LabelOld LabelOld a
    in
    O.P.(impl a' post)

let function_prototypes = Hashtbl.create 7

let map_embedded_fields ~f x =
  match x#typ with
  | JCTpointer (JCtag (st, _), _, _) ->
    List.concat_map
      st.si_fields
      ~f:(function
        | { fi_type = JCTpointer (_, Some l, Some r) as typ } as fi ->
          f ~typ ~l ~r fi
        | _ -> [])
  | _ -> []

let allocates ~internal ~type_safe ?region_list ef =
  function
  | None -> True
  | Some (pos, locs) ->
    let mk_positioned =
      let p = (new assertion ~pos JCAtrue :> < mark : _; pos : _ > ) in
      P.locate ~p ~kind:JCVCallocates
    in
    let tr tables f =
      tables |>
      List.filter ((=) (internal = None) % external_region ?region_list) |>
      List.map f |>
      List.map mk_positioned |>
      O.P.conj
    in
    let alloc_frame =
      let at_locs =
        locs |>
        List.concat_map
          ~f:(fun loc ->
            loc ::
            map_embedded_fields
              loc
              ~f:(fun ~typ ~l:_ ~r:_ fi ->
                [location_with_node ~typ loc @@ JCLderef (location_set_of_location loc, LabelPost, fi, loc#region)]))
        |>
        List.map (fun loc -> Name.alloc_table (lderef_alloc_class ~type_safe loc, loc#region), loc)
      in
      tr (AllocMap.keys ef.fe_writes.e_alloc_tables) @@
      fun (ac, r) ->
      let alloc_same_except ps = O.P.alloc_same_except ac ~r ~old:(internal |? LabelOld) ps in
      match
        List.fold_left (fun acc (a_t', loc) -> if a_t' = Name.alloc_table (ac, r) then loc :: acc else acc) [] at_locs
      with
      | [] -> alloc_same_except (O.T.pset_empty ())
      | locs ->
        let pset =
          pset_union_of_list @@
          List.map
            (fun ls -> O.T.pset_all @@ collect_pset_locations Any ~type_safe ~global_assertion:false LabelPost ls)
            locs
        in
        alloc_same_except pset
    in
    let tag_frame =
      tr (TagMap.keys ef.fe_writes.e_tag_tables) @@
      fun (pc, r) -> O.P.tag_extends ~r ~old:(internal |? LabelOld) pc
    in
    mk_positioned @@ O.P.(alloc_frame && tag_frame)

let prepare_fun f _funpos spec _body acc =
  begin
    match spec.fs_decreases with
      | None -> ()
      | Some(t,r) ->
          Hashtbl.add decreases_clause_table f.fun_tag (t,r)
  end;
  acc

let func f funpos spec body =
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
      []
      f.fun_parameters
  in
  (* global variables valid predicates *)
  let variables_valid_pred_apps = True in
  (* precondition for calling the function and extra one for analyzing it *)
  let external_requires =
    let kind = JCVCpre (if Option.is_some body then "Internal" else "External") in
    P.locate
      ~p:(new assertion JCAtrue :> < mark : _; pos: _ >)
      ~kind @@
      named_predicate ~type_safe:true ~global_assertion:false ~kind:JCVCrequires ~relocate:false
        LabelHere LabelHere spec.fs_requires
  in
  let external_requires =
    if Options.trust_ai then
      external_requires
    else
      let free_requires =
        named_predicate ~type_safe:true ~global_assertion:false ~relocate:false
          LabelHere LabelHere spec.fs_free_requires
      in
      O.P.(external_requires && free_requires)
  in
  let internal_requires =
    named_predicate ~type_safe:false ~global_assertion:false ~relocate:false
      LabelHere LabelHere spec.fs_requires
  in
  let free_requires =
    named_predicate ~type_safe:false ~global_assertion:false ~relocate:false
      LabelHere LabelHere spec.fs_free_requires
  in
  let free_requires = O.P.(variables_valid_pred_apps && free_requires) in
  let internal_requires = O.P.(internal_requires && free_requires) in
  let internal_requires =
    List.fold_left
      (fun acc (_, vi) ->
         let argument_req =
           let all_effects = ef_union f.fun_effects.fe_reads f.fun_effects.fe_writes in
           O.P.(Interp_struct.valid_pre ~in_param:true all_effects vi && Interp_struct.instanceof_pre all_effects vi)
         in
         O.P.(argument_req && acc))
      internal_requires
      f.fun_parameters
  in
  (* partition behaviors as follows:
     - (optional) 'safety' behavior (if Arguments Invariant Policy is selected)
     - (optional) 'inferred' behaviors (computed by analysis)
     - user defined behaviors *)
  let behaviors = spec.fs_default_behavior :: spec.fs_behavior in
  let (safety_behavior,
       normal_behaviors_inferred,
       normal_behaviors,
       excep_behaviors_inferred,
       excep_behaviors) =
    List.fold_left
      (fun (safety, normal_inferred, normal, excep_inferred, excep) (_pos, id, b) ->
         let make_post ~type_safe ~internal =
           (if internal && Options.trust_ai then
               b.b_ensures
            else
              Assertion.mkand
                [b.b_ensures;
                 b.b_free_ensures]
                ())
           |>
           named_predicate ~type_safe ~global_assertion:false ~kind:JCVCensures ~relocate:false LabelPost LabelOld |>
           O.P.(&&) @@
             assigns
               ~type_safe
               ~region_list:f.fun_param_regions
               LabelOld
               f.fun_effects
               b.b_assigns
           |>
           (* Add alloc_extends[except] predicates for those alloc tables modified by the function, i.e. *)
           (* listed in the f.fun_effects.fe_writes. *)
           (* We except psets of locations specified in the allocates clause i.e. b.b_allocates. *)
           (* IMPORTANT: We should add the predicates BOTH to the external and internal postconditions, *)
           (* otherwise safety might be violated. *)
           O.P.(&&) @@
             allocates
               ~internal:None
               ~type_safe
               ~region_list:f.fun_param_regions
               f.fun_effects
               b.b_allocates
           |>
           O.P.(&&) @@
             if not internal && id = "safety" then
               let all_effects = ef_union f.fun_effects.fe_reads f.fun_effects.fe_writes in
               O.P.(Interp_struct.valid_pre ~in_param:true all_effects f.fun_result &&
                    Interp_struct.instanceof_pre all_effects f.fun_result)
             else
               True
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
               O.P.(variables_valid_pred_apps && internal_post)
             in
             let external_post =
               O.P.(variables_valid_pred_apps && external_post)
             in
             (id, b, internal_post, external_post) :: safety,
             normal_inferred, normal, excep_inferred, excep
           | "inferred" ->
             assert (b.b_assumes = None);
             safety, behav :: normal_inferred,
             (if Options.trust_ai then normal else behav :: normal),
             excep_inferred, excep
           | _ ->
             safety, normal_inferred, behav :: normal,
             excep_inferred, excep
           end
         | Some exc ->
           if id = "inferred" then begin
             assert (b.b_assumes = None);
             safety, normal_inferred, normal,
             ExceptionMap.add_merge
               List.append exc [behav] excep_inferred,
             if Options.trust_ai then excep else
               ExceptionMap.add_merge List.append exc [behav] excep
           end else
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
             exc [exc.exi_name ^ "_b", b, True, True] acc)
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
    O.P.(f b post && acc)
  in
  let add_postcondition ~internal =
    add_modif_postcondition ~internal (fun _b post -> post)
  in
  let internal_safety_post =
    List.fold_right (add_postcondition ~internal:true) safety_behavior True
  in
  let external_safety_post =
    List.fold_right (add_postcondition ~internal:false) safety_behavior True
  in
  let normal_post =
    List.fold_right
      (add_modif_postcondition ~internal:false assume_in_postcondition)
      normal_behaviors True
  in
  let normal_post_inferred =
    List.fold_right (add_postcondition ~internal:false)
      normal_behaviors_inferred True
  in
  let excep_posts =
    ExceptionMap.fold
      (fun exc bl acc ->
         let a' =
           List.fold_right (add_postcondition ~internal:false) bl True
         in
         (Name.exception_ exc, a') :: acc)
      excep_behaviors
      []
  in
  let excep_posts_inferred =
    ExceptionMap.fold
      (fun exc bl acc ->
         let a' =
           List.fold_right
             (add_modif_postcondition ~internal:false assume_in_postcondition)
             bl
             True
         in
         (Name.exception_ exc, a') :: acc)
      excep_behaviors_inferred
      []
  in

  (* Function type *)
  let Typ ret_typ = ty f.fun_result.vi_type in
  let ret_type = why_type ret_typ f.fun_result.vi_type in
  let fparams = List.map snd f.fun_parameters in
  let param_normal_post =
    if is_purely_exceptional_fun spec then False
    else O.P.conj [external_safety_post; normal_post; normal_post_inferred]
  in
  let param_excep_posts = excep_posts @ excep_posts_inferred in
  let annot_type = (* function declaration with precondition *)
    O.Wt.some @@
    Annot (
      external_requires,
      ret_type,
      external_read_effects,
      external_write_effects,
       param_normal_post,
      param_excep_posts)
   in
   let Why_type fun_type =
     annot_fun_parameters fparams
       external_write_params external_read_params annot_type
   in
   let external_unsafe =
     let name = f.fun_final_name in
     Hashtbl.add function_prototypes name (O.Wt.some fun_type);
     O.Entry.some @@
     O.Mod.mk
       ~name:(Name.Module.func ~extern:true ~safe:false f)
       ~safe:false
       [O.Wd.mk ~name @@ Param fun_type]
   in
   let annot_type =
     O.Wt.some @@
     Annot (True, ret_type,
            external_read_effects, external_write_effects,
            param_normal_post, param_excep_posts)
   in
   let Why_type fun_type =
     annot_fun_parameters fparams
       external_write_params external_read_params annot_type
   in
   let external_safe =
     let name = f.fun_final_name in
     Hashtbl.add function_prototypes name (O.Wt.some fun_type);
     O.Entry.some @@
     O.Mod.mk
       ~name:(Name.Module.func ~extern:true ~safe:true f)
       ~safe:false
       [O.Wd.mk ~name @@ Param fun_type]
   in
  (* restore assigned status for parameters assigned in the body *)
  List.iter (fun v -> v.vi_assigned <- true) assigned_params;
  (* Function body *)
  let behaviors =
    Option.map_default
      body
      ~default:[]
      ~f:(fun body ->
        if Options.verify = [] || List.mem f.fun_name Options.verify then
          (* parameters *)
          let params = fun_parameters fparams internal_write_params internal_read_params in
          let wrap_body f spec bname body =
            (* rename formals after parameters are computed and before body is treated *)
            let list_of_refs =
              List.fold_right
                (fun id ->
                   Fn.on id.vi_assigned @@
                   fun bl ->
                   let n = id.vi_final_name in
                   let newn = "mutable_" ^ n in
                   id.vi_final_name <- newn;
                   (newn, n) :: bl)
                fparams
                []
            in
            body |>
            function_body f spec bname |>
            (let assert_internal_allocates =
               Fn.on'
                 (bname = "default") @@
               fun () ->
               let allocates =
                 allocates
                   ~internal:(Some LabelPre)
                   ~type_safe:true
                   ~region_list:f.fun_param_regions
                   f.fun_effects
                   (Triple.trd spec.fs_default_behavior).b_allocates
               in
               Fn.on
                 (O.P.is_not_true allocates)
                 O.E.((^^) @@ mk @@ Assert (`ASSERT, allocates))
             in
             fun (Expr body) ->
               (match f.fun_result.vi_type with
                | JCTnative Tunit ->
                  O.E.(return ret_typ @@ mk @@
                       Try (O.E.check (Ty Void) body ^^ mk (Raise (jessie_return_exception, None)),
                            jessie_return_exception,
                            None,
                            assert_internal_allocates void))
                | _ ->
                  let result = f.fun_result in
                  let Typ typ = ty result.vi_type in
                  let e' = nondet_value typ result.vi_type in
                  O.E.(return ret_typ @@ mk @@
                       Let_ref (jessie_return_variable, e',
                                mk @@
                                Try (O.E.check (Ty Void) body ^^ (mk Absurd),
                                     jessie_return_exception,
                                     None,
                                     assert_internal_allocates @@ mk @@ Deref jessie_return_variable))))
               |>
               define_locals |>
               O.E.(@:) ["init"] |>
               List.fold_right
                 (fun (mut_id, id) e' ->
                 O.E.mk (Let_ref (mut_id, plain_var id, e')))
              list_of_refs
            |>
            (* FS#393: restore parameter real names *)
            Fn.tap
              (Fn.const @@
               List.iter
                 (fun v ->
                    let n = v.vi_final_name in
                    if List.mem_assoc n list_of_refs then
                      v.vi_final_name <- List.assoc n list_of_refs)
                 fparams))
          in
          (* safety behavior *)
          (if (Options.verify_behavior "safety" || Options.verify_behavior "variant") &&
              not (is_purely_exceptional_fun spec) && not Options.verify_invariants_only
           then
             let name = f.fun_final_name in
             let behav =
               if Options.verify_behavior "safety" then "safety"
               else "variant"
             in
             let safety_body = wrap_body f spec behav body in
             [O.Entry.some @@
              O.Mod.mk
                ~name:(Name.Module.func ~safe:false ~extern:false f)
                ~safe:false
                [O.Wd.mk
                   ~name
                   ~expl:("Function " ^ f.fun_name ^ ", safety")
                   ~pos:(Position.of_pos funpos)
                   (Def
                      (O.E.mk @@ Fun (
                         params,
                         ret_type,
                         internal_requires,
                         safety_body,
                         P.locate
                           ~p:(new assertion JCAtrue :> < mark : _; pos: _ >)
                           ~kind:JCVCpost
                           internal_safety_post,
                         false (* we require termination proofs, also Why3 now checks possible divergence *),
                         excep_posts_for_others None excep_behaviors)))]]
           else
             [])
          @
          [O.Entry.some @@
           O.Mod.mk
             ~name:(Name.Module.func ~safe:true ~extern:false f)
             ~safe:true
             (List.fold_right
                (fun (id, b, internal_post, _) ->
                   Fn.on'
                     (Options.verify_behavior id) @@
                   fun () ->
                   let normal_body = wrap_body f spec id body in
                   let name = f.fun_name ^ "_ensures_" ^ id in
                   let beh =
                     if id = "default"
                     then "default behavior"
                     else "behavior " ^ id
                   in
                   List.cons
                     (O.Wd.mk
                        ~name
                        ~expl:("Function " ^ f.fun_name ^ ", " ^ beh)
                        ~pos:(Position.of_pos funpos)
                        (Def
                           (O.E.mk @@ Fun (
                              params,
                              ret_type,
                              assume_in_precondition b internal_requires,
                              normal_body,
                              P.locate
                                ~p:(new assertion JCAtrue :> < mark : _; pos: _ >)
                                ~kind:JCVCpost
                                internal_post,
                              f.fun_may_diverge, (* Adding `diverges' clause for recursive and looping functions *)
                              excep_posts_for_others None excep_behaviors)))))
                normal_behaviors
                []
              @
              ExceptionMap.fold
                (fun exc ->
                   List.fold_right
                     (fun (id, b, internal_post, _) ->
                        Fn.on'
                          (Options.verify_behavior id) @@
                        fun () ->
                        let except_body = wrap_body f spec id body in
                        let name = f.fun_name ^ "_exsures_" ^ id in
                        List.cons
                          (O.Wd.mk
                             ~name
                             ~expl:("Function " ^ f.fun_name ^ ", behavior " ^ id)
                             ~pos:(Position.of_pos funpos)
                             (Def
                                (O.E.mk @@ Fun (
                                   params,
                                   ret_type,
                                   assume_in_precondition b internal_requires,
                                   except_body,
                                   True,
                                   false,
                                   (Name.exception_ exc, internal_post) ::
                                   excep_posts_for_others (Some exc) excep_behaviors))))))
                user_excep_behaviors
                [])]
        else
          [])
  in
  external_safe :: external_unsafe :: behaviors


let func f funpos spec body =
  set_current_function f;
  let r = func f funpos spec body in
  reset_current_function ();
  r

(******************************************************************************)
(*                               Logic entities                               *)
(******************************************************************************)

let logic_type (name, l) = O.Wd.mk ~name @@ Type (List.map Type_var.name l)

let enum_entry_name ~how (type a) =
  function
  | (Int _ as i : a bounded integer) ->
    let (module M) = O.module_of_int_ty i in
    begin match how with
    | `Theory false -> M.theory
    | `Theory true -> M.bit_theory
    | `Module (false, false) -> M.unsafe_module
    | `Module (false, true) -> M.unsafe_bit_module
    | `Module (true, false) -> M.safe_module
    | `Module (true, true) -> M.safe_bit_module
    end
  | Enum _ as e ->
    let (module M) = O.module_of_enum_ty e in
    match how  with
    | `Theory _ -> M.theory
    | `Module (false, _) -> M.unsafe_module
    | `Module (true, _) -> M.safe_module

let enums eis =
  let open O in
  let generic_enum = Mod.dummy "Generic_enum" in
  let safe_enum = Mod.dummy "Safe_enum" in
  let unsafe_enum = Mod.dummy "Unsafe_enum" in
  let safe_enum_ext = Mod.dummy "Safe_enum_ext" in
  let unsafe_enum_ext = Mod.dummy "Unsafe_enum_ext" in
  let open O in
  let here = [`Namespace (None, None)] in
  let mod_ ~th ~safe ty =
    Entry.some @@
    Mod.mk
      ~name:(enum_entry_name ~how:(`Module (safe, false)) ty)
      ~safe
      ~deps:[Dependency (Use (`Import None, th));
             Dependency (Clone (`Export, generic_enum, here));
             Dependency (Clone (`Export, (if safe then safe_enum else unsafe_enum), here));
             Dependency (Clone (`Export, (if safe then safe_enum_ext else unsafe_enum_ext), here))]
      []
  in
  let enum = Th.dummy "Enum" in
  let safe_bit_enum = Mod.dummy "Safe_bit_enum" in
  let unsafe_bit_enum = Mod.dummy "Unsafe_bit_enum" in
  Entry.some enum ::
  List.map
    Entry.some
    [generic_enum; safe_enum; unsafe_enum; safe_enum_ext; unsafe_enum_ext; safe_bit_enum; unsafe_bit_enum] @
  List.flatten @@
  ListLabels.map
    eis
    ~f:(function
      | { ei_type = Int (r, b) } ->
        let i : _ integer = Int (r, b) in
        let th = Th.dummy (enum_entry_name ~how:(`Theory false) i) in
        let bw_th = Th.dummy (enum_entry_name ~how:(`Theory true) i) in
        let bw_mod ~safe =
          Entry.some
            (Mod.mk
               ~name:(enum_entry_name ~how:(`Module (safe, true)) i)
               ~safe
               ~deps:[Dependency (Use (`Import None, th));
                      Dependency (Clone (`Export, (if safe then safe_enum else unsafe_enum), here));
                      Dependency (Clone (`Export, (if safe then safe_bit_enum else unsafe_bit_enum), here))]
               [])
        in
        Entry.[some th;
               some bw_th;
               mod_ ~th ~safe:false i;
               mod_ ~th ~safe:true i;
               bw_mod ~safe:false;
               bw_mod ~safe:true]
      | { ei_type = Enum e; ei_min; ei_max } ->
        let e = Enum e in
        let min = "min" and max = "max" in
        let enum_aux =
          Th.mk
            ~name:(enum_entry_name ~how:(`Theory false) e ^ "_aux")
            [Wd.mk ~name:min @@ Function ([], Lt.integer, T.num ei_min);
             Wd.mk ~name:max @@ Function ([], Lt.integer, T.num ei_max)]
        in
        let th =
          Th.mk
            ~name:(enum_entry_name ~how:(`Theory false) e)
            ~deps:[Use (`Import None, enum_aux);
                   Clone (`Export, enum, [`Constant (min, min); `Constant (max, max)])]
            []
        in
        Entry.[some enum_aux; some th; mod_ ~th ~safe:false e; mod_ ~th ~safe:true e])

let enum_cast (ei_to, ei_from) =
  let return ~bw ~from ~to_ =
    let open O in
    let name ~of_ = enum_entry_name ~how:of_ to_ ^ "_of_" ^ enum_entry_name ~how:of_ from in
    let n = "n" in
    let lt_from = Lt.int from in
    let lt_to = Lt.int to_ in
    let to_int t = T.(To_int from $. t) in
    let cast_name m = "cast" ^ if m then "_modulo" else "" in
    let cast ~m =
      Wd.mk
        ~name:(cast_name m)
        (Function ([n, Logic_type lt_from], lt_to, T.(Of_int (to_, m) $. to_int @@ T.var n)))
    in
    let bw_cast = "bw_cast" in
    let bw_cast_def =
      [Wd.mk
         ~name:bw_cast
         (Logic ([n, Logic_type lt_from], lt_to));
       Wd.mk
         ~name:"Bw_cast_eq"
         (let cast = T.cast ~modulo:true ~from ~to_ in
          let bw_cast = T.($.) (F.local bw_cast) in
          Goal (KAxiom,
                P.(forall n lt_from ~trigs:(fun n -> [[Term (cast n)]; [Term (bw_cast n)]])
                  (fun n -> cast n = bw_cast n))))]
    in
    let cast_val ~safe ~bw ~m =
      let n_t = T.var n in
      let from = enum_entry_name ~how:(`Theory bw) to_, true in
      Wd.mk
        ~name:(cast_name m)
        (Param (Arrow
                  (n, Logic lt_from,
                   (Annot
                      ((if safe && not m && (ei_to.ei_min > ei_from.ei_min || ei_to.ei_max < ei_from.ei_max)
                        then P.(F.user ~from "in_bounds" $. n_t)
                        else True),
                       Logic lt_to,
                       [],
                       [],
                       P.(T.(To_int to_ $. T.result =
                             let n_i = to_int n_t in if m then F.user ~from "normalize" $. n_i else n_i) &&
                          if bw then T.(result = (F.user ~from:(name ~of_:(`Theory true), true) bw_cast $. n_t))
                          else True),
                       [])))))
    in
    let mods ~bw =
      [Entry.some @@
       Mod.mk
         ~name:(name ~of_:(`Module (false, false)))
         ~safe:false
         [cast_val ~safe:false ~bw ~m:false; cast_val ~safe:false ~bw ~m:true];
       Entry.some @@
       Mod.mk
         ~name:(name ~of_:(`Module (true, false)))
         ~safe:true
         [cast_val ~safe:true ~bw ~m:false; cast_val ~safe:true ~bw ~m:false]]
    in
    Entry.some
      (Th.mk
         ~name:(name ~of_:(`Theory false))
         [cast ~m:false; cast ~m:true]) ::
    mods false @
    if bw then
      Entry.some
        (Th.mk
           ~name:(name ~of_:(`Theory true))
           ([cast ~m:false; cast ~m:true] @ bw_cast_def)) ::
      mods true
    else
      []
  in
  match ei_to.ei_type, ei_from.ei_type with
  | Int (r1, b1), Int (r2, b2) -> return ~from:(Int (r2, b2)) ~to_:(Int (r1, b1)) ~bw:true
  | Int (r1, b1), Enum e2 -> return ~from:(Enum e2) ~to_:(Int (r1, b1)) ~bw:false
  | Enum e1, Int (r2, b2) -> return ~from:(Int (r2, b2)) ~to_:(Enum e1) ~bw:false
  | Enum e1, Enum e2 -> return ~from:(Enum e2) ~to_:(Enum e1) ~bw:false

let exception_ ei =
  let return typ_opt =
    O.Wd.mk ~name:(Name.exception_ ei) @@ Exception typ_opt
  in
  match ei.exi_type with
  | Some tei -> let Logic_type t = some_logic_type tei in return (Some t)
  | None -> return None

let variable vi =
  let Why_type wt = some_var_why_type vi in
  let return wt = O.Wd.mk ~name:vi.vi_final_name @@ Param wt in
  if vi.vi_assigned then return (Ref wt) else return wt

let memory (mc, r) =
  O.Wd.mk ~name:(memory_name (mc, r)) @@ Param (Ref (Logic (memory_type mc)))

let alloc_table (pc, r) =
  O.Wd.mk ~name:(Name.alloc_table (pc, r)) @@ Param (Ref (Logic (alloc_table_type pc)))

let tag_table (rt, r) =
  O.Wd.mk ~name:(Name.tag_table (rt, r)) @@ Param (Ref (Logic (tag_table_type rt)))

include Interp_struct

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_interp.ml"
  End:
*)

