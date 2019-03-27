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
(*  AstraVer fork:                                                         *)
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

open Format

open Stdlib
open Envset

open Output_ast
module O = Output

let constant fmttr (type a) =
  let pr fmt = fprintf fmttr fmt in
  function
  | (Void : a constant) -> pr "()"
  | Int n ->
    let n = Numconst.integer n in
    let open Num in
    pr (if n >=/ Numconst.zero then "(%s)" else "(Int.(-_) %s)") @@ string_of_num @@ abs_num n
  | Real f -> pr "%s" f
  | Bool true -> pr "true"
  | Bool false -> pr "false"

let id fmttr id =
  fprintf fmttr "%s" @@
  match id.[0] with
  | 'A' .. 'Z' -> "_" ^ id
  | _ when Why3_kw.is_why3_keyword id -> id ^ "_why3"
  | _ -> id

let uid fmttr uid =
  if uid <> "" then
    fprintf fmttr "%s" @@
    match uid.[0] with
    | 'A' .. 'Z' -> uid
    | 'a' .. 'z' -> String.capitalize uid
    | _ -> "U_" ^ uid

let qid ~entry ~u fmttr =
  let id = if u then uid else id in
  function
  | (where, `Qualified), name when where <> entry -> fprintf fmttr "%a.%a" uid where id name
  | _, name -> fprintf fmttr "%a" id name

let int_ty ~how fmttr (type r) (type b) (ty : (r repr, b bit) xintx bounded integer) =
  let (module Int_ty) = O.module_of_int_ty ty in
  fprintf fmttr "%s" @@
  match how with
  | `Name -> Int_ty.name
  | `Theory `Abstract -> Int_ty.theory
  | `Theory `Bitvector -> Int_ty.bit_theory
  | `Module (`Abstract, `Unsafe) -> Int_ty.unsafe_module
  | `Module (`Abstract, `Safe) -> Int_ty.safe_module
  | `Module (`Bitvector, `Unsafe) -> Int_ty.unsafe_bit_module
  | `Module (`Bitvector, `Safe) -> Int_ty.safe_bit_module

let enum_ty ~how fmttr (type e) (Enum _ as ty : e enum bounded integer) =
  let (module Enum_ty) = O.module_of_enum_ty ty in
  fprintf fmttr "%s" @@
  match how with
  | `Name -> Enum_ty.name
  | `Theory -> Enum_ty.theory
  | `Module `Unsafe -> Enum_ty.unsafe_module
  | `Module `Safe -> Enum_ty.safe_module

let modulo fmttr =
  fprintf fmttr "%s" %
  function
  | `Modulo -> "%"
  | `Check -> ""

let modulo' fmttr =
  fprintf fmttr "%s" %
  function
  | `Modulo -> "_modulo"
  | `Check -> ""

let op fmttr =
  fprintf fmttr "%s" %
  function
  | `Add -> "(+"
  | `Sub -> "(-"
  | `Mul -> "( *"
  | `Div -> "(/"
  | `Mod -> "(%"
  | `Neg -> "(-_"
  | `And -> "(&"
  | `Or -> "(|^"
  | `Xor -> "(^"
  | `Lsl -> "lsl"
  | `Lsr -> "lsr"
  | `Asr -> "asr"
  | `Compl -> "(~_"
  | `Lt -> "(<"
  | `Le -> "(<="
  | `Gt -> "(>"
  | `Ge -> "(>="
  | `Eq -> "(="
  | `Ne -> "(<>"
  | `Neq -> "(<>"
  | `Min -> "min"
  | `Max -> "max"
  | `Abs -> "abs"

let rpar fmttr =
  fprintf fmttr "%s" %
  function
  | `Lsl | `Lsr | `Asr | `Min | `Max | `Abs -> ""
  | `Add | `Sub | `Mul | `Div | `Mod
  | `Neg | `And | `Or | `Xor | `Compl
  | `Lt | `Le | `Gt | `Ge
  | `Eq | `Ne | `Neq -> ")"

type any_integer = Int : ('r repr, 'b bit) xintx bounded integer -> any_integer

module S =
  Set.Make
    (struct
      type t = any_integer
      let compare = compare
    end)

let fail_on_real () =
  failwith "floating point operations are not yet supported in GADT encoding, \
            please use the User generic constructor"

let func ~entry ~where ~bw_ints fmttr (type a) (type b) : (a, b) func -> _ =
  let qid = qid ~entry ~u:false in
  let pr fmt = fprintf fmttr fmt in
  let pr_bop fp ty op' fmodulo modulo = pr "%a.%a%a%a" fp ty op op' fmodulo modulo rpar op' in
  let pr_uop fp ty op' fmodulo modulo = pr "%a.%a%a)" fp ty op op' fmodulo modulo in
  let pr_f fp ty = pr "%a.%s" fp ty in
  let pr_f' fp ty = pr "%a.%s%a" fp ty in
  let int_ty ?(default=true) ?ty' fmttr ty =
    int_ty
      ~how:
        (let bit b = if b then `Bitvector else `Abstract in
         match where,
               S.mem (Int ty) bw_ints && Option.map_default ~default ~f:(fun ty -> S.mem (Int ty) bw_ints) ty'
         with
         | `Logic, b -> `Theory (bit b)
         | `Behavior safe, b -> `Module (bit b, safe))
      fmttr
      ty
  in
  let enum_ty fmttr ty =
    enum_ty
      ~how:
        (match where with
         | `Logic -> `Theory
         | `Behavior safe -> `Module safe)
      fmttr
      ty
  in
  let conv_tys : type a b. _ -> a bounded integer * b bounded integer -> _ = fun fmttr (ty_to, ty_from) ->
    let pr f1 ty1 f2 ty2 = fprintf fmttr "%a_of_%a" f1 ty1 f2 ty2 in
    match ty_to, ty_from with
    | Int _, Int _ -> pr (int_ty ~ty':ty_from) ty_to (int_ty ~ty':ty_to) ty_from
    | Int _, Enum _ -> pr (int_ty ~default:false) ty_to enum_ty ty_from
    | Enum _, Int _ -> pr enum_ty ty_to (int_ty ~default:false) ty_from
    | Enum _, Enum _ -> pr enum_ty ty_to enum_ty ty_from
  in
  function
  | B_int_op (`Add | `Sub | `Mul as op') -> pr "Int.%a)" op op'
  | B_int_op (`Div | `Mod as op') -> pr "ComputerDivision.%s" (match op' with `Div -> "div" | `Mod -> "mod")
  | B_int_op (`Min | `Max as op') -> pr "MinMax.%s" (match op' with `Min -> "min" | `Max -> "max")
  | U_int_op `Neg -> pr "Int.%a)" op `Neg
  | U_int_op `Abs -> pr "Abs.abs"
  | B_bint_op (op, (Int _ as ty), modulo') ->
    pr_bop int_ty ty op modulo modulo'
  | B_bint_op (op, (Enum _ as ty), modulo') ->
    pr_bop enum_ty ty op modulo modulo'
  | U_bint_op (op, (Int _ as ty), modulo') ->
    pr_uop int_ty ty op modulo modulo'
  | U_bint_op (op, (Enum _ as ty), modulo') ->
    pr_uop enum_ty ty op modulo modulo'
  | Of_int (Int _ as ty, modulo) -> pr_f' int_ty ty "of_int" modulo' modulo
  | Of_int (Enum _ as ty, modulo) -> pr_f' enum_ty ty "of_int" modulo' modulo
  | To_int (Int _ as ty) -> pr_f int_ty ty "to_int"
  | To_int (Enum _ as ty) -> pr_f enum_ty ty "to_int"
  | Any (Int _ as ty) -> pr_f int_ty ty "any_"
  | Any (Enum _ as ty) -> pr_f enum_ty ty "any_"
  | Cast (ty_to, ty_from, modulo) -> pr_f' conv_tys (ty_to, ty_from) "cast" modulo' modulo
  | B_bint_bop (op, ty) -> pr_bop int_ty ty op modulo `Check
  | U_bint_bop (op, ty) -> pr_uop int_ty ty op modulo `Check
  | Lsl_bint (ty, modulo) -> pr_bop int_ty ty `Lsl modulo' modulo
  | B_num_pred (pred, Integral Integer) -> pr "%a)" op pred
  | B_num_pred (pred, Integral (Int _ as ty)) -> pr_bop int_ty ty pred modulo `Check
  | B_num_pred (pred, Integral (Enum _ as ty)) -> pr_bop enum_ty ty pred modulo `Check
  | Poly op' -> pr "%a)" op op'
  | User (where, name) -> pr "%a" qid (where, name)
  | To_float _ -> fail_on_real ()
  | Of_float _  -> fail_on_real ()
  | B_num_pred (_, Real _) -> fail_on_real ()

let vc_kind fmttr k =
  fprintf fmttr "%s"
    (match k with
     | JCVCvar_decr -> "Variant decreases"
     | JCVCdiv_by_zero -> "Division by zero"
     | JCVCalloc_size -> "Allocation size"
     | JCVCenum_cast -> "Integer cast"
     | JCVCuser_call n -> "Precondition for " ^ n
     | JCVCpointer_deref -> "Pointer dereference"
     | JCVCpointer_deref_bounds -> "Bounded pointer dereference"
     | JCVCpointer_shift -> "Pointer shift"
     | JCVCseparation -> "Separation assertion"
     | JCVCindex_bounds -> "Pointer index bounds"
     | JCVCarith_overflow -> "Arithmetic overflow"
     | JCVCfp_overflow -> "Floating-point overflow"
     | JCVCpre c -> c
     | JCVCassigns -> "Assigns clause"
     | JCVCallocates -> "Allocates clause"
     | JCVCensures -> "Ensures clause"
     | JCVCassertion pos ->
       begin match Position.line pos with
       | Some l -> Printf.sprintf "Assertion in line %d" l
       | None -> Printf.sprintf "Assertion"
       end
     | JCVCcheck "" -> "Check"
     | JCVCcheck s -> String.capitalize s ^ " check"
     | JCVCpost -> "Postcondition"
     | JCVCglobal_invariant s -> "Global invariant " ^ s
     | JCVCrequires -> "Requires clause")

let jc_position fmttr pos =
  let f, l, b, e as loc = Position.to_loc pos in
  if loc <> Why_loc.dummy_floc then
    fprintf fmttr "#\"%s\" %d %d %d#" f l b e

let why_label fmttr { l_kind; l_behavior; l_pos } =
  let pr fmt = fprintf fmttr fmt in
  let with_behavior =
    match l_behavior with
    | "default" | "" -> ignore
    | b -> fun f -> f b
  in
  jc_position fmttr l_pos;
  if not (Position.is_dummy l_pos) then pr "@ ";
  begin match l_kind with
  | Some vc_kind' ->
    pr "\"expl:%a" vc_kind vc_kind';
    with_behavior @@ pr ", behavior %s";
    pr "\"@ ";
  | None ->
    with_behavior @@ (fun b -> pr "\"for behavior %s\"@ " b)
  end

let tconstr ~entry fmttr (type a) (type b) : (a, b) tconstr -> _ =
  let qid = qid ~entry ~u:false in
  let pr fmt = fprintf fmttr fmt in
  function
  | Numeric (Integral Integer) -> pr "int"
  | Numeric (Integral (Int _  as ty)) -> pr "%a.t" (int_ty ~how:(`Theory `Abstract)) ty
  | Numeric (Integral (Enum _  as ty)) -> pr "%a.t" (enum_ty ~how:`Theory) ty
  | Numeric (Real _) -> fail_on_real ()
  | Bool -> pr "Bool.bool"
  | Void -> pr "unit"
  | Var v -> pr "'%a" id v
  | User (where, name) -> pr "%a" qid (where, name)

let rec ltype_hlist : type a. entry:_ -> _ -> a ltype_hlist -> _  = fun ~entry fmttr ->
  function
  | Nil -> ()
  | Cons (lt, ts) ->
    fprintf fmttr "@ %a" (logic_type ~entry) lt;
    ltype_hlist ~entry fmttr ts

and logic_type : type a. entry:_ -> _ -> a logic_type -> _ = fun ~entry fmttr ->
  function
  | Type (c, Nil) ->
    fprintf fmttr "%a" (tconstr ~entry) c
  | Type (c, tps) ->
    fprintf fmttr "(%a%a)" (tconstr ~entry) c (ltype_hlist ~entry) tps

let split c s =
  try
    let pos = String.rindex s c in
    String.(sub s 0 pos, sub s (pos + 1) @@ length s - pos - 1)
  with
  | Not_found -> "", s

let of_int_const ~entry ~where ~bw_ints =
  let func fmttr = func ~entry ~where ~bw_ints fmttr in
  fun fmttr
    (type r) (type b)
    ((Int _ as ty, modulo), Int s : ((r, b) xintx bounded integer * _) * unbounded integer number constant) ->
    let pr fmt = fprintf fmttr fmt in
    let s' = Numconst.integer s in
    let f =
      let open Buffer in
      let buf = create 10 in
      let buf_formatter = formatter_of_buffer buf in
      let f = Of_int (ty, modulo) in
      fun ~subst fmttr ->
        if not subst then
          fprintf fmttr "%a" func f
        else begin
          fprintf buf_formatter "%a%!" func f;
          let scope, _ = split '.' @@ contents buf in
          clear buf;
          fprintf fmttr "%s.%s" scope "of_int_const"
        end
    in
    let open Num in
    let fallback () = pr "(%t@ (%s))" (f ~subst:false) (string_of_num s') in
    if not (S.mem (Int ty) bw_ints) then
      fallback ()
    else
      let min, max =
        let (module M) = O.module_of_int_ty ty in
        try
          let ei = Common.StringHashtblIter.find Typing.enum_types_table M.name in
          Env.(ei.ei_min, ei.ei_max)
        with
        | Not_found -> assert false
      in
      if min <=/ s' && s' <=/ max then
        if s' >=/ Int 0 then
          pr "(%t@ %s)" (f ~subst:true) (string_of_num s')
        else
          pr "(Int.(-_)@ (%t@ %s))" (f ~subst:true) (string_of_num (minus_num s'))
      else
        fallback ()

let rec term_hlist : type a. entry:_ -> bw_ints:_ -> consts:_ -> _ -> a term_hlist -> _ =
  fun ~entry ~bw_ints ~consts fmttr ->
  function
  | Nil -> ()
  | Cons (t, ts) ->
    fprintf fmttr "@ %a" (term ~entry ~bw_ints ~consts) t;
    term_hlist ~entry ~bw_ints ~consts fmttr ts

and term : type a. entry:_ -> bw_ints: _ -> consts:_ -> _ -> a term -> _ = fun ~entry ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let term_hlist fmttr = term_hlist ~entry ~bw_ints ~consts fmttr
  and term fmttr = term ~entry ~bw_ints ~consts fmttr
  and func fmttr = func ~entry ~where:`Logic ~bw_ints fmttr
  in
  function
  | Const c -> constant fmttr c
  | App (Of_int (Int _ as ty, modulo), Cons (Const c, Nil)) ->
    pr "%a" (of_int_const ~entry ~where:`Logic ~bw_ints) ((ty, modulo), c)
  | App (f, Nil) -> pr "%a" func f
  | App (f, (Cons _ as ts)) ->
    pr "@[(%a%a)@]" func f term_hlist ts
  | Var v -> pr "%a" id v
  | Deref v | Deref_at (v, _) when StringSet.mem v consts ->
    pr "%a" id v
  | Deref v -> pr "!%a" id v
  | Deref_at (v, "") -> pr "(old@ !%a)" id v
  | Deref_at (v, l) -> pr "(at@ !%a@ '%a)" id v uid l
  | Typed (t, _) -> term fmttr t
  | Poly { term = t } -> term fmttr t
  | Labeled (l, t) ->
    pr "(%a%a)" why_label l term t
  | If (t1, t2, t3) ->
    pr "@[<hov 1>(if@ %a@ then@ %a@ else@ %a)@]"
      term t1 term t2 term t3
  | Let (v, t1, t2) ->
    pr "@[<hov 1>(let@ %a@ =@ %a@ in@ %a)@]"
      id v term t1 term t2

let rec list ~sep element fmttr =
  function
  | [] -> ()
  | [x] -> element fmttr x
  | x :: xs ->
    fprintf fmttr "%a%( fmt %)" element x sep;
    list element ~sep fmttr xs

let list ?(pre:_ format6="") ~sep ?(post: _ format6="") element fmttr =
  function
  | [] -> ()
  | l ->
    fprintf fmttr "%( fmt %)%a%( smt %)" pre (list element ~sep) l post

let rec pred ~entry ~bw_ints ~consts fmttr =
  let pr fmt = fprintf fmttr fmt in
  let term_hlist fmttr = term_hlist ~entry ~bw_ints ~consts fmttr
  and term fmttr = term ~entry ~bw_ints ~consts fmttr
  and pred = pred ~entry ~bw_ints ~consts
  and triggers = triggers ~entry ~bw_ints ~consts
  and func fmttr = func ~entry ~where:`Logic ~bw_ints fmttr
  and logic_type fmttr = logic_type ~entry fmttr in
  function
  | True -> pr "true"
  | False -> pr "false"
  | And (`Don't_split, p1, p2) ->
    pr "@[(%a@ /\\@ %a)@]" pred p1 pred p2
  | And (`Split, p1, p2) ->
    pr "@[(%a@ &&@ %a)@]" pred p1 pred p2
  | Or (p1, p2) ->
    pr "@[(%a@ \\/@ %a)@]" pred p1 pred p2
  | Iff (p1, p2) ->
    pr "@[(%a@ <->@ %a)@]" pred p1 pred p2
  | Not p -> pr "@[(not@ %a)@]" pred p
  | Impl (p1, p2) ->
    pr "@[<hov 1>(%a@ ->@ %a)@]" pred p1 pred p2
  | If (t, p1, p2) ->
    pr "@[<hov 1>(if@ %a@ then@ %a@ else@ %a)@]"
      term t pred p1 pred p2
  | Let (v, t, p) ->
    pr "@[<hov 1>(let@ @[<hov 1>%a@ =@ %a@ in@]@ %a)@]"
      id v term t pred p
  | Forall (v, t, trigs, p) ->
    pr "@[<hov 1>(forall@ %a@ :@ %a%a.@ %a)@]"
      id v logic_type t triggers trigs pred p
  | Exists (v, t, trigs, p) ->
    pr "@[<hov 1>(exists@ %a@ :@ %a%a.@ %a)@]"
      id v logic_type t triggers trigs pred p
  | App (f, Nil) -> pr "%a" func f
  | App (f, (Cons _ as ts)) ->
    pr "@[(%a%a)@]" func f term_hlist ts
  | Labeled (l, p) ->
    pr "@[(%a%a)@]" why_label l pred p

and triggers ~entry ~bw_ints ~consts fmttr =
  let term fmttr = term ~entry ~bw_ints ~consts fmttr
  and pred = pred ~entry ~bw_ints ~consts in
  let pat fmttr =
    function
    | Term t -> term fmttr t
    | Pred p -> pred fmttr p
  in
  list ~pre:"@ [" (list pat ~sep:",@ ") ~sep:"@ |@ " ~post:"]@ " fmttr

let rec why_type : type a. entry:_ -> bw_ints:_ -> consts:_ -> _ -> a why_type -> _ =
  fun ~entry ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt
  and qid  = qid ~entry ~u:true
  and pred = pred ~entry ~bw_ints ~consts
  and logic_type fmttr = logic_type ~entry fmttr
  and why_type fmttr = why_type ~entry ~bw_ints ~consts fmttr in
  function
  | Arrow (id', t1, t2) ->
    let id' = if id' = "" then "_" else id' in
    let pr ~colon = pr "@[<hov 1>(%a@ :@ %a) %s@ %a@]" id id' why_type t1 (if colon then ":" else "") why_type t2 in
    begin match t2 with
    | Arrow _ -> pr ~colon:false
    | Typed (Arrow _, _) -> pr ~colon:false
    | Poly { why_type } when (match why_type with Arrow _ -> true | _  -> false) -> pr ~colon:false
    | Annot (_, Arrow _, _, _, _, _) -> pr ~colon:false
    | _ -> pr ~colon:true
    end
  | Logic t -> logic_type fmttr t
  | Ref t -> pr "ref@ %a" why_type t
  | Typed (wt, _) -> why_type fmttr wt
  | Poly { why_type = wt } -> why_type fmttr wt
  | Annot (p, t, reads, writes, q, signals) ->
    pr "%a@ " why_type t;
    pr "@[@[<hov 2>requires@ {@ %a@ }@]" pred p;
    let ids = list id ~sep:",@ " in
    begin match List.sort compare reads with
    | [] -> ()
    | reads ->
      pr "@ reads@ {@ %a@ }" ids reads
    end;
    begin match List.sort compare writes with
    | [] -> ()
    | writes ->
      pr "@ writes@ {@ %a@ }" ids writes
    end;
    pr "@ @[<hov 2>ensures@ {@ %a@ }@]" pred q;
    begin match signals with
    | [] -> pr "@]"
    | l ->
      pr "@ ";
      List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %a@ result@ ->@ %a@ }@]@]" qid e pred r) l
    end

let variant ~entry ~bw_ints ~consts fmttr =
  let pr fmt = fprintf fmttr fmt in
  function
  | None -> ()
  | Some (t, r_opt) ->
    pr "variant@ {@ %a@ }" (term ~entry ~bw_ints ~consts) t;
    Option.iter (pr "@ with@ %s") r_opt

let option value fmttr =
  function
  | None -> ()
  | Some v ->
    value fmttr v

let any_type ~entry ~bw_ints ~consts fmttr = function Why_type t -> why_type ~entry ~bw_ints ~consts fmttr t

let rec expr_hlist : type a. entry:_ -> safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr_hlist -> _ =
  fun ~entry ~safe ~bw_ints ~consts fmttr ->
  function
  | Nil -> ()
  | Cons (e, es) ->
    fprintf fmttr "@ %a" (expr ~entry ~safe ~bw_ints ~consts) e;
    expr_hlist ~entry ~safe ~bw_ints ~consts fmttr es

and expr_node : type a. entry:_ -> safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr_node -> _ =
  fun ~entry ~safe ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let pr_fun params pre body post diverges signals =
    let consts = List.fold_right (function _, Why_type (Ref _) -> Fn.id | x, _ -> StringSet.add x) params consts in
    let pred = pred ~entry ~bw_ints ~consts
    and any_type = any_type ~entry ~bw_ints ~consts
    and qid = qid ~entry ~u:true in
    pr "@[<hov 1>fun@ @[";
    List.iter (fun (x, t) -> pr "(%a@ :@ %a)@ " id x any_type t) params;
    pr "@]@ @[<hov 0>requires@ {@ %a@ }@ " pred pre;
    begin match signals with
    | [] -> pr "@[<hov 2>ensures@ {@ %a@ }@]@]@ " pred post
    | l ->
      pr "@[<hov 2>ensures@ {@ %a@ }@ %a@]@ "
        pred post
        (list ~sep:"@ " @@
         fun _ (e, r) ->
         pr "@[<hov 2>raises@ {@ %a@ result@ ->@ %a@ }@]" qid e pred r)
        l
    end;
    if diverges = `Diverges then pr "diverges@ ";
    pr "@ ->@ %a@]" (expr ~entry ~safe ~bw_ints ~consts) body
  in
  let pr_let id' e1 e2 =
    let consts = StringSet.add id' consts in
    let expr fmttr = expr ~entry ~safe ~bw_ints ~consts fmttr in
    pr "@[<hov 0>(let@ %a@ =@ %a@ in@ %a)@]" id id' expr e1 expr e2
  in
  let pred = pred ~entry ~bw_ints ~consts
  and qid = qid ~entry ~u:true
  and why_type fmttr = why_type ~entry ~bw_ints ~consts fmttr
  and variant fmttr = variant ~entry ~bw_ints ~consts fmttr
  and expr fmttr = expr ~entry ~safe ~bw_ints ~consts fmttr in
  let expr_list = list expr ~sep:";@ " in
  function
  | Const c -> constant fmttr c
  | Var v ->  pr "%a" id v
  | And (e1, e2) -> pr "@[(%a@ &&@ %a)@]" expr e1 expr e2
  | Or (e1, e2) -> pr "@[(%a@ ||@ %a)@]" expr e1 expr e2
  | Not e -> pr "@[(not@ %a)@]" expr e
  | Void -> pr "()"
  | Deref id' -> pr "!%a" id id'
  | Typed (e, _) -> expr fmttr e
  | Poly { expr_node = en } -> expr_node ~entry ~safe ~bw_ints ~consts fmttr en
  | If (e1, e2, e3) ->
    pr "@[<hov 0>(if@ %a@ @[<hov 1>then@ %a@]@ @[<hov 1>else@ %a@])@]"
      expr e1 expr e2 expr e3
  | While ({ expr_node = Const (Bool true) }, inv, var, e2) ->
    pr
      "@[<hov 0>loop@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ end@]"
      pred inv
      variant var
      expr_list e2
  | While (e1, inv, var, e2) ->
    pr
      "@[<hov 0>while@ %a@ do@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ done@]"
      expr e1
      pred inv
      variant var
      expr_list e2
  | Block ([], Void) -> pr "void"
  | Block ([], Return e) -> pr "%a" expr e
  | Block ([e], Void) -> pr "%a" expr e
  | Block (el, Void) -> pr "@[<hov 0>begin@ @[<hov 1>%a@]@ end@]" expr_list el
  | Block (el, Return e) -> pr "@[<hov 0>begin@ @[<hov 1>%a;@ %a@]@ end@]" expr_list el expr e
  | Assign (id', e) -> pr "@[<hov 1>(%a@ :=@ %a)@]" id id' expr e
  | Let (id, e1, e2) -> pr_let id e1 e2
  | Let_ref (id', e1, e2) ->
    pr "@[<hov 0>(let@ %a@ =@ ref@ %a@ in@ %a)@]" id id' expr e1 expr e2
  | App (Of_int (Int _ as ty, modulo), Cons ({ expr_labels = []; expr_node = Const c }, Nil), _) ->
    pr "@[<hov 1>%a@]" (of_int_const ~entry ~where:(`Behavior safe) ~bw_ints) ((ty, modulo), c)
  | App (f, ehl, ty_opt)  ->
    pr "@[<hov 1>(%a@ %a@ %a)@]"
      (func ~entry ~where:(`Behavior safe) ~bw_ints) f
      (expr_hlist ~entry ~safe ~bw_ints ~consts) ehl
      (option @@ fun fmttr -> fprintf fmttr ":@ %a" why_type) ty_opt
  | Raise (ex, None) ->
    pr "@[<hov 1>(raise@ %a)@]" qid ex
  | Raise (ex, Some e) ->
    pr "@[<hov 1>(raise@ (%a@ %a))@]" qid ex expr e
  | Try (e1, exc, None, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %a@ ->@ %a@ end@]" expr e1 qid exc expr e2
  | Try (e1, exc, Some id', e2) ->
    pr "@[<hov 1>try@ %a@ with@ %a@ %a@ ->@ %a@ end@]" expr e1 qid exc id id' expr e2
  | Fun (params, _, pre, body, post, diverges, signals) ->
    pr_fun params pre body post diverges signals
  | Triple (_, pre, e, True, []) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ (%a))@]" pred pre expr e
  | Triple (`Opaque, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ " pred pre;
    pr "abstract@ ensures@ {@ %a@ }@ " pred post;
    List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %a@ ->@ %a@ }@]" uid e pred r) exceps;
    pr "@ %a@ end)@]" expr e
  | Triple (`Transparent, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ " pred pre;
    begin match exceps with
    | [] ->
      pr "let@ _@ =@ %a@ in@ assert@ {@ %a@ }" expr e pred post
    | _ -> failwith "expr_node: unsupported non-empty exceps clause in Hoare triple" (* TODO *)
    end;
    pr ")@]"
  | Assert (k, p) ->
    pr "@[<hov 0>(%s@ {@ %a@ })@]"
      (match k with `ASSERT -> "assert" | `ASSUME -> "assume" | `CHECK -> "check")
      pred p
  | Black_box t ->
    pr "@[<hov 0>any@ %a@ @]" why_type t
  | Absurd -> pr "@[<hov 0>absurd@ @]"
  | Labeled (l, e) -> pr "@[(%a%a)@]" why_label l expr e

and expr : type a. entry:_ -> safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr -> _ =
  fun ~entry ~safe ~bw_ints ~consts fmttr e ->
  let pr fmt = fprintf fmttr fmt in
  let rec aux =
    function
    | [] -> expr_node ~entry ~safe ~bw_ints ~consts fmttr e.expr_node
    | s :: l ->
      pr "@[<hov 0>'%a:@ " uid s;
      aux l;
      pr "@]"
  in
  aux e.expr_labels

let any_logic_type ~entry fmttr = function Logic_type t -> logic_type ~entry fmttr t

let logic_arg ~entry fmttr (id', t) = fprintf fmttr "(%a@ :@ %a)" id id' (any_logic_type ~entry) t

let goal_kind fmttr =
  fprintf fmttr "%s" %
  function
  | KAxiom -> "axiom"
  | KLemma -> "lemma"
  | KGoal -> "goal"

let why_id ?(constr=false) fmttr { why_name; why_expl; why_pos } =
  let pr fmt = fprintf fmttr fmt in
  pr "%a" (if not constr then id else uid) why_name;
  if not (Position.is_dummy why_pos) then pr "@ %a" jc_position why_pos;
  if why_expl <> "" then pr "@ \"expl:%s\"" why_expl

type 'kind kind =
  | Theory : [`Let | `With] -> [`Theory of [< `Rec | `Nonrec]] kind
  | Module : [`Safe | `Unsafe] -> [`Module of [`Safe | `Unsafe]] kind

let why_decl ~entry (type k) ~(kind : k kind) ~bw_ints ~consts fmttr { why_id = why_id'; why_decl } =
  let pr fmt = fprintf fmttr fmt in
  let why_id = why_id ~constr:false
  and why_uid = why_id ~constr:true in
  let args = list ~sep:"@ " @@ fun fmt (_id, t) -> any_logic_type ~entry fmt t
  and logic_type fmttr = logic_type ~entry fmttr
  and logic_arg fmttr = logic_arg ~entry fmttr
  and pred = pred ~entry ~bw_ints
  and expr ~safe = expr ~entry ~safe ~bw_ints in
  let or_with s = match kind with Theory `With -> "with" | Theory `Let -> s | Module _ -> s in
  match (why_decl : k decl) with
  | Param t ->
    let consts =
      let rec collect_consts : type a. consts:_ -> a why_type -> _ = fun ~consts ->
        function
        | Logic _ -> consts
        | Ref _ -> consts
        | Typed (wt, _) -> collect_consts ~consts wt
        | Poly { why_type } -> collect_consts ~consts why_type
        | Arrow (id, t1, t2) ->
          let collect_consts' () = collect_consts ~consts:(StringSet.add id consts) t2 in
          begin match t1 with
          | Ref _ -> collect_consts ~consts t2
          | Logic _ -> collect_consts' ()
          | Arrow _ -> collect_consts' ()
          | Annot _ -> collect_consts' ()
          | Typed (wt, _) -> collect_consts ~consts wt
          | Poly { why_type } -> collect_consts ~consts why_type
          end
        | Annot (_, t, _, _, _, _) -> collect_consts ~consts t
      in
      collect_consts ~consts t
    in
    let colon =
      match t with
      | Arrow _ -> ""
      | Typed (Arrow _, _) -> ""
      | Poly { why_type } when (match why_type with Arrow _ -> true | _  -> false) -> ""
      | Annot (_, Arrow _, _, _, _, _) -> ""
      | _ -> ":"
    in
    pr "val@ %a%s@ %a" why_id why_id' colon (why_type ~entry ~bw_ints ~consts) t
  | Logic (args', Type (Bool, Nil)) ->
    pr "%s@ %a@ %a" (or_with "predicate") why_id why_id' args args'
  | Logic (args', t) ->
    pr "%s@ %a@ %a@ :@ %a" (or_with "function") why_id why_id' args args' logic_type t
  | Inductive (args', cases) ->
    pr "inductive@ %a@ @[%a@]@ =@\n@[<v 0>%a@]"
      why_id why_id'
      args args'
      (list ~sep:"@ " @@ fun _ (id', p) -> pr "|@ %a:@ @[%a@]" id id' (pred ~consts) p) cases
  | Goal (k, p) ->
    pr "%a %a@ %s :@ @[<hov 1>%a@]"
      goal_kind k
      why_uid why_id'
      (match k with
       | KAxiom
         when String.(length why_id'.why_name >= 11 &&
                      equal "LF__Lemma__" @@ sub why_id'.why_name 0 11) -> "\"W:non_conservative_extension:N\""
       | _                                                              -> "")
      (pred ~consts) p
  | Def e ->
    let Module safe = kind in
    pr "let@ %a@ =@ %a"
      why_id why_id'
      (expr ~consts ~safe) e
  | Predicate (args, p) ->
    pr "%s@ %a@ %a@ =@[<hov 2>@ %a@]"
      (or_with "predicate")
      why_id why_id'
      (list ~sep:"@ " logic_arg) args
      (pred ~consts:(List.fold_right (StringSet.add % fst) args consts)) p
  | Function (args, t, e) ->
    pr "%s %a@ %a :@ %a@ =@[<hov 2>@ %a@]"
      (or_with "function")
      why_id why_id'
      (list ~sep:"@ " logic_arg) args
      logic_type t
      (term ~entry ~bw_ints ~consts:(List.fold_right (StringSet.add % fst) args consts)) e
  | Type tvs ->
    pr "type@ %a@ %a" why_id why_id' (list ~sep:"@ " id) tvs
  | Exception None ->
    pr "exception@ %a" why_uid why_id'
  | Exception (Some t) ->
    pr "exception@ %a@ %a" why_uid why_id' logic_type t

let why_decl_group ~entry (type k) ~(kind : k kind) ~bw_ints ~consts fmttr (d : k why_decl_group) =
  let pr fmt = fprintf fmttr fmt in
  match d with
  | Rec (d, ds) ->
    why_decl ~entry ~kind:(Theory `Let) ~bw_ints ~consts fmttr d;
    pr "@\n";
    List.iter (fun d -> why_decl ~entry ~kind:(Theory `With) ~bw_ints ~consts fmttr d; pr "@\n") ds
  | Nonrec d ->
    why_decl ~entry ~kind:(Theory `Let) ~bw_ints ~consts fmttr d
  | Code d ->
    why_decl ~entry ~kind ~bw_ints ~consts fmttr d

module Staged :
sig
  type +'a t
  val stage : 'a -> 'a t
  val unstage : 'a t -> 'a
end = struct
  type 'a t = 'a
  let stage = Fn.id
  let unstage = Fn.id
end

open Staged

let split_fprintf ~cons =
  let open Buffer in
  let buf = create 10 in
  let buf_formatter = formatter_of_buffer buf in
  stage @@
  fun f expand x ->
  let x, imported = expand x in
  fprintf buf_formatter "%a%!" f x;
  let scope, name = split '.' @@ contents buf in
  clear buf;
  (if scope <> "" then cons scope imported else `Current), name

let expand_func : _ func -> _ func * _ =
  function
  | User ((where, `Short), name) -> User ((where, `Qualified), name), true
  | f -> f, false

let expand_tconstr : _ tconstr -> _ tconstr * _ =
  function
  | User ((where, `Short), name) -> User ((where, `Qualified), name), true
  | f -> f, false

let (|~>) init f = f ~init

let (%~>) f' f ~init = f ~init:(f' ~init)

let ref_module = `Module ("Ref", true)

let ref_theory = `Theory ("Ref", true)

let deref = "(!)"

let int_theory = `Theory ("Int", true)

module Func =
struct
  type ('a, 'b) t = ('a, 'b) func

  type _ kind =
    | Logic : [> `Current | `Theory of string * bool ] kind
    | Code : [ `Safe | `Unsafe ] -> [> `Current | `Theory of string * bool | `Module of string * bool ] kind

  let fold (type s) (type a) (type b) (type k) :
    entry:_ -> bw_ints:_ -> kind:k kind -> f:(acc:s -> k * string -> s) -> init:_ -> (a, b) t -> _ =
    fun ~entry ~bw_ints ~kind ~f ->
      let func = func ~entry ~bw_ints in
      let func, (split_fprintf : _ -> _ -> _ -> k * string) =
        match kind with
        | Logic ->
          func ~where:`Logic, unstage (split_fprintf ~cons:(fun th imported -> `Theory (th, imported)))
        | Code safe ->
          func ~where:(`Behavior safe), unstage (split_fprintf ~cons:(fun md imported -> `Module (md, imported)))
      in
      fun ~init f' ->
        let usage = split_fprintf func expand_func f' in
        let fold_int () =
          let usage : k * string =
            match kind, usage with
            | Logic, (`Current, name) -> int_theory, name
            | Code _, (`Current, name) -> int_theory, name
            | Logic, u -> u
            | Code _, u -> u
          in
          f ~acc:init usage
        in
        match f' with
        | U_int_op _ -> fold_int ()
        | B_int_op _ -> fold_int ()
        | B_num_pred _ -> fold_int ()
        | _ -> f ~acc:init usage

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Term =
struct
  type 'a t = 'a term
  let rec fold : type a. entry:_ -> bw_ints:_ -> f:_ -> init:_ -> a term -> _ = fun ~entry ~bw_ints ~f ->
    let fold t = fold ~entry ~bw_ints ~f t
    and fold_hlist hl = fold_hlist ~entry ~bw_ints ~f hl
    and fold_func f' = Func.fold ~entry ~bw_ints ~kind:Func.Logic ~f f' in
    let fold_id ~init id = f ~acc:init (`Current, id) in
    fun ~init ->
    function
    | Const _ -> init
    | App (f', thl) ->
      fold_func ~init f' |~>
      fold_hlist thl
    | Var v -> fold_id ~init v
    | Deref v ->
      f ~acc:init (ref_theory, deref) |~>
      fold_id v
    | Deref_at (v, _) ->
      f ~acc:init (ref_theory, deref) |~>
      fold_id v
    | Typed (t, _) -> fold ~init t
    | Poly { term } -> fold ~init term
    | Labeled (_, t) -> fold ~init t
    | If (i, t, e) ->
      fold ~init i |~>
      fold t |~>
      fold e
    | Let (_, t1, t2) ->
      fold ~init t1 |~>
      fold t2
  and fold_hlist : type a. entry:_ -> bw_ints:_ -> f:_ -> init:_ -> a term_hlist -> _ = fun ~entry ~bw_ints ~f ->
    let fold t = fold ~entry ~bw_ints ~f t
    and fold_hlist hl = fold_hlist ~entry ~bw_ints ~f hl in
    fun ~init ->
    function
    | Nil -> init
    | Cons (t, ts) ->
      fold ~init t |~>
      fold_hlist ts

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Logic_type =
struct
  type 'a t = 'a logic_type
  let rec fold : type a. entry:_ -> bw_ints:_ -> f:_ -> init:_ -> a logic_type -> _ = fun ~entry ~bw_ints ~f ->
    let fold lt = fold ~entry ~bw_ints ~f lt in
    let split_fprintf f = unstage (split_fprintf ~cons:(fun th imported -> `Theory (th, imported))) f in
    fun ~init ->
    function
    | Type (tc, lthl) ->
      f ~acc:init (split_fprintf (tconstr ~entry) expand_tconstr tc) |~>
      let rec fold' : type a. init:_ -> a ltype_hlist -> _ = fun ~init ->
        function
        | Nil -> init
        | Cons (lt, lts) ->
          fold ~init lt |~>
          fold' lts
      in
      fold' lthl

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Pred =
struct
  type t = pred
  let rec fold ~entry ~bw_ints ~f =
    let fold p = fold ~entry ~bw_ints ~f p
    and fold_term t = Term.fold ~entry ~bw_ints ~f t
    and fold_term_hlist hl = Term.fold_hlist ~entry ~bw_ints ~f hl
    and fold_logic_type lt = Logic_type.fold ~entry ~bw_ints ~f lt
    and fold_func f' = Func.fold ~entry ~bw_ints ~kind:Func.Logic ~f f' in
    fun ~init ->
    let fold_quant lt trigs p =
      fold_logic_type ~init lt |~>
      (let f init =
        function
        | Pred p -> fold ~init p
        | Term t -> fold_term ~init t
       in
       ListLabels.fold_left ~f:(List.fold_left f) trigs) |~>
      fold p
    in
    function
    | True | False -> init
    | And (_, p1, p2)
    | Or (p1, p2)
    | Iff (p1, p2)
    | Impl (p1, p2) ->
      fold ~init p1 |~>
      fold p2
    | Not p
    | Labeled (_, p) -> fold ~init p
    | If (t, p1, p2) ->
      fold_term ~init t |~>
      fold p1 |~>
      fold p2
    | Let (_, t, p) ->
      fold_term ~init t |~>
      fold p
    | Forall (_, lt, trigs, p) ->
      fold_quant lt trigs p
    | Exists (_, lt, trigs, p) ->
      fold_quant lt trigs p
    | App (p, thl) ->
      fold_func ~init p |~>
      fold_term_hlist thl

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Qid =
struct
  type t = (string * [ `Qualified | `Short ]) * string

  let fold ~entry ~init ~f =
    function
    | (md, qual), ex when md <> entry ->
      f ~acc:init (`Module (md, qual = `Short), ex)
    | _, ex ->
      f ~acc:init (`Current, ex)

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Why_type =
struct
  type 'a t = 'a why_type
  let rec fold : type a. entry:_ -> bw_ints:_ -> f:_ -> init:_ -> a why_type -> _ = fun ~entry ~bw_ints ~f ->
    let fold wt = fold ~entry ~bw_ints ~f wt
    and fold_logic_type lt = Logic_type.fold ~entry ~bw_ints ~f lt
    and fold_pred = Pred.fold ~entry ~bw_ints ~f
    and fold_qid = Qid.fold ~entry ~f
    in
    fun ~init ->
    function
    | Arrow (_, wt1, wt2) ->
      fold ~init wt1 |~>
      fold wt2
    | Logic lt ->
      fold_logic_type ~init lt
    | Ref wt ->
      f ~acc:init (ref_module, "ref") |~>
      fold wt
    | Typed (wt, _) -> fold ~init wt
    | Poly { why_type } -> fold ~init why_type
    | Annot (pre, wt, reads, writes, post, exns) ->
      fold_pred ~init pre |~>
      fold wt |~>
      let f acc name = f ~acc (`Current, name) in
      let open ListLabels in
      fold_left ~f reads %~>
      fold_left ~f writes %~>
      fold_pred post %~>
      fold_left ~f:(fun init (name, p) -> fold_qid ~init name |~> fold_pred p) exns

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Expr =
struct
  type 'a t = 'a expr
  let rec fold : type a. entry:_ -> safe:_ -> bw_ints:_ -> f:_ -> init:_ -> a expr -> _ =
    fun ~entry ~safe ~bw_ints ~f ->
    let fold ~init e = fold ~entry ~safe ~bw_ints ~f ~init e
    and fold_hlist hl = fold_hlist ~entry ~safe ~bw_ints ~f hl
    and fold_pred = Pred.fold ~entry ~bw_ints ~f
    and fold_term t = Term.fold ~entry ~bw_ints ~f t
    and fold_why_type wt = Why_type.fold ~entry ~bw_ints ~f wt
    and fold_func f' = Func.fold ~entry ~bw_ints ~kind:(Func.Code safe) ~f f'
    and fold_qid = Qid.fold ~entry ~f
    in
    let split_fprintf f = unstage (split_fprintf ~cons:(fun th imported -> `Theory (th, imported))) f in
    let fold' init e = fold ~init e in
    fun ~init e ->
    match e.expr_node with
    | Const _ -> init
    | Var v
    | Deref v ->
      f ~acc:(f ~acc:init (ref_module, deref)) (`Current, v)
    | And (e1, e2) ->
      fold ~init e1 |~>
      fold e2
    | Or (e1, e2) ->
      fold ~init e1 |~>
      fold e2
    | Not e -> fold ~init e
    | Void -> init
    | Typed (e, _) -> fold ~init e
    | Poly { expr_node } -> fold ~init { e with expr_node }
    | If (i, t, e) ->
      fold ~init i |~>
      fold t |~>
      fold e
    | While (cond, inv, var, exprs) ->
      fold ~init cond |~>
      fold_pred inv |~>
      Option.fold
        var
        ~f:(fun init (var, rel) ->
          fold_term ~init var |~>
          Option.fold
            rel
            ~f:(fun acc rel ->
              f ~acc @@ split_fprintf pp_print_string (fun s -> s, false) rel)) |~>
      ListLabels.fold_left ~f:fold' exprs
    | Block (l, e) ->
      List.fold_left fold' init l |~>
      begin match e with
      | Void -> fun ~init -> init
      | Return e -> fold e
      end
    | Assign (v, e) ->
      f ~acc:init (`Current, v) |~>
      fold e
    | Let (_, e1, e2) ->
      fold ~init e1 |~>
      fold e2
    | Let_ref (_, e1, e2) ->
      f ~acc:init (ref_module, "ref") |~>
      fold e1 |~>
      fold e2
    | App (f', hl, wt_opt) ->
      fold_func ~init f' |~>
      fold_hlist hl |~>
      Option.fold ~f:(fun init wt -> fold_why_type ~init wt) wt_opt
    | Raise (qid, e_opt) ->
      fold_qid ~init qid |~>
      Option.fold ~f:fold' e_opt
    | Try (e, qid, v, h) ->
      let f ~init:acc = f ~acc in
      fold ~init e |~>
      fold_qid qid |~>
      Option.fold ~f:(fun init v -> f ~init (`Current, v)) v |~>
      fold h
    | Fun (args, rt, pre, e, post, _, exns) ->
      List.fold_left (fun init (_, Why_type t) -> fold_why_type ~init t) init args |~>
      fold_why_type rt |~>
      fold_pred pre |~>
      fold e |~>
      fold_pred post |~>
      ListLabels.fold_left ~f:(fun init (qid, p) -> fold_qid ~init qid |~> fold_pred p) exns
    | Triple (_, pre, e, post, exns) ->
      fold_pred ~init pre |~>
      fold e |~>
      fold_pred post |~>
      ListLabels.fold_left ~f:(fun acc (id, p) -> f ~acc (`Current, id) |~> fold_pred p) exns
    | Assert (_, p) ->
      fold_pred ~init p
    | Black_box wt -> fold_why_type ~init wt
    | Absurd -> init
    | Labeled (_, e) -> fold ~init e
  and fold_hlist : type a. entry:_ -> safe:_ -> bw_ints:_ -> f:_ -> init:_ -> a expr_hlist -> _ =
    fun ~entry ~safe ~bw_ints ~f ->
    let fold t = fold ~entry ~safe ~bw_ints ~f t
    and fold_hlist hl = fold_hlist ~entry ~safe ~bw_ints ~f hl in
    fun ~init ->
    function
    | Nil -> init
    | Cons (t, ts) ->
      fold ~init t |~>
      fold_hlist ts

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Why_decl =
struct
  type 'kind t = 'kind why_decl

  type ('kind, 'deps) kind =
    | Theory : ([`Theory of [< `Rec | `Nonrec ]], [> `Theory of string * bool | `Current]) kind
    | Module : [`Safe | `Unsafe] ->
      ([`Module of [`Safe | `Unsafe]],
       [> `Theory of string * bool | `Module of string * bool | `Current ]) kind

  let fold ~entry ~bw_ints (type a) (type b) (type s) ~(kind : (a, b) kind) ~(f : acc:s -> b * string -> s) =
    let fold_why_type ~f wt = Why_type.fold ~entry ~bw_ints ~f wt
    and fold_logic_type ~f t = Logic_type.fold ~entry ~bw_ints ~f t
    and fold_pred ~f = Pred.fold ~entry ~bw_ints ~f
    and fold_term ~f t = Term.fold ~entry ~bw_ints ~f t in
    let fold_args ~f ~init =
      List.fold_left (fun init (_, Logic_type lt) -> fold_logic_type ~f ~init lt) init
    in
    fun ~(init : s) (d : a why_decl) ->
    match d.why_decl with
    | Param wt -> let Module _ = kind in fold_why_type ~f ~init wt
    | Def e -> let Module safe = kind in Expr.fold ~entry ~safe ~bw_ints ~f ~init e
    | Logic (args, rt) ->
      let Theory = kind in
      fold_args ~f ~init args |~>
      fold_logic_type ~f rt
    | Predicate (args, p) ->
      let Theory = kind in
      fold_args ~f ~init args |~>
      fold_pred ~f p
    | Inductive (args, preds) ->
      let Theory = kind in
      fold_args ~f ~init args |~>
      ListLabels.fold_left preds ~f:(fun init (_, p) -> fold_pred ~f ~init p)
    | Goal (_, p) ->
      let Theory = kind in
      fold_pred ~f ~init p
    | Function (args, rt, t) ->
      let Theory = kind in
      fold_args ~f ~init args |~>
      fold_logic_type ~f rt |~>
      fold_term ~f t
    | Type _ -> let Theory = kind in init
    | Exception lt_opt ->
      let Module _ = kind in
      Option.fold lt_opt ~init ~f:(fun init -> fold_logic_type ~f ~init)

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Why_decl_group =
struct
  open Why_decl
  let fold ~entry ~bw_ints (type a b c) ~(kind : (a, b) kind) ~(f : acc:c -> b * string -> c) =
    let fold ~kind ~f ~init d = fold ~entry ~bw_ints ~kind ~f ~init d in
    fun ~(init : c) (d : a why_decl_group) ->
      match kind, d with
      | Theory as kind,   Rec (d, ds) -> List.fold_left (fun init -> fold ~kind ~f ~init) (fold ~kind ~f ~init d) ds
      | Theory as kind,   Nonrec d    -> fold ~kind ~f ~init d
      | Module _ as kind, Code d      -> fold ~kind ~f ~init d

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
  let iter_ids (type k) f (d : k why_decl_group) =
    match d with
    | Rec (d, ds) -> f d.why_id; List.iter (fun d -> f d.why_id) ds
    | Nonrec d    -> f d.why_id
    | Code d      -> f d.why_id
  let iter_names f = iter_ids (fun d -> f d.why_name)
  let id (type k) (d : k why_decl_group) =
    match d with
    | Rec (d, _) -> d.why_id
    | Nonrec d   -> d.why_id
    | Code d     -> d.why_id
  let name d = (id d).why_name
  let pos d = (id d).why_pos
end

module Entry =
struct
  type 'kind t = 'kind entry

  type 's for_any_entry =
    { f : 'a. state:'s -> consts:StringSet.t -> enter:(consts:StringSet.t -> StringSet.t) ->
        'a entry -> 's * StringSet.t }
  type ('s, 'k) for_why_decl_group =
    state:'s -> consts:StringSet.t -> enter:(consts:StringSet.t -> StringSet.t) ->
    print:(consts:StringSet.t -> formatter -> unit) -> 'k why_decl_group -> 's * StringSet.t

  type 'a over =
    | Entries :
        <
          iter_entries : 'iter_entries;
          iter_decls   : _;
          iter         : 'iter_entries;
          decl_kind    : _;
          value        : some_entry;
          f            : 'state for_any_entry;
          state        : 'state
        > over
    | Decls :
        <
          iter_entries : _;
          iter_decls   : 'iter_decls;
          iter         : 'iter_decls;
          decl_kind    : 'decl_kind;
          value        : 'decl_kind why_decl_group;
          f            : ('state, 'decl_kind) for_why_decl_group;
          state        : 'state
        > over

  module M = Map.Make (String)

  module H =
    Hashtbl.Make
      (struct
        type t = string
        let equal a b = String.compare a b = 0
        let hash = Hashtbl.hash
      end)

  type ('s, 'f) iter_entries =
    { iter : 'a. consts:StringSet.t -> entry:'a entry -> (enter:'s -> f:'f -> StringSet.t) Staged.t }

  type ('s, 'v, 'k, 'f) continuation =
    { continue :
        'a.
          state:('s * 'v) H.t ->
        consts:StringSet.t ->
        entry:(unit -> 'k entry) -> (* Exactly the same entry as was passed to the outer iter function *)
        entry':'a entry -> (* Possibly different entry for further implicit self-recursion *)
        (enter:'s -> f:'f -> StringSet.t) Staged.t }

  let expansions = ref []

  let add_expansion pat expansion = expansions := (Str.regexp pat, expansion) :: !expansions

  let () =
    add_expansion "\\(Bit_u?i\\|Ui\\|I\\)nt[0-9]+" (`Prefix "enum");
    add_expansion "Bit_u?int[0-9]+_of_bit_u?int[0-9]+" (`Prefix "enum");
    add_expansion "Int" (`Prefix "int");
    add_expansion "ComputerDivision" (`Prefix "int");
    add_expansion "Abs" (`Prefix "int");
    add_expansion "MinMax" (`Prefix "int");
    add_expansion "Bool" (`Prefix "bool");
    add_expansion "Ref" (`Prefix "ref");
    add_expansion
      "\\(\
       Acc_offset_safe\\|\
       Acc_safe\\|\
       Acc_unsafe\\|\
       Alloc\\|\
       Allocable\\|\
       Alloc_table\\|\
       Any_alloc_table\\|\
       Any_bool\\|\
       Any_int\\|\
       Any_memory\\|\
       Any_pointer\\|\
       Any_real\\|\
       Any_tag_table\\|\
       Assigns\\|\
       Assigns_strong\\|\
       Charp_tag_id\\|\
       Downcast_safe\\|\
       Downcast_unsafe\\|\
       Eq_pointer_safe\\|\
       Eq_pointer_unsafe\\|\
       Memory\\|\
       Pointer\\|\
       Pset\\|\
       Pset_all\\|\
       Pset_deref\\|\
       Pset_disjoint\\|\
       Pset_included\\|\
       Pset_range\\|\
       Pset_range_left\\|\
       Pset_range_right\\|\
       Pset_union\\|\
       Reinterpret\\|\
       Reinterpret_cast\\|\
       Reinterpret_safe\\|\
       Return\\|\
       Rmem\\|\
       Rreinterpret_unsafe\\|\
       Same_except\\|\
       Shift_safe\\|\
       Shift_unsafe\\|\
       Sidecast\\|\
       Sidecast_safe\\|\
       Sidecast_safe_reinterpret\\|\
       Sidecast_unsafe\\|\
       Sub_pointer_safe\\|\
       Sub_pointer_unsafe\\|\
       Tag\\|\
       Tag_id\\|\
       Tag_table\\|\
       Tag_table_type\\|\
       Upd_offset_safe\\|\
       Upd_safe\\|\
       Upd_unsafe\\|\
       Voidp\\|\
       Voidp_tag_id\\|\
       Zwf\\)$"
      (`Prefix "core");
    add_expansion "[A-Za-z_]+_enum\\|Enum" (`Prefix "enum")

  let expansion_acts = H.create 25

  let register name =
    ListLabels.iter
      !expansions
      ~f:(fun (pat, expansion) ->
        if Str.string_match pat name 0 && Str.match_end () = String.length name then
          H.add expansion_acts name expansion);
    name

  let expand =
    let apply expansion name =
      match expansion with
      | `Prefix p -> String.lowercase p ^ "." ^ name
      | `Subst s -> s
    in
    fun name->
    try apply (H.find expansion_acts name) name with Not_found -> name

  let dep ~name =
    let no_subst =
      match H.find expansion_acts name with
      | `Prefix _ -> true
      | `Subst _ -> false
      | exception Not_found -> true
    in
    function
    | `Import None | `Export as r -> r
    | `As None as r when no_subst -> r
    | `As None -> `As (Some name)
    | `Import _ | `As _ as r when no_subst -> r
    | `Import (Some name') | `As Some (name') ->
      failwith ("dep: conflicting `as' imports: `" ^ name' ^"' vs. `" ^ name ^ "'")

  let iter =
    fun (type iter) (type value) (type decl_kind) (type f) (type state)
      ~(over : <
        iter_entries : file:value list -> (state, f) iter_entries;
        iter_decls   : consts:StringSet.t -> entry:decl_kind entry -> (enter:state -> f:f -> StringSet.t) Staged.t;
        iter         : iter;
        decl_kind    : decl_kind;
        value        : value;
        f            : f;
        state        : state
                       > over)
      ~(init : state)
      ->
        let continue : (state, value, decl_kind, f) continuation -> iter = fun { continue } ->
          let state : (state * value) H.t = H.create 100 in
          match over with
          | Entries ->
            fun ~file ->
              let f (type k) (e : k entry) =
                let add name = H.add state name (init, Entry e) in
                match e with
                | Theory (id, _) -> add (register id.why_name)
                | Module (id, _) -> add (register id.why_name)
              in
              List.iter (fun (Entry e) -> f e) file;
              { iter = fun ~consts ~entry -> continue ~state ~consts ~entry:(fun () -> assert false) ~entry':entry }
          | Decls ->
            fun ~consts ~entry ->
              let (l : decl_kind why_decl_group list) =
                match entry with
                | Theory (_, None) -> []
                | Module (_, None) -> []
                | Theory (_, Some (_, decls)) -> decls
                | Module (_, Some (_, _, decls)) -> decls
              in
              List.iter (fun g -> Why_decl_group.iter_names (fun name -> H.add state name (init, g)) g) l;
              continue ~state ~consts ~entry:(fun () -> entry) ~entry':entry
        in
        let map_ints ~how =
          let b = Buffer.create 25 in
          let b_formatter = formatter_of_buffer b in
          List.fold_left
            (fun m (Int ty as typ) ->
               int_ty
                 ~how:(match how with `Theory -> `Theory `Abstract | `Module safe -> `Module (`Abstract, safe))
                 b_formatter
                 ty;
               pp_print_flush b_formatter ();
               let scope = Buffer.contents b in
               Buffer.clear b;
               M.add scope typ m)
            M.empty
            O.([Int Int8.ty;
                Int Uint8.ty;
                Int Int16.ty;
                Int Uint16.ty;
                Int Int32.ty;
                Int Uint32.ty;
                Int Int64.ty;
                Int Uint64.ty])
        in
        let bw_ints_cache = H.create 50 in
        let rec continuation
          : type kind.
            state: (state * value) H.t -> consts:_ -> entry:(unit -> decl_kind entry) -> entry':kind entry ->
          (enter:state -> f:f -> StringSet.t) Staged.t =
          fun ~state ~consts ~entry ~entry' ->
            let bw_ints =
              let module M' = Map.Make (struct type t = any_integer let compare = compare end) in
              let fold_decl_group map init =
                let parse_conv_entry =
                  let open Str in
                  let conv_regexp =
                    regexp
                      "\\(Safe_\\|Unsafe_\\)?\\([Bb]it_\\)?\\([Uu]\\)?\\([Ii]nt[0-9]+\\)_of_\
                       \\(Safe_\\|Unsafe_\\)?\\([Bb]it_\\)?\\([Uu]\\)?\\([Ii]nt[0-9]+\\)"
                  in
                  let get s n =
                    try
                      matched_group n s
                    with
                    | Not_found -> ""
                  in
                  fun s ->
                    if string_match conv_regexp s 0 && match_end () = String.length s then
                      let get = get s in
                      Some (String.capitalize (get 2 ^ get 3 ^ get 4),
                            String.capitalize (get 6 ^ get 7 ^ get 8))
                    else
                      None
                in
                Why_decl_group.fold
                  ~bw_ints:S.empty
                  ~init
                  ~f:(fun ~acc:(s, m as acc) ->
                    let try_int_entry name f =
                      try
                        f (M.find name map)
                      with
                      | Not_found -> acc
                    in
                    let try_conv_entry name f =
                      match parse_conv_entry name with
                      | Some (name1, name2) ->
                        try_int_entry name1 @@ fun ty1 ->
                        try_int_entry name2 @@ fun ty2 ->
                        let find ty = try M'.find ty m with Not_found -> [] in
                        let tys1, tys2 = find ty1, find ty2 in
                        f ty1 ty2 M'.(add ty1 (ty2 :: tys1) m |> add ty2 (ty1 :: tys2))
                      | None -> acc
                    in
                    function
                    | (`Theory (name, _) | `Module (name, _)),
                      ("(&)" | "(|^)" | "(^)" | "(~_)" | "lsl" | "lsr" | "asr" | "lsl_modulo" |
                       "(+%)" | "(-%_)" | "(-%)" | "(*%)" | "(/%)" | "(%%)" | "of_int_modulo") ->
                      try_int_entry name (fun ty -> S.add ty s, m)
                    | (`Theory (name, _) | `Module (name, _)), "cast" ->
                      try_conv_entry name (fun _ _ m -> s, m)
                    | (`Theory (name, _) | `Module (name, _)), "cast_modulo" ->
                      try_conv_entry name (fun ty1 ty2 m -> S.(add ty1 s |> add ty2), m)
                    | (`Theory (name, _) | `Module (name, _)), reinterpret
                      when name = Name.Theory.reinterpret_mem ->
                      begin match Name.Theory.reinterpret_pred reinterpret with
                      | None -> acc
                      | Some (name, _) -> try_conv_entry name (fun ty1 ty2 m -> S.(add ty1 s |> add ty2), m)
                      end
                    | _ -> acc)
              in
              let close_bw_ints (s, deps) =
                let rec dfs ~deps ty acc =
                  if not (S.mem ty acc) then
                    let acc = S.add ty acc in
                    begin match M'.find ty deps with
                    | tys ->
                      List.fold_right (dfs ~deps) tys acc
                    | exception Not_found -> acc
                    end
                  else
                    acc
                in
                S.fold (dfs ~deps) s S.empty
              in
              let memo name r =
                try
                  H.find bw_ints_cache name
                with
                | Not_found ->
                  let r = r () in
                  H.add bw_ints_cache name r;
                  r
              in
              let open Why_decl in
              match entry' with
              | Theory (_, None) -> S.empty
              | Module (_, None) -> S.empty
              | Theory (id, Some (_, decls)) ->
                memo id.why_name @@
                fun () ->
                List.fold_left
                  (fold_decl_group ~entry:id.why_name ~kind:Theory @@ map_ints ~how:`Theory)
                  (S.empty, M'.empty)
                  decls |>
                close_bw_ints
              | Module (id, Some (_, safe, decls)) ->
                memo id.why_name @@
                fun () ->
                let map = M.fold M.add (map_ints ~how:`Theory) @@ map_ints ~how:(`Module safe) in
                List.fold_left
                  (fold_decl_group ~entry:id.why_name ~kind:(Module safe) map)
                  (S.empty, M'.empty)
                  decls |>
                close_bw_ints
            in
            stage @@
            fun ~(enter : state) ~(f : f) ->
            match over with
            | Entries ->
              let f' : 'a. state:state -> consts:_ -> enter:_ -> 'a entry -> state * _ = f.f in
              let enter (consts, acc) name imported =
                try
                  let s, (Entry e' as e) = H.find state name in
                  if s = init then H.replace state name (enter, e);
                  let s, consts =
                    f'
                      ~state:s
                      ~consts
                      ~enter:(fun ~consts -> unstage (continuation ~state ~consts ~entry ~entry':e') ~enter ~f)
                      e'
                  in
                  H.replace state name (s, e);
                  consts,
                  match M.find name acc with
                  | None | Some true -> acc
                  | Some false when imported = Some false -> acc
                  | Some false -> M.add name (Some true) acc
                  | exception Not_found -> M.add name imported acc
                with
                | Not_found -> failwith ("Unrecognized Why3ML file entry: " ^ name)
              in
              let f ~name init d =
                Why_decl_group.fold
                  ~bw_ints
                  ~f:(fun ~acc ->
                    function
                    | `Current, _ -> acc
                    | `Module (name', imported), _
                    | `Theory (name', imported), _ when name' <> name ->
                      enter acc name' (Some imported)
                    | (`Module _ | `Theory _), _ -> acc)
                  ~init
                  d
              in
              let open Why_decl in
              begin match entry' with
              | Theory (_, None) -> consts
              | Module (_, None) -> consts
              | Theory ({ why_name = name }, Some (deps, decls)) ->
                List.fold_left
                  (fun acc ->
                     function
                     | Use (_, Theory (id', _))
                     | Clone (_, Theory (id', _), _) ->
                       enter acc id'.why_name None)
                  (consts, M.empty)
                  !deps |~>
                ListLabels.fold_left ~f:(f ~entry:name ~kind:Theory ~name) decls |>
                fun (consts, m as acc) ->
                M.iter
                  (fun name import ->
                     match H.find state name, import with
                     | (_, Entry (Theory _ as e)), Some import ->
                       deps := Use ((if import then `Import None else `As None), e) :: !deps
                     | _ -> ()
                     | exception Not_found -> assert false (* already checked during map initialization *))
                  m;
                if fst (H.find state name) = init then
                  fst @@ enter acc name None
                else
                  consts
              | Module ({ why_name = name }, Some (deps, safe, decls)) ->
                List.fold_left
                  (fun acc ->
                     fun (Dependency d) ->
                       let enter (type k) =
                         function
                         | (Theory (id', _) : k entry) -> enter acc id'.why_name None
                         | Module (id', _) -> enter acc id'.why_name None
                       in
                       match d with
                       | Use (_, e) | Clone (_, e, _) -> enter e)
                  (consts, M.empty)
                  !deps |~>
                ListLabels.fold_left ~f:(f ~entry:name ~kind:(Module safe) ~name) decls |>
                fun (consts, m as acc) ->
                M.iter
                  (fun name import ->
                     let add import e =
                       deps := Dependency (Use ((if import then `Import None else `As None), e)) :: !deps
                     in
                     match H.find state name, import with
                     | (_, Entry (Theory _ as e)), Some import -> add import e
                     | (_, Entry (Module _ as e)), Some import -> add import e
                     | _ -> ()
                     | exception Not_found -> assert false (* already checked during map initialization *))
                  m;
                if fst (H.find state name) = init then
                  fst @@ enter acc name None
                else
                  consts
              end
            | Decls ->
              let f : state:state -> consts:_ -> enter:_ -> print:_ -> decl_kind why_decl_group -> state * _ = f in
              let enter ~self ~why_decl_group consts name =
                try
                  let s, d = H.find state name in
                  if s = init then Why_decl_group.iter_names (fun name -> H.replace state name (enter, d)) d;
                  let s, consts =
                    f
                      ~state:s
                      ~consts
                      ~enter:(fun ~consts -> self ~consts d)
                      ~print:(fun ~consts fmttr -> why_decl_group ~consts fmttr d)
                      d
                  in
                  Why_decl_group.iter_names (fun name -> H.replace state name (s, d)) d;
                  consts
                with
                | Not_found -> consts
              in
              let f ~name ~self ~why_decl_group ~consts d =
                Why_decl_group.fold
                  ~entry:name
                  ~bw_ints
                  ~init:consts
                  ~f:(fun ~acc:consts ->
                    function
                    | (`Module (name', _) | `Theory (name', _)), name'' when name = name' ->
                      enter ~self ~why_decl_group consts name''
                    | (`Module _ | `Theory _), _ -> consts
                    | `Current, name'' -> enter ~self ~why_decl_group consts name'')
                  d
              in
              let sort l =
                List.sort
                  Why_decl_group.(
                    fun d1 d2 ->
                      let c = Position.compare (pos d1) (pos d2) in
                      if c <> 0 then c else compare (id d1) (id d2))
                  l
              in
              let open Why_decl in
              match entry () with
              | Theory (_, None) -> consts
              | Module (_, None) -> consts
              | Theory ({ why_name = name }, Some (_, decls)) ->
                let why_decl_group = why_decl_group ~entry:name ~kind:(Theory `Let) ~bw_ints in
                let rec self ~consts d = f ~kind:Theory ~name ~self ~why_decl_group ~consts d in
                let enter ~consts d = enter ~self ~why_decl_group consts (Why_decl_group.name d) in
                List.fold_left (fun consts d -> enter ~consts:(self ~consts d) d) consts @@ sort decls
              | Module ({ why_name = name }, Some (_, safe, decls)) ->
                let why_decl_group = why_decl_group ~entry:name ~kind:(Module safe) ~bw_ints in
                let rec self ~consts d = f ~kind:(Module safe) ~name ~self ~why_decl_group ~consts d in
                let enter ~consts d = enter ~self ~why_decl_group consts (Why_decl_group.name d) in
                List.fold_left (fun consts d -> enter ~consts:(self ~consts d) d) consts @@ sort decls
        in
        continue { continue = continuation }
end

let dependency fmttr =
  let dependency_spec ~name fmttr =
    let pr fmt = fprintf fmttr fmt in
    let alias = option @@ fun fmt -> fprintf fmt "as@ %s" in
    function
    | `Import name_opt -> pr "import@ %s@ %a" name alias name_opt
    | `Export -> pr "export@ %s" name
    | `As name_opt -> pr "%s@ %a" name alias name_opt
  in
  let substs fmttr =
    function
    | [] -> ()
    | substs ->
      fprintf
        fmttr
        "@ with@ @[<hov 2>%a@]"
        (list
           ~sep:",@ " @@
         fun fmttr ->
         let pr fmt = fprintf fmttr fmt in
         let subst kind ~name ~name' = fprintf fmttr "%s@ %s@ =@ %s" kind name name' in
         function
         | `Constant (name, name') -> subst "constant" ~name ~name'
         | `Type (name, name') -> subst "type" ~name  ~name'
         | `Function (name, name') -> subst "function" ~name ~name'
         | `Predicate (name, name') -> subst "predicate" ~name ~name'
         | `Namespace (name, name') ->
           let name, name' = Pair.map ~f:(Option.value ~default:".") (name, name') in
           subst "namespace" ~name ~name'
         | `Lemma name -> pr "lemma %s" name
         | `Goal name -> pr "goal %s" name)
        substs
  in
  let pr fmt = fprintf fmttr fmt in
  let name (type a) =
    function
    | (Theory (id, _) : a entry) -> id.why_name
    | Module (id, _) -> id.why_name
  in
  function
  | Use (spec, entry) ->
    let name = name entry in
    pr "use@ %a" (dependency_spec ~name:(Entry.expand name)) (Entry.dep ~name spec)
  | Clone (spec, entry, substs') ->
    let name = Entry.expand (name entry) in
    pr "clone@ %a%a" (dependency_spec ~name) spec substs substs'

let module_dependency fmttr = function Dependency d -> dependency fmttr d

let entry ~consts fmttr (type k) (entry : k entry) =
  let pr fmt = fprintf fmttr fmt in
  let decls () =
    unstage
      (Entry.iter
         ~over:Entry.Decls
         ~init:`TODO
         ~consts
         ~entry)
      ~enter:`Running
      ~f:(fun ~state ~consts ~enter ~print d ->
        match state with
        | `TODO ->
          let consts = enter ~consts in
          pr "@\n%t@\n" @@ print ~consts;
          let add (type k) (d : k why_decl_group) =
            let add () = StringSet.add (Why_decl_group.name d) consts in
            match d with
            | Code { why_decl = Def _; _ }           -> add ()
            | Code { why_decl = Param (Logic _); _ } -> add ()
            | _                                      -> consts
          in
          `Done, add d
        | `Running ->
          (* Cyclic dependencies can be spurious due to local names treated as declarations *)
          `Running, consts
        | `Done -> `Done, consts)
  in
  let pr_entry kind name dep deps =
    pr "@\n%s@ %a@ @[<hov 2>@\n%a" kind (why_id ~constr:true) name (list dep ~sep:"@\n@\n" ~post:"@\n") deps;
    let consts = decls () in
    pr "@]@\nend@.";
    consts
  in
  match entry with
  | Theory (_, None) -> consts
  | Module (_, None) -> consts
  | Theory (name, Some (deps, _)) ->
    pr_entry "theory" name dependency !deps
  | Module (name, Some (deps, _, _)) ->
    pr_entry "module" name module_dependency !deps

let why3_builtin_locals = StringSet.singleton "result"

let file fmttr file =
  let open Entry in
  let iter =
    iter
      ~over:Entry.Entries
      ~init:`TODO
      ~file
  in
  let entry =
    fun fmttr ~consts e ->
      unstage
        (iter.iter
           ~consts
           ~entry:e)
        ~enter:`Running
        ~f:{ f = fun ~state ~consts ~enter e ->
          match state with
          | `TODO ->
            let consts = enter ~consts in
            let consts = entry fmttr ~consts e in
            `Done, consts
          | `Running ->
            failwith "Cyclic dependency between resulting Why3ML modules/theories"
          | `Done -> `Done, consts }
  in
  let consts = ref why3_builtin_locals in
  list
    ~sep:""
    (fun fmttr ->
       function
       | Entry entry' -> consts := entry fmttr ~consts:!consts entry')
    fmttr
    (List.sort
       (fun e1 e2 ->
          let compare
              { why_name = id1; why_pos = pos1 }
              { why_name = id2; why_pos = pos2 } =
            let c = Position.compare pos1 pos2 in
            if c <> 0 then c else compare id1 id2
          in
          let min l =
            List.fold_left
              (fun min curr ->
                 if compare min curr <= 0 then min else curr)
              (List.hd l)
              l
          in
          let decls =
            let ids l = List.map Why_decl_group.id l in
            function
            | Entry (Module (_, None)) -> []
            | Entry (Module (_, Some (_, _, decls))) -> ids decls
            | Entry (Theory (_, None)) -> []
            | Entry (Theory (_, Some (_, decls))) -> ids decls
          in
          match decls e1, decls e2 with
          | [], _ :: _ -> -1
          | _ :: _, [] -> 1
          | [], [] -> 0
          | decls1, decls2 ->
            compare (min decls1) (min decls2))
       file)

let entry ~consts fmttr e = ignore (entry ~consts fmttr e)

let file ~filename f =
  Why_pp.print_in_file
    (fun fmttr -> fprintf fmttr "%a" file f)
    filename

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_print_why3.ml"
  End:
*)
