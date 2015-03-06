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

open Format
(*open Why_pp*)

open Stdlib
open Envset

open Output_ast
module O = Output
(*open Output_misc*)

let fprintf_constant fmttr (type a) =
  let pr fmt = fprintf fmttr fmt in
  function
  | (Void : a constant) -> pr "()"
  | Int n -> pr "(%s)" n
  | Real f -> pr "%s" f
  | Bool true -> pr "Bool.True"
  | Bool false -> pr "Bool.False"

let fprintf_id fmttr id =
  fprintf fmttr "%s" @@
  match id.[0] with
  | 'A' .. 'Z' -> "_" ^ id
  | _ when Why3_kw.is_why3_keyword id -> id ^ "_why3"
  | _ -> id

let fprintf_uid fmttr uid =
  fprintf fmttr "%s" @@
  match uid.[0] with
  | 'A' .. 'Z' -> uid
  | 'a' .. 'z' -> String.capitalize uid
  | _ -> "U_" ^ uid

let fprintf_int_ty ~how fmttr (type r) (type b) (ty : (r range, b bit) integer) =
  let (module Int_ty) = O.module_of_int_ty ty in
  fprintf fmttr "%s" @@
  match how with
  | `Name -> Int_ty.name
  | `Theory false -> Int_ty.theory
  | `Theory true -> Int_ty.bit_theory
  | `Module (false, false) -> Int_ty.unsafe_module
  | `Module (false, true) -> Int_ty.safe_module
  | `Module (true, false) -> Int_ty.unsafe_bit_module
  | `Module (true, true) -> Int_ty.safe_bit_module

let fprintf_enum_ty ~how fmttr (Enum name) =
  let pr fmt = fprintf fmttr fmt in
  match how with
  | `Name -> pr "%s" name
  | `Theory -> pr "%a" fprintf_uid name
  | `Module false -> pr "%s" ("Unsafe_" ^ name)
  | `Module true -> pr "%s" ("Safe_" ^ name)

let fprintf_modulo fmttr modulo =
  fprintf fmttr "%s" @@
  match modulo with
  | true -> "%"
  | false -> ""

let fprintf_op fmttr op =
  fprintf fmttr "%s" @@
  match op with
  | `Add -> "+"
  | `Sub -> "-"
  | `Mul -> "*"
  | `Div -> "/"
  | `Mod -> "%%"
  | `Neg -> "-"
  | `And -> "&"
  | `Or -> "|^"
  | `Xor -> "^"
  | `Lsl -> "<<"
  | `Lsr -> ">>"
  | `Asr -> ">>>"
  | `Compl -> "~"
  | `Lt -> "<"
  | `Le -> "<="
  | `Gt -> ">"
  | `Ge -> ">="
  | `Eq -> "="
  | `Ne -> "<>"
  | `Neq -> "<>"

type any_integer = Int : ('r range, 'b bit) integer -> any_integer

module S =
  Set.Make
    (struct
      type t = any_integer
      let compare = compare
    end)

let fail_on_real () =
  failwith "floating point operations are not yet supported in GADT encoding, \
            please use the User generic constructor"

let fprintf_func ~where ~bw_ints fmttr (type a) (type b) =
  let pr fmt = fprintf fmttr fmt in
  let pr_bop fp ty = pr "%a.(%a%a)" fp ty in
  let pr_uop fp ty = pr "%a.(%a%a_)" fp ty in
  let pr_f fp ty = pr "%a.%s" fp ty in
  let fprintf_int_ty fmttr ty =
    fprintf_int_ty
      ~how:
        (match where, S.mem (Int ty) bw_ints with
         | `Logic, bit -> `Theory bit
         | `Behavior safe, bit -> `Module (safe, bit))
      fmttr
      ty
  in
  let fprintf_enum_ty fmttr ty =
    fprintf_enum_ty
      ~how:
        (match where with
         | `Logic -> `Theory
         | `Behavior safe -> `Module safe)
      fmttr
      ty
  in
  function
  | (B_int_op op : (a, b) func) -> pr "Int.(%a)" fprintf_op op
  | U_int_op op -> pr "Int.(%a_)" fprintf_op op
  | B_bint_op (op, (Int _ as ty), modulo) ->
    pr_bop fprintf_int_ty ty fprintf_op op fprintf_modulo modulo
  | B_bint_op (op, (Enum _ as ty), modulo) ->
    pr_bop fprintf_enum_ty ty fprintf_op op fprintf_modulo modulo
  | U_bint_op (op, (Int _ as ty), modulo) ->
    pr_uop fprintf_int_ty ty fprintf_op op fprintf_modulo modulo
  | U_bint_op (op, (Enum _ as ty), modulo) ->
    pr_uop fprintf_enum_ty ty fprintf_op op fprintf_modulo modulo
  | Of_int (Int _ as ty) -> pr_f fprintf_int_ty ty "of_int"
  | Of_int (Enum _ as ty) -> pr_f fprintf_enum_ty ty "of_int"
  | To_int (Int _ as ty) -> pr_f fprintf_int_ty ty "to_int"
  | To_int (Enum _ as ty) -> pr_f fprintf_enum_ty ty "to_int"
  | B_bint_bop (op, ty) -> pr_bop fprintf_int_ty ty fprintf_op op fprintf_modulo false
  | U_bint_bop (op, ty) -> pr_uop fprintf_int_ty ty fprintf_op op fprintf_modulo false
  | Lsl_bint (ty, modulo) -> pr_bop fprintf_int_ty ty fprintf_op `Lsl fprintf_modulo modulo
  | B_num_pred (pred, Integral Integer) -> pr "%a" fprintf_op pred
  | B_num_pred (pred, Integral (Int _ as ty)) -> pr_bop fprintf_int_ty ty fprintf_op pred fprintf_modulo false
  | B_num_pred (pred, Integral (Enum _ as ty)) -> pr_bop fprintf_enum_ty ty fprintf_op pred fprintf_modulo false
  | Poly op -> pr "%a" fprintf_op op
  | User (_, false, name) -> pr "%a" fprintf_id name
  | User (where, true, name) -> pr "%a.%a" fprintf_uid where fprintf_id name
  | To_float _ -> fail_on_real ()
  | Of_float _  -> fail_on_real ()
  | B_num_pred (_, Real _) -> fail_on_real ()

let fprintf_vc_kind fmttr k =
  fprintf fmttr "%s"
    (match k with
     | JCVCvar_decr -> "Variant decreases"
     | JCVCpack -> "Pack"
     | JCVCunpack -> "Unpack"
     | JCVCdiv_by_zero -> "Division by zero"
     | JCVCalloc_size -> "Allocation size"
     | JCVCuser_call n -> "Precondition for " ^ n
     | JCVCpointer_deref -> "Pointer dereference"
     | JCVCpointer_deref_bounds -> "Bounded pointer dereference"
     | JCVCpointer_shift -> "Pointer shift"
     | JCVCseparation -> "Separation assertion"
     | JCVCindex_bounds -> "Pointer index bounds"
     | JCVCdowncast -> "Pointer cast"
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

let fprintf_jc_position fmttr pos =
  let f, l, b, e as loc = Position.to_loc pos in
  if loc <> Why_loc.dummy_floc then
    fprintf fmttr "#\"%s\" %d %d %d#" f l b e

let fprintf_why_label fmttr { l_kind; l_behavior; l_pos } =
  let pr fmt = fprintf fmttr fmt in
  let with_behavior =
    match l_behavior with
    | "default" | "" -> ignore
    | b -> fun f -> f b
  in
  fprintf_jc_position fmttr l_pos;
  if not (Position.is_dummy l_pos) then pr "@ ";
  begin match l_kind with
  | Some vc_kind ->
    pr "\"expl:%a" fprintf_vc_kind vc_kind;
    with_behavior @@ pr ", behavior %s";
    pr "\"@ ";
  | None ->
    with_behavior @@ (fun b -> pr "\"for behavior %s\"@ " b)
  end

let fprintf_tconstr fmttr (type a) (type b) =
  let pr fmt = fprintf fmttr fmt in
  function
  | (Numeric (Integral Integer) : (a, b) tconstr) -> pr "int"
  | Numeric (Integral (Int _  as ty)) -> pr "%a.t" (fprintf_int_ty ~how:(`Theory false)) ty
  | Numeric (Integral (Enum _  as ty)) -> pr "%a.t" (fprintf_enum_ty ~how:`Theory) ty
  | Numeric (Real _) -> fail_on_real ()
  | Bool -> pr "Bool.bool"
  | Void -> pr "()"
  | Var v -> pr "'%a" fprintf_id v
  | User (_, false, name) -> pr "%a" fprintf_id name
  | User (where, true, name) -> pr "%a.%a" fprintf_uid where fprintf_id name

let rec fprintf_ltype_hlist : type a. _ -> a ltype_hlist -> _  = fun fmttr ->
  function
  | Nil -> ()
  | Cons (lt, ts) ->
    fprintf fmttr "@ %a" fprintf_logic_type lt;
    fprintf_ltype_hlist fmttr ts

and fprintf_logic_type : type a. _ -> a logic_type -> _ = fun fmttr ->
  function
  | Type (c, tps) ->
    fprintf fmttr "%a%a" fprintf_tconstr c fprintf_ltype_hlist tps

let rec fprintf_term_hlist : type a. bw_ints:_ -> consts:_ -> _ -> a term_hlist -> _ = fun ~bw_ints ~consts fmttr ->
  function
  | Nil -> ()
  | Cons (t, ts) ->
    fprintf fmttr "@ %a" (fprintf_term ~bw_ints ~consts) t;
    fprintf_term_hlist ~bw_ints ~consts fmttr ts

and fprintf_term : type a. bw_ints: _ -> consts:_ -> _ -> a term -> _ = fun ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let fprintf_term_hlist fmttr = fprintf_term_hlist ~bw_ints ~consts fmttr
  and fprintf_term fmttr = fprintf_term ~bw_ints ~consts fmttr
  and fprintf_func fmttr = fprintf_func ~where:`Logic ~bw_ints fmttr
  in
  function
  | Const c -> fprintf_constant fmttr c
  | App (f, Nil) -> pr "%a" fprintf_func f
  | App (f, (Cons _ as ts)) ->
    pr "@[(%a%a)@]" fprintf_func f fprintf_term_hlist ts
  | Var v -> pr "%a" fprintf_id v
  | Deref v | Deref_at (v, _) when StringSet.mem v consts ->
    pr "%a" fprintf_id v
  | Deref v -> pr "!%a" fprintf_id v
  | Deref_at (v, "") -> pr "(old@ !%a)" fprintf_id v
  | Deref_at (v, l) -> pr "(at@ !%a@ '%a)" fprintf_id v fprintf_uid l
  | Labeled (l, t) ->
    pr "(%a%a)" fprintf_why_label l fprintf_term t
  | If (t1, t2, t3) ->
    pr "@[<hov 1>(if@ %a@ then@ %a@ else@ %a)@]"
      fprintf_term t1 fprintf_term t2 fprintf_term t3
  | Let (v, t1, t2) ->
    pr "@[<hov 1>(let@ %a@ =@ %a@ in@ %a)@]"
      fprintf_id v fprintf_term t1 fprintf_term t2

let rec fprintf_list fprintf_element ~sep fmttr =
  function
  | [] -> ()
  | [x] -> fprintf_element fmttr x
  | x :: xs ->
    fprintf fmttr "%a%( fmt %)" fprintf_element x sep;
    fprintf_list fprintf_element ~sep fmttr xs

let rec fprintf_pred ~bw_ints ~consts fmttr =
  let pr fmt = fprintf fmttr fmt in
  let fprintf_term_hlist fmttr = fprintf_term_hlist ~bw_ints ~consts fmttr
  and fprintf_term fmttr = fprintf_term ~bw_ints ~consts fmttr
  and fprintf_pred = fprintf_pred ~bw_ints ~consts
  and fprintf_triggers = fprintf_triggers ~bw_ints ~consts
  and fprintf_func fmttr = fprintf_func ~where:`Logic ~bw_ints fmttr
  in
  function
  | True -> pr "true"
  | False -> pr "false"
  | And (p1, p2) ->
    pr "@[(%a@ /\\@ %a)@]" fprintf_pred p1 fprintf_pred p2
  | Or (p1, p2) ->
    pr "@[(%a@ \\/@ %a)@]" fprintf_pred p1 fprintf_pred p2
  | Iff (p1, p2) ->
    pr "@[(%a@ <->@ %a)@]" fprintf_pred p1 fprintf_pred p2
  | Not p -> pr "@[(not@ %a)@]" fprintf_pred p
  | Impl (p1, p2) ->
    pr "@[<hov 1>(%a@ ->@ %a)@]" fprintf_pred p1 fprintf_pred p2
  | If (t, p1, p2) ->
    pr "@[<hov 1>(if@ %a@ then@ %a@ else@ %a)@]"
      fprintf_term t fprintf_pred p1 fprintf_pred p2
  | Let (v, t, p) ->
    pr "@[<hov 1>(let@ @[<hov 1>%a@ =@ %a@ in@]@ %a)@]"
      fprintf_id v fprintf_term t fprintf_pred p
  | Forall (v, t, trigs, p) ->
    pr "@[<hov 1>(forall@ %a:@,%a@,%a@,.@ %a)@]"
      fprintf_id v fprintf_logic_type t fprintf_triggers trigs fprintf_pred p
  | Exists (v, t, trigs, p) ->
    pr "@[<hov 1>(exists@ %a:%a%a.@ %a)@]"
      fprintf_id v fprintf_logic_type t fprintf_triggers trigs fprintf_pred p
  | App (f, Nil) -> pr "%a" fprintf_func f
  | App (f, (Cons _ as ts)) ->
    pr "@[(%a%a)@]" fprintf_func f fprintf_term_hlist ts
  | Labeled (l, p) ->
    pr "@[(%a%a)@]" fprintf_why_label l fprintf_pred p

and fprintf_triggers ~bw_ints ~consts fmttr =
  let fprintf_term fmttr = fprintf_term ~bw_ints ~consts fmttr
  and fprintf_pred = fprintf_pred ~bw_ints ~consts
  in
  let fprintf_pat fmttr =
    function
    | Term t -> fprintf_term fmttr t
    | Pred p -> fprintf_pred fmttr p
  in
  fprintf_list ~sep:"@ |@ " (fprintf_list fprintf_pat ~sep:",@ ") fmttr

let rec fprintf_type : type a. bw_ints:_ -> consts:_ -> _ -> a why_type -> _ = fun ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let fprintf_pred = fprintf_pred ~bw_ints ~consts in
  let fprintf_type fmttr = fprintf_type ~bw_ints ~consts fmttr in
  function
  | Prod_type (id, t1, t2) ->
    let id = if id = "" then "_" else id in
    pr "@[<hov 1>(%a@ :@ %a)@ %a@]" fprintf_id id fprintf_type t1 fprintf_type t2
  | Base_type t -> fprintf_logic_type fmttr t
  | Ref_type t -> pr "ref@ %a" fprintf_type t
  | Annot_type (p, t, reads, writes, q, signals) ->
    pr "%a@ " fprintf_type t;
    pr "@[@[<hov 2>requires@ {@ %a@ }@]" fprintf_pred p;
    let fprintf_ids = fprintf_list fprintf_id ~sep:",@ "  in
    begin match List.sort compare reads with
    | [] -> ()
    | reads ->
      pr "@ reads@ {@ %a@ }" fprintf_ids reads
    end;
    begin match List.sort compare writes with
      | [] -> ()
      | writes ->
        pr "@ writes@ {@ %a@ }" fprintf_ids writes
    end;
    pr "@[<hov 2>ensures@ {@ %a@ }@]" fprintf_pred q;
    begin match signals with
      | [] -> pr "@]"
      | l ->
        pr "@ ";
        List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %s@ result@ ->@ %a@ }@]@]" e fprintf_pred r) l
    end

let fprintf_variant ~bw_ints ~consts fmttr =
  let pr fmt = fprintf fmttr fmt in
  function
  | None -> ()
  | Some (t, r_opt) ->
    pr "variant@ {@ %a@ }" (fprintf_term ~bw_ints ~consts) t;
    Option.iter (pr "@ with@ %s") r_opt

let fprintf_option fprintf_val fmttr =
  function
  | None -> ()
  | Some v ->
    fprintf_val fmttr v

let fprintf_any_type ~bw_ints ~consts fmttr = function Why_type t -> fprintf_type ~bw_ints ~consts fmttr t

let rec fprintf_expr_hlist : type a. safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr_hlist -> _ =
  fun ~safe ~bw_ints ~consts fmttr ->
  function
  | Nil -> ()
  | Cons (e, es) ->
    fprintf fmttr "@ %a" (fprintf_expr ~safe ~bw_ints ~consts) e;
    fprintf_expr_hlist ~safe ~bw_ints ~consts fmttr es

and fprintf_expr_node : type a. safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr_node -> _ =
  fun ~safe ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let pr_fun params ty pre body post diverges signals =
    let consts = List.fold_right (function _, Why_type (Ref_type _) -> Fn.id | x, _ -> StringSet.add x) params consts in
    let fprintf_pred = fprintf_pred ~bw_ints ~consts
    and fprintf_type fmttr = fprintf_type ~bw_ints ~consts fmttr
    and fprintf_any_type = fprintf_any_type ~bw_ints ~consts
    in
    pr "@[<hov 1>fun@ @[";
    List.iter (fun (x, t) -> pr "(%a@ :@ %a)@ " fprintf_id x fprintf_any_type t) params;
    pr ":@ %a" fprintf_type ty;
    pr "@]@ ->@ @[<hov 0>requires@ {@ %a@ }@ " fprintf_pred pre;
    begin match signals with
    | [] -> pr "@[<hov 2>ensures@ {@ %a@ }@]@]@ " fprintf_pred post
    | l ->
      pr "@[<hov 2>ensures@ {@ %a@ }@ %a@]@ "
        fprintf_pred post
        (fprintf_list ~sep:"" @@
         fun _ (e, r) ->
         pr "@[<hov 2>raises@ {@ %a@ result@ ->@ %a@ }@]" fprintf_uid e fprintf_pred r)
        l
    end;
    if diverges then pr "diverges@ ";
    pr "%a@]" (fprintf_expr ~safe ~bw_ints ~consts) body
  in
  let pr_let id e1 e2 =
    let consts = StringSet.add id consts in
    let fprintf_expr fmttr = fprintf_expr ~safe ~bw_ints ~consts fmttr in
    pr "@[<hov 0>(let@ %a@ =@ %a@ in@ %a)@]" fprintf_id id fprintf_expr e1 fprintf_expr e2
  in
  let fprintf_pred = fprintf_pred ~bw_ints ~consts
  and fprintf_type fmttr = fprintf_type ~bw_ints ~consts fmttr
  and fprintf_variant fmttr = fprintf_variant ~bw_ints ~consts fmttr
  and fprintf_expr fmttr = fprintf_expr ~safe ~bw_ints ~consts fmttr
  in
  let fprintf_expr_list = fprintf_list fprintf_expr ~sep:";@ " in
  function
  | Cte c -> fprintf_constant fmttr c
  | Var v ->  pr "%a" fprintf_id v
  | And (e1, e2) -> pr "@[(%a@ &&@ %a)@]" fprintf_expr e1 fprintf_expr e2
  | Or (e1, e2) -> pr "@[(%a@ ||@ %a)@]" fprintf_expr e1 fprintf_expr e2
  | Not e -> pr "@[(not@ %a)@]" fprintf_expr e
  | Void -> pr "()"
  | Deref id -> pr "!%a" fprintf_id id
  | If (e1, e2, e3) ->
    pr "@[<hov 0>(if@ %a@ @[<hov 1>then@ %a@]@ @[<hov 1>else@ %a@])@]"
      fprintf_expr e1 fprintf_expr e2 fprintf_expr e3
  | While ({ expr_node = Cte (Bool true) }, inv, var, e2) ->
    pr
      "@[<hov 0>loop@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ end@]"
      fprintf_pred inv
      fprintf_variant var
      fprintf_expr_list e2
  | While (e1, inv, var, e2) ->
    pr
      "@[<hov 0>while@ %a@ do@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ done@]"
      fprintf_expr e1
      fprintf_pred inv
      fprintf_variant var
      fprintf_expr_list e2
  | Block [] -> pr "void"
  | Block el -> pr "@[<hov 0>begin@ @[<hov 1>%a@]@ end@]" fprintf_expr_list el
  | Assign (id, e) -> pr "@[<hov 1>(%a@ :=@ %a)@]" fprintf_id id fprintf_expr e
  | Let (id, e1, e2) -> pr_let id e1 e2
  | Let_ref (id, e1, e2) ->
    pr "@[<hov 0>(let@ %a@ =@ ref@ %a@ in@ %a)@]" fprintf_id id fprintf_expr e1 fprintf_expr e2
  | App (f, ehl, ty_opt)  ->
    pr "@[<hov 1>(%a@ %a@ %a)@]"
      (fprintf_func ~where:(`Behavior safe) ~bw_ints) f
      (fprintf_expr_hlist ~safe ~bw_ints ~consts) ehl
      (fprintf_option @@ fun fmttr -> fprintf fmttr ":@ %a" fprintf_type) ty_opt
  | Raise (id, None) ->
    pr "@[<hov 1>(raise@ %s)@]" id
  | Raise (id, Some e) ->
    pr "@[<hov 1>(raise@ (%a@ %a))@]" fprintf_uid id fprintf_expr e
  | Try (e1, exc, None, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %a@ ->@ %a@ end@]" fprintf_expr e1 fprintf_uid exc fprintf_expr e2
  | Try (e1, exc, Some id, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %a@ %a@ ->@ %a@ end@]" fprintf_expr e1 fprintf_uid exc fprintf_id id fprintf_expr e2
  | Fun (params, ty, pre, body, post, diverges, signals) ->
    pr_fun params ty pre body post diverges signals
  | Triple (_, pre, e, True, []) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ (%a))@]" fprintf_pred pre fprintf_expr e
  | Triple (true, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ " fprintf_pred pre;
    pr "abstract@ ensures@ {@ %a@ }@ " fprintf_pred post;
    List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %a@ ->@ %a@ }@]" fprintf_uid e fprintf_pred r) exceps;
    pr "@ %a@ end)@]" fprintf_expr e
  | Triple (false, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ " fprintf_pred pre;
    begin match exceps with
    | [] ->
      pr "let@ _@ =@ %a@ in@ assert@ {@ %a@ }" fprintf_expr e fprintf_pred post
    | _ -> failwith "fprintf_expr_node: unsupported non-empty exceps clause in Hoare triple" (* TODO *)
    end;
    pr ")@]"
  | Assert (k, p) ->
    pr "@[<hov 0>(%s@ {@ %a@ })@]"
      (match k with `ASSERT -> "assert" | `ASSUME -> "assume" | `CHECK -> "check")
      fprintf_pred p
  | Black_box t ->
    pr "@[<hov 0>any@ %a@ @]" fprintf_type t
  | Absurd -> pr "@[<hov 0>absurd@ @]"
  | Labeled (l, e) -> pr "@[(%a%a)@]" fprintf_why_label l fprintf_expr e

and fprintf_expr : type a. safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr -> _ = fun ~safe ~bw_ints ~consts fmttr e ->
  let pr fmt = fprintf fmttr fmt in
  let rec aux =
    function
    | [] -> fprintf_expr_node ~safe ~bw_ints ~consts fmttr e.expr_node
    | s :: l ->
      pr "@[<hov 0>('%a:@ " fprintf_uid s;
      aux l;
      pr ")@]"
  in
  aux e.expr_labels

let fprintf_any_logic_type fmttr = function Logic_type t -> fprintf_logic_type fmttr t

let fprint_logic_arg fmttr (id, t) = fprintf fmttr "(%a@ :@ %a)" fprintf_id id fprintf_any_logic_type t

let fprintf_goal_kind fmttr =
  fprintf fmttr "%s" %
  function
  | KAxiom -> "axiom"
  | KLemma -> "lemma"
  | KGoal -> "goal"

let fprintf_why_id ?(constr=false) fmttr { why_name; why_expl; why_pos } =
  let pr fmt = fprintf fmttr fmt in
  pr "%a" (if not constr then fprintf_id else fprintf_uid) why_name;
  if not (Position.is_dummy why_pos) then pr "@ %a" fprintf_jc_position why_pos;
  if why_expl <> "" then pr "@ \"expl:%s\"" why_expl

let why3_builtin_locals = StringSet.singleton "result"

let fprintf_why_decl ~safe ~bw_ints ~consts fmttr (type a) (type r) { why_id; why_decl } =
  let pr fmt = fprintf fmttr fmt in
  let pr_why_id = fprintf_why_id ~constr:false
  and pr_why_uid = fprintf_why_id ~constr:true in
  let pr_args = fprintf_list ~sep:"@ " @@ fun fmt (_id, t) -> fprintf_any_logic_type fmt t in
  let fprintf_global_pred = fprintf_pred ~bw_ints ~consts:why3_builtin_locals in
  let fprintf_global_expr = fprintf_expr ~bw_ints ~consts:why3_builtin_locals in
  match (why_decl : a decl) with
  | Param t ->
    let consts =
      let rec collect_consts : type a. consts:_ -> a why_type -> _ = fun ~consts ->
        function
        | Base_type _ -> consts
        | Ref_type _ -> consts
        | Prod_type (id, t1, t2) ->
          let collect_consts' () = collect_consts ~consts:(StringSet.add id consts) t2 in
          begin match t1 with
          | Ref_type _ -> collect_consts ~consts t2
          | Base_type _ -> collect_consts' ()
          | Prod_type _ -> collect_consts' ()
          | Annot_type _ -> collect_consts' ()
          end
        | Annot_type (_, t, _, _, _, _) -> collect_consts ~consts t
      in
      collect_consts ~consts t
    in
    pr "val@ %a@ %a" pr_why_id why_id (fprintf_type ~bw_ints ~consts) t
  | Logic (args, Type (Bool, Nil)) ->
    pr "predicate@ %a@ %a" pr_why_id why_id pr_args args
  | Logic (args, t) ->
    pr "function@ %a@ %a@ :@ %a" pr_why_id why_id pr_args args fprintf_logic_type t
  | Inductive (args, cases) ->
    pr "inductive@ %a@ @[%a@]@ =@\n@[<v 0>%a@]"
      pr_why_id why_id
      pr_args args
      (fprintf_list ~sep:"@ " @@ fun _ (id, p) -> pr "|@ %a:@ @[%a@]" fprintf_id id fprintf_global_pred p) cases
  | Goal (k, p) ->
    pr "%a@ %a@ :@ %a"
      fprintf_goal_kind k
      pr_why_id why_id
      fprintf_global_pred p
  | Def e ->
    pr "let@ %a@ =@ %a"
      pr_why_id why_id
      (fprintf_global_expr ~safe) e
  | Predicate (args, p) ->
    pr "predicate@ %a@ %a@ =@ %a"
      pr_why_id why_id
      (fprintf_list ~sep:"@ " fprint_logic_arg) args
      (fprintf_pred ~bw_ints ~consts:(List.fold_right (StringSet.add % fst) args why3_builtin_locals)) p
  | Function (args, t, e) ->
    pr "function@ %a@ %a@ :@ %a =@ %a"
      pr_why_id why_id
      (fprintf_list ~sep:"@ " fprint_logic_arg) args
      fprintf_logic_type t
      (fprintf_term ~bw_ints ~consts:(List.fold_right (StringSet.add % fst) args why3_builtin_locals)) e
  | Type tvs ->
    pr "type@ %a %a" pr_why_id why_id (fprintf_list ~sep:"@ " fprintf_id) tvs
  | Exception None ->
    pr "exception@ %a" pr_why_uid why_id
  | Exception (Some t) ->
    pr "exception@ %a@ %a" pr_why_uid why_id fprintf_logic_type t

let split c s =
  try
    let pos = String.index s c in
    String.(sub s 0 pos, sub s (pos + 1) @@ length s - pos - 1)
  with
  | Not_found -> "", s

module Staged :
sig
  type 'a t
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
  | User (where, false, name) -> User (where, true, name), true
  | f -> f, false

let expand_tconstr : _ tconstr -> _ tconstr * _ =
  function
  | User (where, false, name) -> User (where, true, name), true
  | f -> f, false

let (|~>) init f = f ~init

let (%~>) f' f ~init = f ~init:(f' ~init)

module Term =
struct
  type 'a t = 'a term
  let rec fold : type a. bw_ints:_ -> f:_ -> init:_ -> a term -> _ = fun ~bw_ints ~f ->
    let fold t = fold ~bw_ints ~f t
    and fold_hlist hl = fold_hlist ~bw_ints ~f hl in
    let fold_id ~init id = f ~acc:init (`Current, id) in
    let split_fprintf f = unstage (split_fprintf ~cons:(fun th imported -> `Theory (th, imported))) f in
    fun ~init ->
    function
    | Const _ -> init
    | App (f', thl) ->
      f ~acc:init (split_fprintf (fprintf_func ~where:`Logic ~bw_ints) expand_func f') |~>
      fold_hlist thl
    | Var v -> fold_id ~init v
    | Deref v -> fold_id ~init v
    | Deref_at (v, _) -> fold_id ~init v
    | Labeled (_, t) -> fold ~init t
    | If (i, t, e) ->
      fold ~init i |~>
      fold t |~>
      fold e
    | Let (_, t1, t2) ->
      fold ~init t1 |~>
      fold t2
  and fold_hlist : type a. bw_ints:_ -> f:_ -> init:_ -> a term_hlist -> _ = fun ~bw_ints ~f ->
    let fold t = fold ~bw_ints ~f t
    and fold_hlist hl = fold_hlist ~bw_ints ~f hl in
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
  let rec fold : type a. bw_ints:_ -> f:_ -> init:_ -> a logic_type -> _ = fun ~bw_ints ~f ->
    let fold lt = fold ~bw_ints ~f lt in
    let split_fprintf f = unstage (split_fprintf ~cons:(fun th imported -> `Theory (th, imported))) f in
    fun ~init ->
    function
    | Type (tc, lthl) ->
      f ~acc:init (split_fprintf fprintf_tconstr expand_tconstr tc) |~>
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
  let rec fold ~bw_ints ~f =
    let fold = fold ~bw_ints ~f
    and fold_term t = Term.fold ~bw_ints ~f t
    and fold_term_hlist hl = Term.fold_hlist ~bw_ints ~f hl
    and fold_logic_type lt = Logic_type.fold ~bw_ints ~f lt in
    let split_fprintf f = unstage (split_fprintf ~cons:(fun th imported -> `Theory (th, imported))) f in
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
    | And (p1, p2)
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
      f ~acc:init (split_fprintf (fprintf_func ~where:`Logic ~bw_ints) expand_func p) |~>
      fold_term_hlist thl

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Why_type =
struct
  type 'a t = 'a why_type
  let rec fold : type a. bw_ints:_ -> f:_ -> init:_ -> a why_type -> _ = fun ~bw_ints ~f ->
    let fold wt = fold ~bw_ints ~f wt
    and fold_logic_type lt = Logic_type.fold ~bw_ints ~f lt
    and fold_pred = Pred.fold ~bw_ints ~f in
    fun ~init ->
    function
    | Prod_type (_, wt1, wt2) ->
      fold ~init wt1 |~>
      fold wt2
    | Base_type lt ->
      fold_logic_type ~init lt
    | Ref_type wt ->
      fold ~init wt
    | Annot_type (pre, wt, reads, writes, post, exns) ->
      fold_pred ~init pre |~>
      fold wt |~>
      let f acc name = f ~acc (`Current, name) in
      let open ListLabels in
      fold_left ~f reads %~>
      fold_left ~f writes %~>
      fold_pred post %~>
      fold_left ~f:(fun acc (name, p) -> f acc name |~> fold_pred p) exns

  let iter ~f = fold ~init:() ~f:(fun ~acc:_ -> f)
end

module Expr =
struct
  type 'a t = 'a expr
  let rec fold : type a. safe:_ -> bw_ints:_ -> f:_ -> init:_ -> a expr -> _ = fun ~safe ~bw_ints ~f ->
    let fold ~init e = fold ~safe ~bw_ints ~f ~init e
    and fold_hlist hl = fold_hlist ~safe ~bw_ints ~f hl
    and fold_pred = Pred.fold ~bw_ints ~f
    and fold_term t = Term.fold ~bw_ints ~f t
    and fold_why_type wt = Why_type.fold ~bw_ints ~f wt in
    let fold' init e = fold ~init e in
    let split_fprintf_th f = unstage (split_fprintf ~cons:(fun th imported -> `Theory (th, imported))) f in
    let split_fprintf_mod f = unstage (split_fprintf ~cons:(fun th imported -> `Module (th, imported))) f in
    fun ~init e ->
    match e.expr_node with
    | Cte _ -> init
    | Var v
    | Deref v ->
      f ~acc:init (`Current, v)
    | And (e1, e2) ->
      fold ~init e1 |~>
      fold e2
    | Or (e1, e2) ->
      fold ~init e1 |~>
      fold e2
    | Not e -> fold ~init e
    | Void -> init
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
              f ~acc @@ split_fprintf_th pp_print_string (fun s -> s, false) rel)) |~>
      ListLabels.fold_left ~f:fold' exprs
    | Block l ->
      List.fold_left fold' init l
    | Assign (v, e) ->
      f ~acc:init (`Current, v) |~>
      fold e
    | Let (_, e1, e2) ->
      fold ~init e1 |~>
      fold e2
    | Let_ref (_, e1, e2) ->
      fold ~init e1 |~>
      fold e2
    | App (f', hl, wt_opt) ->
      f ~acc:init (split_fprintf_mod (fprintf_func ~where:(`Behavior safe) ~bw_ints) expand_func f') |~>
      fold_hlist hl |~>
      Option.fold ~f:(fun init wt -> fold_why_type ~init wt) wt_opt
    | Raise (id, e_opt) ->
      f ~acc:init (`Current, id) |~>
      Option.fold ~f:fold' e_opt
    | Try (e, id, v, h) ->
      let f ~init:acc = f ~acc in
      fold ~init e |~>
      f (`Current, id) |~>
      Option.fold ~f:(fun init v -> f ~init (`Current, v)) v |~>
      fold h
    | Fun (args, rt, pre, e, post, _, exns) ->
      List.fold_left (fun init (_, Why_type t) -> fold_why_type ~init t) init args |~>
      fold_why_type rt |~>
      fold_pred pre |~>
      fold e |~>
      fold_pred post |~>
      ListLabels.fold_left ~f:(fun acc (id, p) -> f ~acc (`Current, id) |~> fold_pred p) exns
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
  and fold_hlist : type a. safe:_ -> bw_ints:_ -> f:_ -> init:_ -> a expr_hlist -> _ = fun ~safe ~bw_ints ~f ->
    let fold t = fold ~safe ~bw_ints ~f t
    and fold_hlist hl = fold_hlist ~safe ~bw_ints ~f hl in
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
    | Theory : ([`Theory], [> `Theory of string * bool | `Current]) kind
    | Module : bool -> ([`Module of bool], [> `Theory of string * bool | `Module of string * bool | `Current ]) kind

  let fold ~bw_ints (type a) (type b) (type s) ~(kind : (a, b) kind) ~(f : acc:s -> b * string -> s) =
    let fold_why_type ~f wt = Why_type.fold ~bw_ints ~f wt
    and fold_logic_type ~f t = Logic_type.fold ~bw_ints ~f t
    and fold_pred ~f = Pred.fold ~bw_ints ~f
    and fold_term ~f t = Term.fold ~bw_ints ~f t
    in
    let fold_args ~f ~init =
      List.fold_left (fun init (_, Logic_type lt) -> fold_logic_type ~f ~init lt) init
    in
    fun ~(init : s) (d : a why_decl) ->
    match d.why_decl with
    | Param wt -> let Module _ = kind in fold_why_type ~f ~init wt
    | Def e -> let Module safe = kind in Expr.fold ~safe ~bw_ints ~f ~init e
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

type 's for_any_entry = { f : 'a. 's -> 'a entry -> 's }
type 's for_any_why_decl = { f : 'a. 's -> 'a why_decl -> 's }

type 'a over =
  | Entries :
      <
        iter_entries : 'iter_entries;
        iter_decls   : _;
        iter         : 'iter_entries;
        decl_kind    : _;
        value        : any_entry;
        f            : 'state for_any_entry;
        state        : 'state
      > over
  | Decls :
      <
        iter_entries : _;
        iter_decls   : 'iter_decls;
        iter         : 'iter_decls;
        decl_kind    : 'decl_kind;
        value        : 'decl_kind why_decl;
        f            : 'state for_any_why_decl;
        state        : 'state
      > over

module Entry =
struct
  type 'kind t = 'kind entry

  module M = Map.Make (String)

  module H =
    Hashtbl.Make
      (struct
        type t = string
        let equal a b = String.compare a b = 0
        let hash = Hashtbl.hash
      end)

  let iter =
    fun (type iter) (type value) (type decl_kind) (type f) (type state)
      ~(over : <
        iter_entries : file:value list -> (entry:decl_kind entry -> (enter:state -> f:f -> unit) Staged.t) Staged.t;
        iter_decls   : entry:decl_kind entry -> (enter:state -> f:f -> unit) Staged.t;
        iter         : iter;
        decl_kind    : decl_kind;
        value        : value;
        f            : f;
        state        : state
          > over)
      ~(init : state)
      ->
        let continue :
          (state:(state * value) H.t -> entry:decl_kind entry -> (enter:state -> f:f -> unit) Staged.t) ->
          iter
          = fun continue ->
            let state : (state * value) H.t = H.create 100 in
            match over with
            | Entries ->
              fun ~file ->
                let f (type k) (e : k entry) =
                  let add name = H.add state name (init, Entry e) in
                  match e with
                  | Theory (name, _) -> add name
                | Module (name, _) -> add name
                in
                List.iter (fun (Entry e) -> f e) file;
                stage @@ continue ~state
            | Decls ->
              fun ~entry ->
                let (l : decl_kind why_decl list) =
                  match entry with
                  | Theory (_, None) -> []
                  | Module (_, None) -> []
                  | Theory (_, Some (_, decls)) -> decls
                  | Module (_, Some (_, _, decls)) -> decls
                in
                let compare_why_decls
                    { why_id = { why_name = id1; why_pos = pos1 } }
                    { why_id = { why_name = id2; why_pos = pos2 } }
                  =
                  let c = Position.compare pos1 pos2 in
                  if c <> 0 then c else compare id1 id2
                in
                List.iter
                  (fun ({ why_id = { why_name } } as d) -> H.add state why_name (init, d))
                  (List.sort compare_why_decls l);
                continue ~state ~entry
        in
        let map_ints ~how =
          let b = Buffer.create 25 in
          let b_formatter = formatter_of_buffer b in
          List.fold_left
            (fun m (Int ty as typ) ->
               fprintf_int_ty
                 ~how:(match how with `Theory -> `Theory false | `Module safe -> `Module (safe, false))
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
        let continuation ~(state : (state * value) H.t) = fun ~(entry : decl_kind entry) ->
          let bw_ints =
            let fold_decls map init =
              Why_decl.fold
                ~bw_ints:S.empty
                ~init
                ~f:(fun ~acc ->
                  function
                  | (`Theory (name, _) | `Module (name, _)), ("&" | "|^" | "^" | "~_" | "<<" | ">>" | ">>>") ->
                    begin try
                      S.add (M.find name map) acc
                    with
                    | Not_found -> acc
                    end
                  | _ -> acc)
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
            match entry with
            | Theory (_, None) -> S.empty
            | Module (_, None) -> S.empty
            | Theory (name, Some (_, decls)) ->
              memo name @@ fun () -> List.fold_left (fold_decls ~kind:Theory @@ map_ints ~how:`Theory) S.empty decls
            | Module (name, Some (_, safe, decls)) ->
              memo name @@
              fun () ->
              let map = M.fold M.add (map_ints ~how:`Theory) @@ map_ints ~how:(`Module safe) in
              List.fold_left (fold_decls ~kind:(Module safe) map) S.empty decls
          in
          stage @@
          fun ~(enter : state) ~(f : f) ->
          match over with
          | Entries ->
            let f : 'a. state -> 'a entry -> state = f.f in
            let enter acc name imported =
              try
                let s, (Entry e' as e) = H.find state name in
                if s = init then H.replace state name (enter, e);
                H.replace state name (f s e', e);
                match M.find name acc with
                | None | Some true -> acc
                | Some false when not imported -> acc
                | Some false -> M.add name (Some true) acc
                | exception Not_found -> M.add name None acc
              with
              | Not_found -> failwith ("Unrecognized Why3ML file entry: " ^ name)
            in
            let f ~name init d =
              Why_decl.fold
                ~bw_ints
                ~f:(fun ~acc ->
                  function
                  | `Current, _ -> acc
                  | `Module (name', imported), _
                  | `Theory (name', imported), _ when name' <> name ->
                    enter acc name' imported
                  | (`Module _ | `Theory _), _ -> acc)
                ~init
                d
            in
            let open Why_decl in
            begin match entry with
            | Theory (_, None) -> ()
            | Module (_, None) -> ()
            | Theory (name, Some (deps, decls)) ->
              List.fold_left
                (fun acc ->
                   function
                   | Use (_, Theory (name', _))
                   | Clone (_, Theory (name', _), _) ->
                     enter acc name' false)
                M.empty
                !deps |~>
              ListLabels.fold_left ~f:(f ~kind:Theory ~name) decls |>
              M.iter
                (fun name import ->
                   match H.find state name, import with
                   | (_, Entry (Theory _ as e)), Some import ->
                     deps := Use ((if import then `Import None else `As None), e) :: !deps
                   | _ -> ()
                   | exception Not_found -> assert false (* already checked during map initialization *))
            | Module (name, Some (deps, safe, decls)) ->
              List.fold_left
                (fun acc ->
                   fun (Dependency d) ->
                     let enter (type k) =
                       function
                       | (Theory (name', _) : k entry) -> enter acc name' false
                       | Module (name', _) -> enter acc name' false
                     in
                     match d with
                     | Use (_, e) | Clone (_, e, _) -> enter e)
                M.empty
                !deps |~>
              ListLabels.fold_left ~f:(f ~kind:(Module safe) ~name) decls |>
              M.iter
                (fun name import ->
                   let add import e =
                     deps := Dependency (Use ((if import then `Import None else `As None), e)) :: !deps
                   in
                   match H.find state name, import with
                   | (_, Entry (Theory _ as e)), Some import -> add import e
                   | (_, Entry (Module _ as e)), Some import  -> add import e
                   | _ -> ()
                   | exception Not_found -> assert false (* already checked during map initialization *))
            end
          | Decls ->
            let f : 'a. state -> 'a why_decl -> state = f.f in
            let enter name =
              try
                let s, d = H.find state name in
                if s = init then H.replace state name (enter, d);
                H.replace state name (f s d, d)
              with
              | Not_found -> ()
            in
            let f ~name d =
              Why_decl.iter
                ~bw_ints
                ~f:(function
                  | (`Module (name', _) | `Theory (name', _)), name'' when name = name' -> enter name''
                  | (`Module _ | `Theory _), _ -> ()
                  | `Current, name'' -> enter name'')
                d
            in
            let open Why_decl in
            match entry with
            | Theory (_, None) -> ()
            | Module (_, None) -> ()
            | Theory (name, Some (_, decls)) ->
              List.iter (f ~kind:Theory ~name) decls
            | Module (name, Some (_, safe, decls)) ->
              List.iter (f ~kind:(Module safe) ~name) decls
        in
        continue continuation
end

(*
(* Drop auxiliary arguments to satisfy common output interface *)
let globalize f = f ~locals:why3_builtin_locals
let fprintf_term = globalize fprintf_term
let fprintf_assertion = globalize fprintf_assertion
let fprintf_expr = globalize fprintf_expr

let pr_use fmttr f ?(import = false) ?as_ s =
  let pr fmt = fprintf fmttr fmt in
  if f then begin
    pr "use %s%s" (if import then "import " else "") s;
    Option.iter (pr " as %s") as_;
    pr "@\n@\n"
  end
and import = true

let fprintf_why3_imports ?float_model fmttr d =
  let pr = pr_use fmttr in
  pr ~import true "int.Int";
  pr         true "bool.Bool";
  pr         d.why3_IntMinMax         ~as_:"IntMinMax"  "int.MinMax";
  pr         d.why3_ComputerDivision                    "int.ComputerDivision";
  pr ~import d.why3_reals                               "real.RealInfix";
  pr         d.why3_FromInt                             "real.FromInt";
  pr         d.why3_Truncate                            "real.Truncate";
  pr         d.why3_Square                              "real.Square";
  pr         d.why3_Power                               "int.Power";
  pr         d.why3_PowerInt                            "real.PowerInt";
  pr         d.why3_PowerReal                           "real.PowerReal";
  pr         d.why3_RealMinMax        ~as_:"RealMinMax" "real.MinMax";
  pr         d.why3_AbsInt            ~as_:"AbsInt"     "int.Abs";
  pr         d.why3_AbsReal           ~as_:"AbsReal"    "real.Abs";
  pr         d.why3_ExpLog                              "real.ExpLog";
  pr         d.why3_Trigonometry                        "real.Trigonometry";
  begin match float_model with
  | Some Env.FMfull ->
    pr ~import true ~as_:"Single" "floating_point.SingleFull";
    pr ~import true ~as_:"Double" "floating_point.DoubleFull"
  | Some Env.FMdefensive ->
    pr ~import true ~as_:"Single" "floating_point.Single";
    pr ~import true ~as_:"Double" "floating_point.Double"
  | Some Env.FMmultirounding ->
    pr ~import true ~as_:"Double" "floating_point.DoubleMultiRounding"
  | Some Env.FMmath ->
    failwith "unsupported \"math\" floating-point model" (* TODO *)
  | None -> ()
  end;
  pr ~import true                                       "jessie3theories.Jessie_memory_model"

let fprintf_why_decls ?float_model fmttr decls =
  let deps = empty_why3_dependencies in
  List.iter (iter_why_decl @@ add_why3_dependencies deps) decls;
  (* Partitioning -- needed due to possible name clashes (from different Why3ML scopes) *)
  let types, params, defs, others =
    List.fold_left
      (fun (t, p, d, o) ->
         function
         | Type _ as t'   ->   t' :: t, p,         d,         o
         | Exception _
         | Param _  as p' ->   t,       p' :: p,   d,         o
         | Def _ as d'    ->   t,       p,         d' :: d,   o
         | _ as o'        ->   t,       p,         d,         o' :: o)
      ([], [], [], [])
      decls
  in
  let pr fmt = fprintf fmttr fmt in
  let pr_use = pr_use fmttr true in
  pr "theory Jessie_model@\n@\n";
  fprintf_why3_imports ?float_model fmttr deps;
  pr_use ~import "jessie3_integer.Integer";
  output_decls get_why_id iter_why_decl (fprintf_why_decl fmttr) types;
  output_decls get_why_id iter_why_decl (fprintf_why_decl fmttr) others;
  pr "end@\n@\n";
  pr "module Jessie_program@\n@\n";
  fprintf_why3_imports ?float_model fmttr deps;
  pr_use ~import "Jessie_model";
  pr_use ~import "ref.Ref";
  pr_use ~import "jessie3.JessieDivision";
  Option.iter (fun _ ->
    pr_use ~import "floating_point.Rounding")
    float_model;
  begin match float_model with
  | Some Env.FMfull ->
    pr_use ~import "jessie3.JessieFloatsFull"
  | Some Env.FMdefensive ->
    pr_use ~import "jessie3.JessieFloats"
  | Some Env.FMmultirounding ->
    pr_use ~import "jessie3.JessieFloatsMultiRounding"
  | Some Env.FMmath -> failwith "unsupported \"math\" floating-point model" (* TODO *)
  | None -> ()
  end;
  pr_use ~import "jessie3.Jessie_memory_model_parameters";
  pr_use ~import "jessie3_integer.Integer";
  output_decls get_why_id iter_why_decl (fprintf_why_decl fmttr) params;
  output_decls get_why_id iter_why_decl (fprintf_why_decl fmttr) defs;
  pr "end@\n@\n"

let print_to_file = print_to_file (fun f -> f ^ ".mlw") fprintf_vc_kind fprintf_why_decls

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_why3_output.ml"
  End:
*)
*)
