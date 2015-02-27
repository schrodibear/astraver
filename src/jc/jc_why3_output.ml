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

type any_integer = Int : ('r, 's) integer -> any_integer

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
    fprintf fmttr " %a" fprintf_logic_type lt;
    fprintf_ltype_hlist fmttr ts

and fprintf_logic_type : type a. _ -> a logic_type -> _ = fun fmttr ->
  function
  | Type (c, tps) ->
    fprintf fmttr "%a%a" fprintf_tconstr c fprintf_ltype_hlist tps

let why3_builtin_locals = StringSet.singleton "result"

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
  let pr fmt = fprintf fmttr fmt in
  let fprintf_term fmttr = fprintf_term ~bw_ints ~consts fmttr
  and fprintf_pred = fprintf_pred ~bw_ints ~consts
  in
  let fprintf_pat fmttr =
    function
    | Term t -> fprintf_term fmttr t
    | Pred p -> fprintf_pred fmttr p
  in
  let rec fprintf_pats fmttr =
    function
    | [] -> ()
    | [p] -> pr "%a" fprintf_pat p
    | p :: ps ->
      pr "%a,@ " fprintf_pat p;
      fprintf_pats fmttr ps
  in
  let rec fprintf_alts fmttr =
    function
    | [] -> ()
    | [p] -> pr "%a" fprintf_pats p
    | p :: ps ->
      pr "%a@ |@ " fprintf_pats p;
      fprintf_alts fmttr ps
  in
  fprintf_alts fmttr
(*
let rec fprintf_type ~locals ~need_colon anon fmttr t =
  let pr fmt = fprintf fmttr fmt in
  let fprintf_assertion = fprintf_assertion ~locals in
  let pt = fprintf_type ~locals ~need_colon:false anon in
  begin match t with
    | Prod_type _ -> ()
    | _ when need_colon -> pr ":@ "
    | _ -> ()
  end;
  match t with
  | Prod_type (id, t1, t2) ->
    let id = if id = "" || anon then "_anonymous" else id in
    pr "@[<hov 1>(%s@ :@ %a)@ %a@]" (why3_ident id) pt t1 (fprintf_type ~locals ~need_colon anon) t2
  | Base_type t -> fprintf_logic_type fmttr t
  | Ref_type t -> pr "ref@ %a" pt t
  | Annot_type (p, t, reads, writes, q, signals) ->
    pr "%a@ " pt t;
    pr "@[@[<hov 2>requires@ {@ %a@ }@]@ " fprintf_assertion p;
    let print_ids = print_list comma @@ fun _ -> pr "%s" % why3_ident in
    begin match List.sort compare reads with
    | [] -> ()
    | reads ->
      pr "reads@ {@ %a@ }@ " print_ids reads
    end;
    begin match List.sort compare writes with
      | [] -> ()
      | writes ->
        pr "writes@ {@ %a@ }@ " print_ids writes
    end;
    pr "@[<hov 2>ensures@ {@ %a@ }@]" fprintf_assertion q;
    begin match signals with
      | [] -> pr "@]"
      | l ->
        pr "@ ";
        List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %s@ result@ ->@ %a@ }@]@]" e fprintf_assertion r) l
    end

let fprintf_variant ~locals fmttr =
  let pr fmt = fprintf fmttr fmt in
  function
  | None -> ()
  | Some (t, r_opt) ->
    pr "variant@ {@ %a@ }" (fprintf_term ~locals) t;
    Option.iter (pr "@ with@ %s") r_opt

let rec fprintf_expr_node ~locals in_app fmttr =
  let pr fmt = fprintf fmttr fmt in
  let pr_fun params pre body post diverges signals =
    let locals = List.fold_right (function _, Ref_type _ -> Fn.id | x, _ -> StringSet.add x) params locals in
    let fprintf_assertion = fprintf_assertion ~locals in
    pr "@[<hov 1>fun@ @[";
    List.iter (fun (x, t) -> pr "(%s@ :@ %a)@ " (why3_id x) (fprintf_type ~locals ~need_colon:false false) t) params;
    pr "@]@ ->@ @[<hov 0>requires@ {@ %a@ }@ " fprintf_assertion pre;
    begin match signals with
    | [] -> pr "@[<hov 2>ensures@ {@ %a@ }@]@]@ " fprintf_assertion post
    | l ->
      pr "@[<hov 2>ensures@ {@ %a@ }@ %a@]@ "
        fprintf_assertion post
        (print_list alt @@
         fun _ (e, r) ->
         pr "@[<hov 2>raises@ {@ %s@ result@ ->@ %a@ }@]" e fprintf_assertion r)
        l
    end;
    if diverges then pr "diverges@ ";
    pr "%a@]" (fprintf_expr ~locals) body
  in
  let pr_let id e1 e2 =
    let locals = StringSet.add id locals in
    let fprintf_expr = fprintf_expr ~locals in
    pr "@[<hov 0>(let@ %s@ =@ %a@ in@ %a)@]" (why3_id id) fprintf_expr e1 fprintf_expr e2
  in
  let fprintf_assertion = fprintf_assertion ~locals
  and fprintf_type = fprintf_type ~locals
  and fprintf_variant = fprintf_variant ~locals
  and fprintf_expr = fprintf_expr ~locals
  and fprintf_expr_gen = fprintf_expr_gen ~locals
  and fprintf_expr_list = fprintf_expr_list ~locals
  in
  function
  | Cte c -> fprintf_constant fmttr c
  | Var id ->  pr "%s" (why3_param id)
  | And (e1, e2) -> pr "@[(%a@ &&@ %a)@]" fprintf_expr e1 fprintf_expr e2
  | Or (e1, e2) -> pr "@[(%a@ ||@ %a)@]" fprintf_expr e1 fprintf_expr e2
  | Not e1 -> pr "@[(not@ %a)@]" fprintf_expr e1
  | Void -> pr "()"
  | Deref id -> pr "!%s" (why3_id id)
  | If (e1, e2, e3) ->
    pr "@[<hov 0>(if@ %a@ @[<hov 1>then@ %a@]@ @[<hov 1>else@ %a@])@]"
      fprintf_expr e1 fprintf_expr e2 fprintf_expr e3
  | While({ expr_node = Cte (Prim_bool true) }, inv, var, e2) ->
    pr
      "@[<hov 0>loop@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ end@]"
      fprintf_assertion inv
      fprintf_variant var
      fprintf_expr_list e2
  | While (e1, inv, var, e2) ->
    pr
      "@[<hov 0>while@ %a@ do@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ done@]"
      fprintf_expr e1
      fprintf_assertion inv
      fprintf_variant var
      fprintf_expr_list e2
  | Block [] -> pr "void"
  | Block el -> pr "@[<hov 0>begin@ @[<hov 1>%a@]@ end@]" fprintf_expr_list el
  | Assign (id, e) -> pr "@[<hov 1>(%s@ :=@ %a)@]" (why3_id id) fprintf_expr e
  | Let (id, e1, e2) ->
    pr_let id e1 e2
  | Let_ref (id, e1, e2) ->
    pr "@[<hov 0>(let@ %s@ =@ ref@ %a@ in@ %a)@]" (why3_id id) fprintf_expr e1 fprintf_expr e2
  | App ({ expr_node = App ({ expr_node = Var id }, e1, _) }, e2, _) when  is_why3_poly_eq id ->
    pr "@[<hov 1>(%a@ =@ %a)@]" fprintf_expr e1 fprintf_expr e2
  | App({ expr_node = App ({ expr_node = Var id }, e1, _)}, e2, _) when is_why3_poly_neq id ->
    pr "@[<hov 1>(%a@ <>@ %a)@]" fprintf_expr e1 fprintf_expr e2
  | App (e1, e2, _) when in_app ->
    pr "@[<hov 1>%a@ %a@]" (fprintf_expr_gen true) e1 fprintf_expr e2
  | App (e1, e2, ty)  ->
    pr "@[<hov 1>(%a@ %a@ %a)@]"
      (fprintf_expr_gen true) e1 fprintf_expr e2
      (print_option @@ fprintf_type ~need_colon:true false) ty
  | Raise (id, None) ->
    pr "@[<hov 1>(raise@ %s)@]" id
  | Raise (id, Some e) ->
    pr "@[<hov 1>(raise@ (%s@ %a))@]" id fprintf_expr e
  | Try (e1, exc, None, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %s@ ->@ %a@ end@]" fprintf_expr e1 exc fprintf_expr e2
  | Try (e1, exc, Some id, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %s@ %s@ ->@ %a@ end@]" fprintf_expr e1 exc id fprintf_expr e2
  | Fun (params, pre, body, post, diverges, signals) ->
    pr_fun params pre body post diverges signals
  | Triple (_, pre, e, LTrue, []) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ (%a))@]" fprintf_assertion pre fprintf_expr e
  | Triple (true, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ " fprintf_assertion pre;
    pr "abstract@ ensures@ {@ %a@ }@ " fprintf_assertion post;
    List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %s@ ->@ %a@ }@]" e fprintf_assertion r) exceps;
    pr "@ %a@ end)@]" fprintf_expr e
  | Triple (false, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ " fprintf_assertion pre;
    begin match exceps with
    | [] ->
      pr "let@ _@ =@ %a@ in@ assert@ {@ %a@ }" fprintf_expr e fprintf_assertion post
    | _ -> failwith "fprintf_expr_node: unsupported non-empty exceps clause in Hoare triple" (* TODO *)
    end;
    pr ")@]"
  | Assert (k, p, e) ->
    pr "@[<hov 0>(%s@ {@ %a@ };@ %a)@]"
      (match k with `ASSERT -> "assert" | `ASSUME -> "assume" | `CHECK -> "check")
      fprintf_assertion p fprintf_expr e
  | BlackBox t ->
    pr "@[<hov 0>any@ %a@ @]" (fprintf_type ~need_colon:false false) t
  | Absurd -> pr "@[<hov 0>absurd@ @]"
  | Labeled (l, e) -> pr "@[(%a%a)@]" fprintf_why_label l fprintf_expr e

and fprintf_expr_gen ~locals in_app fmttr e =
  let pr fmt = fprintf fmttr fmt in
  let rec aux =
    function
    | [] -> fprintf_expr_node ~locals in_app fmttr e.expr_node
    | s :: l ->
      pr "@[<hov 0>('%s:@ " @@ why3_constr s;
      aux l;
      pr ")@]"
  in
  aux e.expr_labels

and fprintf_expr ~locals e = fprintf_expr_gen ~locals false e

and fprintf_expr_list' ~locals ~next fmttr =
  function
  | [] -> ()
  | e :: l ->
    fprintf fmttr (if next then ";@ %a" else "%a") (fprintf_expr ~locals) e;
    fprintf_expr_list' ~locals ~next:true fmttr l

and fprintf_expr_list ~locals fmttr l = fprintf_expr_list' ~locals ~next:false fmttr l


let fprint_logic_arg fmttr (id, t) = fprintf fmttr "(%s@ :@ %a)" (why3_ident id) fprintf_logic_type t

let string_of_goal_kind =
  function
  | KAxiom -> "axiom"
  | KLemma -> "lemma"
  | KGoal -> "goal"

let fprintf_why_id ?(constr = false) fmttr { why_name; why_expl; why_pos } =
  let pr fmt = fprintf fmttr fmt in
  pr "%s" @@ (if not constr then why3_ident else why3_constr) why_name;
  if not (Position.is_dummy why_pos) then pr "@ %a" fprintf_jc_position why_pos;
  if why_expl <> "" then pr "@ \"expl:%s\"" why_expl

let fprintf_why_decl fmttr =
  let pr fmt = fprintf fmttr fmt in
  let ext b = if b then "external@ " else "" in
  let pr_id = fprintf_why_id ~constr:false
  and pr_constr = fprintf_why_id ~constr:true in
  let pr_args = print_list space @@ fun fmt (_id, t) -> fprintf_logic_type fmt t in
  let fprintf_global_assertion = fprintf_assertion ~locals:why3_builtin_locals in
  let fprintf_global_expr = fprintf_expr ~locals:why3_builtin_locals in
  function
  | Param (b, id, t)  ->
    let locals =
      let rec collect_locals ~locals =
        function
        | Base_type _ | Ref_type _ -> locals
        | Prod_type (id, t1, t2) ->
          begin match t1 with
          | Ref_type _ -> collect_locals ~locals t2
          | Base_type _ | Prod_type _ | Annot_type _ -> collect_locals ~locals:(StringSet.add id locals) t2
          end
        | Annot_type (_, t, _, _, _, _) -> collect_locals ~locals t
      in
      collect_locals ~locals:why3_builtin_locals t
    in
    pr "@[<hov 1>%sval@ %a@ %a@]@.@." (ext b) pr_id id (fprintf_type ~locals ~need_colon:true false) t
  | Logic (b, id, args, t) when is_prop t ->
    pr "@[<hov 1>%spredicate@ %a@ %a@ @.@."
      (ext b) pr_id id pr_args args
  | Logic (b, id, args, t) ->
    pr "@[<hov 1>%sfunction@ %a@ %a@ :@ %a@.@."
      (ext b) pr_id id  pr_args args fprintf_logic_type t
  | Inductive (b, id, args, cases) ->
    pr "@[<hov 1>%sinductive@ %a@ @[%a@]@ =@\n@[<v 0>%a@]@\n@."
      (ext b)
      pr_id id pr_args args
      (print_list newline @@ fun _ (id, a) -> pr "|@ %s:@ @[%a@]" id fprintf_global_assertion a) cases
  | Goal (k, id, p)  ->
    pr "@[<hov 1>%s@ %a@ :@ %a@]@.@."
      (string_of_goal_kind k)
      pr_id id
      fprintf_global_assertion p
  | Def (id, e)  ->
    pr "@[<hov 1>let@ %a@ =@ %a@]@.@."
      pr_id id
      fprintf_global_expr e
  | Predicate (b, id, args, p) ->
    pr "@[<hov 1>%spredicate@ %a@ %a@ =@ %a@]@.@."
      (ext b)
      pr_id id
      (print_list space fprint_logic_arg) args
      (fprintf_assertion ~locals:(List.fold_right (StringSet.add % fst) args why3_builtin_locals)) p
  | Function (b, id, args, t, e) ->
    pr "@[<hov 1>%sfunction@ %a@ %a@ :@ %a =@ %a@]@.@."
      (ext b)
      pr_id id
      (print_list space fprint_logic_arg) args
      fprintf_logic_type t
      (fprintf_term ~locals:(List.fold_right (StringSet.add % fst) args why3_builtin_locals)) e
  | Type (id, [])  ->
    pr "@[type@ %s@]@.@." (why3_ident id.why_name)
  | Type (id, [t]) ->
    pr "@[type@ '%s@ %s@]@.@." t (why3_ident id.why_name)
  | Type (id, t :: l) ->
    pr "@[type@ ('%s" t;
    List.iter (pr ",@ '%s") l;
    pr ")@ %s@]@.@." (why3_ident id.why_name)
  | Exception (id, None) ->
    pr "@[exception@ %a@]@.@." pr_constr id
  | Exception (id, Some t) ->
    pr "@[exception@ %a@ %a@]@.@." pr_constr id fprintf_logic_type t

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
