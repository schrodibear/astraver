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

open Stdlib
open Envset

open Output_ast
module O = Output

let constant fmttr (type a) =
  let pr fmt = fprintf fmttr fmt in
  function
  | (Void : a constant) -> pr "()"
  | Int n -> pr "(%s)" n
  | Real f -> pr "%s" f
  | Bool true -> pr "Bool.True"
  | Bool false -> pr "Bool.False"

let id fmttr id =
  fprintf fmttr "%s" @@
  match id.[0] with
  | 'A' .. 'Z' -> "_" ^ id
  | _ when Why3_kw.is_why3_keyword id -> id ^ "_why3"
  | _ -> id

let uid fmttr uid =
  fprintf fmttr "%s" @@
  match uid.[0] with
  | 'A' .. 'Z' -> uid
  | 'a' .. 'z' -> String.capitalize uid
  | _ -> "U_" ^ uid

let int_ty ~how fmttr (type r) (type b) (ty : (r repr, b bit) xintx bounded integer) =
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

let enum_ty ~how fmttr (Enum name) =
  let pr fmt = fprintf fmttr fmt in
  match how with
  | `Name -> pr "%s" name
  | `Theory -> pr "%a" uid name
  | `Module false -> pr "%s" ("Unsafe_" ^ name)
  | `Module true -> pr "%s" ("Safe_" ^ name)

let modulo fmttr modulo =
  fprintf fmttr "%s" @@
  match modulo with
  | true -> "%"
  | false -> ""

let op fmttr op =
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

let func ~where ~bw_ints fmttr (type a) (type b) =
  let pr fmt = fprintf fmttr fmt in
  let pr_bop fp ty = pr "%a.(%a%a)" fp ty in
  let pr_uop fp ty = pr "%a.(%a%a_)" fp ty in
  let pr_f fp ty = pr "%a.%s" fp ty in
  let int_ty fmttr ty =
    int_ty
      ~how:
        (match where, S.mem (Int ty) bw_ints with
         | `Logic, bit -> `Theory bit
         | `Behavior safe, bit -> `Module (safe, bit))
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
  function
  | (B_int_op op' : (a, b) func) -> pr "Int.(%a)" op op'
  | U_int_op op' -> pr "Int.(%a_)" op op'
  | B_bint_op (op', (Int _ as ty), modulo') ->
    pr_bop int_ty ty op op' modulo modulo'
  | B_bint_op (op', (Enum _ as ty), modulo') ->
    pr_bop enum_ty ty op op' modulo modulo'
  | U_bint_op (op', (Int _ as ty), modulo') ->
    pr_uop int_ty ty op op' modulo modulo'
  | U_bint_op (op', (Enum _ as ty), modulo') ->
    pr_uop enum_ty ty op op' modulo modulo'
  | Of_int (Int _ as ty) -> pr_f int_ty ty "of_int"
  | Of_int (Enum _ as ty) -> pr_f enum_ty ty "of_int"
  | To_int (Int _ as ty) -> pr_f int_ty ty "to_int"
  | To_int (Enum _ as ty) -> pr_f enum_ty ty "to_int"
  | B_bint_bop (op', ty) -> pr_bop int_ty ty op op' modulo false
  | U_bint_bop (op', ty) -> pr_uop int_ty ty op op' modulo false
  | Lsl_bint (ty, modulo') -> pr_bop int_ty ty op `Lsl modulo modulo'
  | B_num_pred (pred, Integral Integer) -> pr "%a" op pred
  | B_num_pred (pred, Integral (Int _ as ty)) -> pr_bop int_ty ty op pred modulo false
  | B_num_pred (pred, Integral (Enum _ as ty)) -> pr_bop enum_ty ty op pred modulo false
  | Poly op' -> pr "%a" op op'
  | User (_, false, name) -> pr "%a" id name
  | User (where, true, name) -> pr "%a.%a" uid where id name
  | To_float _ -> fail_on_real ()
  | Of_float _  -> fail_on_real ()
  | B_num_pred (_, Real _) -> fail_on_real ()

let vc_kind fmttr k =
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

let tconstr fmttr (type a) (type b) =
  let pr fmt = fprintf fmttr fmt in
  function
  | (Numeric (Integral Integer) : (a, b) tconstr) -> pr "int"
  | Numeric (Integral (Int _  as ty)) -> pr "%a.t" (int_ty ~how:(`Theory false)) ty
  | Numeric (Integral (Enum _  as ty)) -> pr "%a.t" (enum_ty ~how:`Theory) ty
  | Numeric (Real _) -> fail_on_real ()
  | Bool -> pr "Bool.bool"
  | Void -> pr "()"
  | Var v -> pr "'%a" id v
  | User (_, false, name) -> pr "%a" id name
  | User (where, true, name) -> pr "%a.%a" uid where id name

let rec ltype_hlist : type a. _ -> a ltype_hlist -> _  = fun fmttr ->
  function
  | Nil -> ()
  | Cons (lt, ts) ->
    fprintf fmttr "@ %a" logic_type lt;
    ltype_hlist fmttr ts

and logic_type : type a. _ -> a logic_type -> _ = fun fmttr ->
  function
  | Type (c, tps) ->
    fprintf fmttr "%a%a" tconstr c ltype_hlist tps

let rec term_hlist : type a. bw_ints:_ -> consts:_ -> _ -> a term_hlist -> _ = fun ~bw_ints ~consts fmttr ->
  function
  | Nil -> ()
  | Cons (t, ts) ->
    fprintf fmttr "@ %a" (term ~bw_ints ~consts) t;
    term_hlist ~bw_ints ~consts fmttr ts

and term : type a. bw_ints: _ -> consts:_ -> _ -> a term -> _ = fun ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let term_hlist fmttr = term_hlist ~bw_ints ~consts fmttr
  and term fmttr = term ~bw_ints ~consts fmttr
  and func fmttr = func ~where:`Logic ~bw_ints fmttr
  in
  function
  | Const c -> constant fmttr c
  | App (f, Nil) -> pr "%a" func f
  | App (f, (Cons _ as ts)) ->
    pr "@[(%a%a)@]" func f term_hlist ts
  | Var v -> pr "%a" id v
  | Deref v | Deref_at (v, _) when StringSet.mem v consts ->
    pr "%a" id v
  | Deref v -> pr "!%a" id v
  | Deref_at (v, "") -> pr "(old@ !%a)" id v
  | Deref_at (v, l) -> pr "(at@ !%a@ '%a)" id v uid l
  | Labeled (l, t) ->
    pr "(%a%a)" why_label l term t
  | If (t1, t2, t3) ->
    pr "@[<hov 1>(if@ %a@ then@ %a@ else@ %a)@]"
      term t1 term t2 term t3
  | Let (v, t1, t2) ->
    pr "@[<hov 1>(let@ %a@ =@ %a@ in@ %a)@]"
      id v term t1 term t2

let rec list element ~sep fmttr =
  function
  | [] -> ()
  | [x] -> element fmttr x
  | x :: xs ->
    fprintf fmttr "%a%( fmt %)" element x sep;
    list element ~sep fmttr xs

let rec pred ~bw_ints ~consts fmttr =
  let pr fmt = fprintf fmttr fmt in
  let term_hlist fmttr = term_hlist ~bw_ints ~consts fmttr
  and term fmttr = term ~bw_ints ~consts fmttr
  and pred = pred ~bw_ints ~consts
  and triggers = triggers ~bw_ints ~consts
  and func fmttr = func ~where:`Logic ~bw_ints fmttr
  in
  function
  | True -> pr "true"
  | False -> pr "false"
  | And (p1, p2) ->
    pr "@[(%a@ /\\@ %a)@]" pred p1 pred p2
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
    pr "@[<hov 1>(forall@ %a:@,%a@,%a@,.@ %a)@]"
      id v logic_type t triggers trigs pred p
  | Exists (v, t, trigs, p) ->
    pr "@[<hov 1>(exists@ %a:%a%a.@ %a)@]"
      id v logic_type t triggers trigs pred p
  | App (f, Nil) -> pr "%a" func f
  | App (f, (Cons _ as ts)) ->
    pr "@[(%a%a)@]" func f term_hlist ts
  | Labeled (l, p) ->
    pr "@[(%a%a)@]" why_label l pred p

and triggers ~bw_ints ~consts fmttr =
  let term fmttr = term ~bw_ints ~consts fmttr
  and pred = pred ~bw_ints ~consts
  in
  let pat fmttr =
    function
    | Term t -> term fmttr t
    | Pred p -> pred fmttr p
  in
  list ~sep:"@ |@ " (list pat ~sep:",@ ") fmttr

let rec why_type : type a. bw_ints:_ -> consts:_ -> _ -> a why_type -> _ = fun ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let pred = pred ~bw_ints ~consts in
  let why_type fmttr = why_type ~bw_ints ~consts fmttr in
  function
  | Prod_type (id', t1, t2) ->
    let id' = if id' = "" then "_" else id' in
    pr "@[<hov 1>(%a@ :@ %a)@ %a@]" id id' why_type t1 why_type t2
  | Base_type t -> logic_type fmttr t
  | Ref_type t -> pr "ref@ %a" why_type t
  | Annot_type (p, t, reads, writes, q, signals) ->
    pr "%a@ " why_type t;
    pr "@[@[<hov 2>requires@ {@ %a@ }@]" pred p;
    let ids = list id ~sep:",@ "  in
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
    pr "@[<hov 2>ensures@ {@ %a@ }@]" pred q;
    begin match signals with
      | [] -> pr "@]"
      | l ->
        pr "@ ";
        List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %s@ result@ ->@ %a@ }@]@]" e pred r) l
    end

let variant ~bw_ints ~consts fmttr =
  let pr fmt = fprintf fmttr fmt in
  function
  | None -> ()
  | Some (t, r_opt) ->
    pr "variant@ {@ %a@ }" (term ~bw_ints ~consts) t;
    Option.iter (pr "@ with@ %s") r_opt

let option value fmttr =
  function
  | None -> ()
  | Some v ->
    value fmttr v

let any_type ~bw_ints ~consts fmttr = function Why_type t -> why_type ~bw_ints ~consts fmttr t

let rec expr_hlist : type a. safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr_hlist -> _ =
  fun ~safe ~bw_ints ~consts fmttr ->
  function
  | Nil -> ()
  | Cons (e, es) ->
    fprintf fmttr "@ %a" (expr ~safe ~bw_ints ~consts) e;
    expr_hlist ~safe ~bw_ints ~consts fmttr es

and expr_node : type a. safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr_node -> _ =
  fun ~safe ~bw_ints ~consts fmttr ->
  let pr fmt = fprintf fmttr fmt in
  let pr_fun params ty pre body post diverges signals =
    let consts = List.fold_right (function _, Why_type (Ref_type _) -> Fn.id | x, _ -> StringSet.add x) params consts in
    let pred = pred ~bw_ints ~consts
    and why_type fmttr = why_type ~bw_ints ~consts fmttr
    and any_type = any_type ~bw_ints ~consts
    in
    pr "@[<hov 1>fun@ @[";
    List.iter (fun (x, t) -> pr "(%a@ :@ %a)@ " id x any_type t) params;
    pr ":@ %a"  why_type ty;
    pr "@]@ ->@ @[<hov 0>requires@ {@ %a@ }@ " pred pre;
    begin match signals with
    | [] -> pr "@[<hov 2>ensures@ {@ %a@ }@]@]@ " pred post
    | l ->
      pr "@[<hov 2>ensures@ {@ %a@ }@ %a@]@ "
        pred post
        (list ~sep:"" @@
         fun _ (e, r) ->
         pr "@[<hov 2>raises@ {@ %a@ result@ ->@ %a@ }@]" uid e pred r)
        l
    end;
    if diverges then pr "diverges@ ";
    pr "%a@]" (expr ~safe ~bw_ints ~consts) body
  in
  let pr_let id' e1 e2 =
    let consts = StringSet.add id' consts in
    let expr fmttr = expr ~safe ~bw_ints ~consts fmttr in
    pr "@[<hov 0>(let@ %a@ =@ %a@ in@ %a)@]" id id' expr e1 expr e2
  in
  let pred = pred ~bw_ints ~consts
  and why_type fmttr = why_type ~bw_ints ~consts fmttr
  and variant fmttr = variant ~bw_ints ~consts fmttr
  and expr fmttr = expr ~safe ~bw_ints ~consts fmttr
  in
  let expr_list = list expr ~sep:";@ " in
  function
  | Cte c -> constant fmttr c
  | Var v ->  pr "%a" id v
  | And (e1, e2) -> pr "@[(%a@ &&@ %a)@]" expr e1 expr e2
  | Or (e1, e2) -> pr "@[(%a@ ||@ %a)@]" expr e1 expr e2
  | Not e -> pr "@[(not@ %a)@]" expr e
  | Void -> pr "()"
  | Deref id' -> pr "!%a" id id'
  | If (e1, e2, e3) ->
    pr "@[<hov 0>(if@ %a@ @[<hov 1>then@ %a@]@ @[<hov 1>else@ %a@])@]"
      expr e1 expr e2 expr e3
  | While ({ expr_node = Cte (Bool true) }, inv, var, e2) ->
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
  | Block [] -> pr "void"
  | Block el -> pr "@[<hov 0>begin@ @[<hov 1>%a@]@ end@]" expr_list el
  | Assign (id', e) -> pr "@[<hov 1>(%a@ :=@ %a)@]" id id' expr e
  | Let (id, e1, e2) -> pr_let id e1 e2
  | Let_ref (id', e1, e2) ->
    pr "@[<hov 0>(let@ %a@ =@ ref@ %a@ in@ %a)@]" id id' expr e1 expr e2
  | App (f, ehl, ty_opt)  ->
    pr "@[<hov 1>(%a@ %a@ %a)@]"
      (func ~where:(`Behavior safe) ~bw_ints) f
      (expr_hlist ~safe ~bw_ints ~consts) ehl
      (option @@ fun fmttr -> fprintf fmttr ":@ %a" why_type) ty_opt
  | Raise (id, None) ->
    pr "@[<hov 1>(raise@ %s)@]" id
  | Raise (id, Some e) ->
    pr "@[<hov 1>(raise@ (%a@ %a))@]" uid id expr e
  | Try (e1, exc, None, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %a@ ->@ %a@ end@]" expr e1 uid exc expr e2
  | Try (e1, exc, Some id', e2) ->
    pr "@[<hov 1>try@ %a@ with@ %a@ %a@ ->@ %a@ end@]" expr e1 uid exc id id' expr e2
  | Fun (params, ty, pre, body, post, diverges, signals) ->
    pr_fun params ty pre body post diverges signals
  | Triple (_, pre, e, True, []) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ (%a))@]" pred pre expr e
  | Triple (true, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert@ {@ %a@ };@ " pred pre;
    pr "abstract@ ensures@ {@ %a@ }@ " pred post;
    List.iter (fun (e, r) -> pr "@[<hov 2>raises@ {@ %a@ ->@ %a@ }@]" uid e pred r) exceps;
    pr "@ %a@ end)@]" expr e
  | Triple (false, pre, e, post, exceps) ->
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

and expr : type a. safe:_ -> bw_ints:_ -> consts:_ -> _ -> a expr -> _ = fun ~safe ~bw_ints ~consts fmttr e ->
  let pr fmt = fprintf fmttr fmt in
  let rec aux =
    function
    | [] -> expr_node ~safe ~bw_ints ~consts fmttr e.expr_node
    | s :: l ->
      pr "@[<hov 0>('%a:@ " uid s;
      aux l;
      pr ")@]"
  in
  aux e.expr_labels

let any_logic_type fmttr = function Logic_type t -> logic_type fmttr t

let logic_arg fmttr (id', t) = fprintf fmttr "(%a@ :@ %a)" id id' any_logic_type t

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
  | Theory : [`Theory] kind
  | Module : bool -> [`Module of bool] kind

let why_decl (type k) ~(kind : k kind) ~bw_ints ~consts fmttr { why_id = why_id'; why_decl } =
  let pr fmt = fprintf fmttr fmt in
  let why_id = why_id ~constr:false
  and why_uid = why_id ~constr:true in
  let args = list ~sep:"@ " @@ fun fmt (_id, t) -> any_logic_type fmt t in
  let pred = pred ~bw_ints in
  let expr = expr ~bw_ints in
  match (why_decl : k decl) with
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
    pr "val@ %a@ %a" why_id why_id' (why_type ~bw_ints ~consts) t
  | Logic (args', Type (Bool, Nil)) ->
    pr "predicate@ %a@ %a" why_id why_id' args args'
  | Logic (args', t) ->
    pr "function@ %a@ %a@ :@ %a" why_id why_id' args args' logic_type t
  | Inductive (args', cases) ->
    pr "inductive@ %a@ @[%a@]@ =@\n@[<v 0>%a@]"
      why_id why_id'
      args args'
      (list ~sep:"@ " @@ fun _ (id', p) -> pr "|@ %a:@ @[%a@]" id id' (pred ~consts) p) cases
  | Goal (k, p) ->
    pr "%a@ %a@ :@ %a"
      goal_kind k
      why_id why_id'
      (pred ~consts) p
  | Def e ->
    let Module safe = kind in
    pr "let@ %a@ =@ %a"
      why_id why_id'
      (expr ~consts ~safe) e
  | Predicate (args, p) ->
    pr "predicate@ %a@ %a@ =@ %a"
      why_id why_id'
      (list ~sep:"@ " logic_arg) args
      (pred ~consts:(List.fold_right (StringSet.add % fst) args consts)) p
  | Function (args, t, e) ->
    pr "function@ %a@ %a@ :@ %a =@ %a"
      why_id why_id'
      (list ~sep:"@ " logic_arg) args
      logic_type t
      (term ~bw_ints ~consts:(List.fold_right (StringSet.add % fst) args consts)) e
  | Type tvs ->
    pr "type@ %a %a" why_id why_id' (list ~sep:"@ " id) tvs
  | Exception None ->
    pr "exception@ %a" why_uid why_id'
  | Exception (Some t) ->
    pr "exception@ %a@ %a" why_uid why_id' logic_type t

let split c s =
  try
    let pos = String.index s c in
    String.(sub s 0 pos, sub s (pos + 1) @@ length s - pos - 1)
  with
  | Not_found -> "", s

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
      f ~acc:init (split_fprintf (func ~where:`Logic ~bw_ints) expand_func f') |~>
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
      f ~acc:init (split_fprintf tconstr expand_tconstr tc) |~>
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
      f ~acc:init (split_fprintf (func ~where:`Logic ~bw_ints) expand_func p) |~>
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
      f ~acc:init (split_fprintf_mod (func ~where:(`Behavior safe) ~bw_ints) expand_func f') |~>
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

module Entry =
struct
  type 'kind t = 'kind entry

  type 's for_any_entry =
    { f : 'a. state:'s -> consts:StringSet.t -> enter:(consts:StringSet.t -> StringSet.t) ->
        'a entry -> 's * StringSet.t }
  type ('s, 'k) for_why_decl =
    state:'s -> consts:StringSet.t -> enter:(consts:StringSet.t -> StringSet.t) ->
    print:(consts:StringSet.t -> formatter -> unit) -> 'k why_decl -> 's * StringSet.t

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
          f            : ('state, 'decl_kind) for_why_decl;
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
                | Theory (name, _) -> add name
                | Module (name, _) -> add name
              in
              List.iter (fun (Entry e) -> f e) file;
              { iter = fun ~consts ~entry -> continue ~state ~consts ~entry:(fun () -> assert false) ~entry':entry }
          | Decls ->
            fun ~consts ~entry ->
              let (l : decl_kind why_decl list) =
                match entry with
                | Theory (_, None) -> []
                | Module (_, None) -> []
                | Theory (_, Some (_, decls)) -> decls
                | Module (_, Some (_, _, decls)) -> decls
              in
              List.iter
                (fun ({ why_id = { why_name } } as d) -> H.add state why_name (init, d))
                l;
              continue ~state ~consts ~entry:(fun () -> entry) ~entry':entry
        in
        let map_ints ~how =
          let b = Buffer.create 25 in
          let b_formatter = formatter_of_buffer b in
          List.fold_left
            (fun m (Int ty as typ) ->
               int_ty
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
        let rec continuation
          : type kind.
            state: (state * value) H.t -> consts:_ -> entry:(unit -> decl_kind entry) -> entry':kind entry ->
          (enter:state -> f:f -> StringSet.t) Staged.t =
          fun ~state ~consts ~entry ~entry' ->
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
            match entry' with
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
            begin match entry' with
            | Theory (_, None) -> consts
            | Module (_, None) -> consts
            | Theory (name, Some (deps, decls)) ->
              List.fold_left
                (fun acc ->
                   function
                   | Use (_, Theory (name', _))
                   | Clone (_, Theory (name', _), _) ->
                     enter acc name' false)
                (consts, M.empty)
                !deps |~>
              ListLabels.fold_left ~f:(f ~kind:Theory ~name) decls |>
              map_snd
                (M.iter
                   (fun name import ->
                      match H.find state name, import with
                      | (_, Entry (Theory _ as e)), Some import ->
                        deps := Use ((if import then `Import None else `As None), e) :: !deps
                      | _ -> ()
                      | exception Not_found -> assert false (* already checked during map initialization *))) |>
              fst
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
                (consts, M.empty)
                !deps |~>
              ListLabels.fold_left ~f:(f ~kind:(Module safe) ~name) decls |>
              map_snd
                (M.iter
                   (fun name import ->
                      let add import e =
                        deps := Dependency (Use ((if import then `Import None else `As None), e)) :: !deps
                      in
                      match H.find state name, import with
                      | (_, Entry (Theory _ as e)), Some import -> add import e
                      | (_, Entry (Module _ as e)), Some import -> add import e
                      | _ -> ()
                      | exception Not_found -> assert false (* already checked during map initialization *))) |>
              fst
            end
          | Decls ->
            let f : state:state -> consts:_ -> enter:_ -> print:_ -> decl_kind why_decl -> state * _ = f in
            let enter ~self ~why_decl consts name =
              try
                let s, d = H.find state name in
                if s = init then H.replace state name (enter, d);
                let s, consts =
                  f
                    ~state:s
                    ~consts
                    ~enter:(fun ~consts -> self ~consts d)
                    ~print:(fun ~consts fmttr -> why_decl ~consts fmttr d)
                    d
                in
                H.replace state name (s, d);
                consts
              with
              | Not_found -> consts
            in
            let f ~name ~self ~why_decl ~consts d =
              Why_decl.fold
                ~bw_ints
                ~init:consts
                ~f:(fun ~acc:consts ->
                  function
                  | (`Module (name', _) | `Theory (name', _)), name'' when name = name' ->
                    enter ~self ~why_decl consts name''
                  | (`Module _ | `Theory _), _ -> consts
                  | `Current, name'' -> enter ~self ~why_decl consts name'')
                d
            in
            let sort l =
              List.sort
              (fun
                { why_id = { why_name = id1; why_pos = pos1 } }
                { why_id = { why_name = id2; why_pos = pos2 } }
                ->
                  let c = Position.compare pos1 pos2 in
                  if c <> 0 then c else compare id1 id2)
              l
            in
            let open Why_decl in
            match entry () with
            | Theory (_, None) -> consts
            | Module (_, None) -> consts
            | Theory (name, Some (_, decls)) ->
              let why_decl = why_decl ~kind:Theory ~bw_ints in
              let rec self ~consts d = f ~kind:Theory ~name ~self ~why_decl ~consts d in
              List.fold_left (fun consts -> self ~consts) consts @@ sort decls
            | Module (name, Some (_, safe, decls)) ->
              let why_decl = why_decl ~kind:(Module safe) ~bw_ints in
              let rec self ~consts d = f ~kind:(Module safe) ~name ~self ~why_decl ~consts d in
              List.fold_left (fun consts -> self ~consts) consts @@ sort decls
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
    | `As name_opt -> alias fmttr name_opt
  in
  let substs fmttr =
    function
    | [] -> ()
    | substs ->
      fprintf
        fmttr
        "@ with@[<hov 2>%a@]"
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
    | (Theory (name, _) : a entry) -> name
    | Module (name, _) -> name
  in
  function
  | Use (spec, entry) ->
    let name = name entry in
    pr "use@ %a" (dependency_spec ~name) spec
  | Clone (spec, entry, substs') ->
    let name = name entry in
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
          pr "%t@\n@." @@ print ~consts;
          let add (type k) d =
            let add () = StringSet.add d.why_id.why_name consts in
            match (d.why_decl : k decl) with
            | Def  _ -> add ()
            | Param (Base_type _) -> add ()
            | _ -> consts
          in
          `Done, add d
        | `Running ->
          (* Cyclic dependencies can be spurious due to local names treated as declarations *)
          `Running, consts
        | `Done -> `Done, consts)
  in
  let pr_entry kind name dep deps =
    pr "%s@ %a@\n@\n@[<hov 2>%a" kind uid name (list dep ~sep:"@\n@\n") deps;
    let consts = decls () in
    pr "@]@\nend";
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
            fprintf fmttr "@\n@.";
            `Done, consts
          | `Running ->
            failwith "Cyclic dependency between resulting Why3ML modules/theories"
          | `Done -> `Done, consts }
  in
  let consts = ref why3_builtin_locals in
  list
    ~sep:"@\n@."
    (fun fmttr ->
       function
       | Entry entry' -> consts := entry fmttr ~consts:!consts entry')
    fmttr
    file

let entry ~consts fmttr e = ignore (entry ~consts fmttr e)

let file ~filename f =
  Why_pp.print_in_file
    (fun fmttr -> fprintf fmttr "%a@." file f)
    filename

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_print_why3.ml"
  End:
*)

