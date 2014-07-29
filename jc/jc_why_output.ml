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

open Format
open Pp

open Jc_why_output_ast
open Jc_why_output_misc

let fprintf_constant fmttr e =
  let pr fmt = fprintf fmttr fmt in
  match e with
  | Prim_void ->  pr "void"
  | Prim_int n -> pr "(%s)" n
  | Prim_real f -> pr "%s" f
  | Prim_bool b -> pr "%b" b

let fprintf_vc_kind fmttr k =
  fprintf fmttr "%s"
    (match k with
     | JCVCvar_decr -> "VarDecr"
     | JCVCpack -> "Pack"
     | JCVCunpack -> "Unpack"
     | JCVCdiv_by_zero -> "DivByZero"
     | JCVCalloc_size -> "AllocSize"
     | JCVCuser_call _ -> "UserCall"
     | JCVCpointer_deref -> "PointerDeref"
     | JCVCindex_bounds -> "IndexBounds"
     | JCVCdowncast -> "DownCast"
     | JCVCarith_overflow -> "ArithOverflow"
     | JCVCfp_overflow -> "FPOverflow")

let add_vc, add_why_id =
  let why_loc_of_pos (b, e) =
      let open Lexing in
      abs_fname b.pos_fname,
      b.pos_lnum,
      b.pos_cnum - b.pos_bol,
      e.pos_cnum - b.pos_bol
  in
  (fun { vc_kind; vc_behavior; vc_pos } ->
    let f, l, fc, lc = why_loc_of_pos vc_pos in
    let mark = Jc_pervasives.new_label_name () in
    why_reg_pos mark (Some vc_kind, None, (if vc_behavior <> "" then Some vc_behavior else None), f, l, fc, lc);
    mark),
  fun { why_name; why_expl; why_pos } ->
    let f, l, fc, lc = why_loc_of_pos why_pos in
    why_reg_pos why_name (None, Some why_expl, None, f, l, fc, lc)

let rec fprintf_logic_type fmttr t =
  let pr fmt = fprintf fmttr fmt in
  match t.lt_args with
  | [] -> pr "%s" t.lt_name
  | [x] -> pr "%a %s" fprintf_logic_type x t.lt_name
  | l ->
    pr
      "(%a) %s"
      (print_list simple_comma fprintf_logic_type) l
      t.lt_name

let rec fprintf_term fmttr t =
  let pr fmt = fprintf fmttr fmt in
  match t with
  | LConst(c) -> fprintf_constant fmttr c
  | LApp ("eq_pointer", [t1; t2]) ->
    pr
      "@[(%a=%a)@]"
      fprintf_term t1
      fprintf_term t2
  | LApp ("ne_pointer", [t1; t2]) ->
    pr
      "@[(%a<>%a)@]"
      fprintf_term t1
      fprintf_term t2
  | LApp (id, t :: tl) ->
    pr "@[%s(%a" id fprintf_term t;
    List.iter (pr ",@ %a" fprintf_term) tl;
    pr ")@]"
  | LApp (id, []) -> pr "%s" id
  | LVar id -> pr "%s" id
  | LDeref id -> pr "%s" id
  | LDerefAtLabel (id, l) -> pr "%s@@%s" id l
  | TNamed (vc, t) ->
    pr "(%s : %a)" (add_vc vc) fprintf_term t
  | TIf (t1, t2, t3) ->
    pr "@[<hov 1>(if %a@ then %a@ else %a)@]"
      fprintf_term t1 fprintf_term t2 fprintf_term t3
  | TLet (v, t1, t2) ->
    pr "@[<hov 1>(let %s@ = %a@ in %a)@]"
      v fprintf_term t1 fprintf_term t2

and fprintf_assertion fmttr a =
  let pr fmt = fprintf fmttr fmt in
  match a with
  | LTrue -> pr "true"
  | LFalse -> pr "false"
  | LAnd (a1, a2) ->
    pr "@[(%a@ and %a)@]"
      fprintf_assertion a1
      fprintf_assertion a2
  | LOr (a1, a2) ->
    pr "@[(%a@ or %a)@]"
      fprintf_assertion a1
      fprintf_assertion a2
  | LIff (a1, a2) ->
    pr "@[(%a@ <-> %a)@]"
      fprintf_assertion a1
      fprintf_assertion a2
  | LNot a1 ->
    pr "@[(not %a)@]"   fprintf_assertion a1
  | LImpl (a1, a2) ->
    pr "@[<hov 1>(%a ->@ %a)@]"
      fprintf_assertion a1 fprintf_assertion a2
  | LIf (t, a1, a2) ->
    pr "@[<hov 1>(if %a@ then %a@ else %a)@]"
      fprintf_term t fprintf_assertion a1 fprintf_assertion a2
  | LLet (id, t, a) ->
    pr "@[<hov 1>(let @[<hov 1>%s =@ %a in@]@ %a)@]"
      id fprintf_term t fprintf_assertion a
  | LForall (id, t, trigs, a) ->
    pr "@[<hov 1>(forall@ %s:@,%a@,%a@,.@ %a)@]"
      id fprintf_logic_type t fprintf_triggers trigs fprintf_assertion a
  | LExists (id, t, trigs, a) ->
    pr "@[<hov 1>(exists %s:%a%a.@ %a)@]"
      id fprintf_logic_type t fprintf_triggers trigs fprintf_assertion a
  | LPred ("le", [t1; t2]) ->
    pr "@[(%a <= %a)@]"
      fprintf_term t1
      fprintf_term t2
  | LPred ("ge", [t1; t2]) ->
    pr "@[(%a >= %a)@]"
      fprintf_term t1
      fprintf_term t2
  | LPred ("eq", [t1; t2]) ->
    pr "@[(%a = %a)@]"
      fprintf_term t1
      fprintf_term t2
  | LPred ("neq", [t1; t2]) ->
    pr "@[(%a <> %a)@]"
      fprintf_term t1
      fprintf_term t2
  | LPred (id, t :: tl) ->
    let id = try List.assoc id ["eq_int_bool", "eq_int"] with Not_found -> id in
    pr "@[%s(%a" id fprintf_term t;
    List.iter (pr ",@ %a" fprintf_term) tl;
    pr ")@]"
  | LPred (id, []) -> pr "%s" id
  | LNamed (vc, a) -> pr "@[(%s:@ %a)@]" (add_vc vc) fprintf_assertion a

and fprintf_triggers fmt trigs =
  let pat fmt = function
    | LPatT t -> fprintf_term fmt t
    | LPatP p -> fprintf_assertion fmt p in
  print_list_delim lsquare rsquare alt (print_list comma pat) fmt trigs

let rec fprintf_type ~need_colon anon fmttr t =
  let pr fmt = fprintf fmttr fmt in
  begin match t with
  | Prod_type _ -> ()
  | _ when need_colon -> pr ": "
  | _ -> ()
  end;
  match t with
  | Prod_type (id, t1, t2) when id = "" || anon ->
    pr "@[<hov 1>%a ->@ %a@]"
      (fprintf_type ~need_colon:false anon) t1
      (fprintf_type ~need_colon anon) t2
  | Prod_type (id, t1, t2) ->
    pr "@[<hov 1>%s:%a ->@ %a@]"
      id
      (fprintf_type ~need_colon:false anon) t1
      (fprintf_type ~need_colon anon) t2
  | Base_type t  -> fprintf_logic_type fmttr t
  | Ref_type t -> pr "%a ref" (fprintf_type ~need_colon:false anon) t
  | Annot_type (p, t, reads, writes, q, signals) ->
    pr "@[@[<hov 2>{ ";
    if is_not_true p
    then fprintf_assertion fmttr p;
    pr "}@]@ %a@ " (fprintf_type ~need_colon:false anon) t;
    begin match List.sort compare reads with
    | [] -> ()
    | r :: l -> pr "reads %s%a@ " r fprintf_comma_string_list l
    end;
    begin match List.sort compare writes with
    | [] -> ()
    | r :: l-> pr "writes %s%a@ " r fprintf_comma_string_list l
    end;
    begin match signals with
    | [] -> pr "@[<hov 2>{ %a }@]@]" fprintf_assertion q
    | l ->
      pr
        "raises%a@ @[<hov 2>{ %a@ | %a }@]@]"
        (print_list comma @@ fun fmt (e, _r) -> fprintf fmt " %s" e)
        l
        fprintf_assertion q
        (print_list alt @@ fun fmt (e, r) -> fprintf fmt "@[<hov 2>%s =>@ %a@]" e fprintf_assertion r)
        l
    end

let fprintf_variant fmttr =
  let pr fmt = fprintf fmttr fmt in
  function
  | None -> ()
  | Some (t, None) -> pr "variant %a" fprintf_term t
  | Some (t, Some r) -> pr "variant %a for %s" fprintf_term t r

let rec fprintf_expr_node fmttr e =
  let pr fmt = fprintf fmttr fmt in
  match e with
  | Cte c -> fprintf_constant fmttr c
  | Var id -> pr "%s" id
  | And (e1, e2) ->
    pr "@[(%a && %a)@]" fprintf_expr e1 fprintf_expr e2
  | Or (e1, e2) ->
    pr "@[(%a || %a)@]" fprintf_expr e1 fprintf_expr e2
  | Not e1 ->
    pr "@[(not %a)@]" fprintf_expr e1
  | Void -> pr "void"
  | Deref id -> pr "!%s" id
  | If (e1, e2, e3) ->
    pr "@[<hov 0>(if %a@ @[<hov 1>then@ %a@]@ @[<hov 1>else@ %a@])@]"
      fprintf_expr e1 fprintf_expr e2 fprintf_expr e3
  | While (e1, inv, var, e2) ->
    pr "@[<hov 0>while %a do@ @[<hov 1>@[<hov 2>{ @[<hov 2>invariant@ %a@]@ @[<hov 2>%a@] }@]@ %a@]@ done@]"
      fprintf_expr e1
      fprintf_assertion inv
      fprintf_variant var
      fprintf_expr_list e2
  | Block [] -> pr "void"
  | Block el ->
    pr "@[<hov 0>begin@ @[<hov 1>  %a@]@ end@]" fprintf_expr_list el
  | Assign (id, e) ->
    pr "@[<hov 1>(%s := %a)@]" id fprintf_expr e
  | Let (id, e1, e2) ->
    pr "@[<hov 0>(let %s =@ %a in@ %a)@]" id fprintf_expr e1 fprintf_expr e2
  | Let_ref (id, e1, e2) ->
    pr "@[<hov 0>(let %s =@ ref %a in@ %a)@]" id fprintf_expr e1 fprintf_expr e2
  | App (e1, e2, _) -> pr "@[<hov 1>(%a %a)@]" fprintf_expr e1 fprintf_expr e2
  | Raise (id, None) -> pr "@[<hov 1>(raise@ %s)@]" id
  | Raise (id, Some e) -> pr "@[<hov 1>(raise@ (%s@ %a))@]" id fprintf_expr e
  | Try (e1, exc, None, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %s ->@ %a end@]"
      fprintf_expr e1 exc fprintf_expr e2
  | Try (e1, exc, Some id, e2) ->
    pr "@[<hov 1>try@ %a@ with@ %s %s ->@ %a end@]"
      fprintf_expr e1 exc id fprintf_expr e2
  | Fun (params, pre, body, post, signals) ->
    pr "@[<hov 1>fun @[";
    List.iter
      (fun (x, t) ->
         pr "(%s : %a) " x (fprintf_type ~need_colon:false false) t)
      params;
    pr "@]->@ @[<hov 0>{ ";
    if pre <> LTrue then fprintf_assertion fmttr pre;
    pr " }@ %a@]@ " fprintf_expr body;
    begin match signals with
    | [] -> pr "@[<hov 2>{ %a }@]@]" fprintf_assertion post
    | l ->
      pr "@[<hov 2>{ %a@ | %a }@]"
        fprintf_assertion post
        (print_list alt @@ fun fmt (e, r) -> fprintf fmt "@[<hov 2>%s =>@ %a@]" e  fprintf_assertion r)
        l
    end;
  | Triple (_, pre, e, LTrue, []) ->
    pr "@[<hov 0>(assert { %a };@ (%a))@]" fprintf_assertion pre fprintf_expr e
  | Triple (o, pre, e, post, exceps) ->
    pr "@[<hov 0>(assert { %a };@ " fprintf_assertion pre;
    pr "(%a)@ " fprintf_expr e;
    begin match exceps with
    | [] ->
      (if o then  pr "{{ %a }}" else pr "{ %a }")
        fprintf_assertion post
    | l ->
      pr (if o then "@[<hov 2>{{ %a@ | %a }}@]" else "@[<hov 2>{ %a@ | %a }@]")
        fprintf_assertion post
        (print_list alt @@ fun fmt (e, r) -> fprintf fmt "@[<hov 2>%s =>@ %a@]" e fprintf_assertion r)
        l
    end;
    pr ")@]"
  | Assert (k, p, e) ->
    pr "@[<hov 0>(%s@ { %a };@ %a)@]"
      (match k with `ASSERT -> "assert" | `ASSUME -> "assume" | `CHECK -> "check")
      fprintf_assertion p fprintf_expr e
  | BlackBox t ->
    pr "@[<hov 0>[ %a ]@]" (fprintf_type ~need_colon:false false) t
  | Absurd -> pr "@[<hov 0>absurd@ @]"
  | Named (_vc, e) -> fprintf_expr fmttr e

and fprintf_expr fmttr e =
  let pr fmt = fprintf fmttr fmt in
  let rec aux l =
    match l with
    | [] -> fprintf_expr_node fmttr e.expr_node
    | s :: l ->
      pr "@[<hov 0>(%s:@ " s;
      aux l;
      pr ")@]"
  in
  aux e.expr_labels

and fprintf_expr_list fmttr l =
  match l with
    | [] -> ()
    | e :: l ->
      fprintf fmttr "%a" fprintf_expr e;
      fprintf_expr_end_list fmttr l

and fprintf_expr_end_list fmttr l =
  match l with
  | [] -> ()
  | e :: l ->
    fprintf fmttr ";@ %a" fprintf_expr e;
    fprintf_expr_end_list fmttr l

let fprint_logic_arg fmttr (id, t) =  fprintf fmttr "%s:%a" id fprintf_logic_type t

let string_of_goal_kind =
  function
  | KAxiom -> "axiom"
  | KLemma -> "lemma"
  | KGoal -> "goal"

let fprintf_why_decl fmttr d =
  let pr fmt = fprintf fmttr fmt in
  let ext b = if b then "external " else "" in
  let name id = add_why_id id; id.why_name in
  match d with
  | Param (b, id, t) ->
    pr "@[<hov 1>%sparameter %s :@ %a@]@\n@."
      (ext b) (name id) (fprintf_type ~need_colon:false false) t
  | Logic (b, id, args,t) ->
    pr "@[<hov 1>%slogic %s: %a -> %a@.@."
      (ext b) (name id)
      (print_list comma @@ fun fmt (_id, t) -> fprintf_logic_type fmt t) args
      fprintf_logic_type t
  | Inductive (b, id, args, cases) ->
    pr "@[<hov 1>%sinductive %s: @[%a -> prop@] =@\n@[<v 0>%a@]@\n@."
      (ext b) (name id)
      (print_list comma @@ fun fmt (_id,t) -> fprintf_logic_type fmt t) args
      (print_list newline @@ fun _fmt (id,a ) -> pr "| %s: @[%a@]" id fprintf_assertion a)
      cases
  | Goal (k, id, p) ->
    pr "@[<hov 1>%s %s :@ %a@]@.@."
      (string_of_goal_kind k)
      (name id)
      fprintf_assertion p
  | Def (id, _, e) ->
    pr "@[<hov 1>let %s =@ %a@]@.@."
      (name id) fprintf_expr e
  | Predicate (b, id, args, p) ->
    pr "@[<hov 1>%spredicate %s(%a) =@ %a@]@.@."
      (ext b) (name id)
      (print_list comma fprint_logic_arg) args
      fprintf_assertion p
  | Function (b, id, args, t, e) ->
    pr "@[<hov 1>%sfunction %s(%a) : %a =@ %a@]@.@."
      (ext b) (name id)
      (print_list comma fprint_logic_arg) args
      fprintf_logic_type t
      fprintf_term e
  | Type (id, []) -> pr "@[type %s@]@.@." (name id)
  | Type (id, [t]) -> pr "@[type '%s %s@]@.@." t (name id)
  | Type (id, t :: l) ->
    pr "@[type ('%s" t;
    List.iter (fun t -> pr ", '%s" t) l;
    pr ") %s@]@.@." (name id)
  | Exception (id, None) -> pr "@[exception %s@]@.@." (name id)
  | Exception (id, Some t) -> pr "@[exception %s of %a@]@.@." (name id) fprintf_logic_type t


let fprintf_why_decls ?float_model:_ fmttr decls =
  let types, params, defs, others =
    List.fold_left
      (fun (t, p, d, o) decl ->
         match decl with
         | Type _ -> decl :: t, p, d, o
         | Exception _ | Param _ -> t, decl :: p, d, o
         | Def _ -> t, p, decl :: d, o
         | _ -> t, p, d, decl :: o)
      ([], [], [], [])
      decls
  in
  let pr = output_decls get_why_id iter_why_decl (fprintf_why_decl fmttr) in
  pr types;
  pr others;
  pr params;
  pr defs
