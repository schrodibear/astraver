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
open Why_pp

open Stdlib
open Envset

open Output_ast
open Output_misc

let fprintf_constant fmttr =
  let pr fmt = fprintf fmttr fmt in
  function
  | Prim_void -> pr "()"
  | Prim_int n -> pr "(%s)" n
  | Prim_real f -> pr "%s" f
  | Prim_bool true -> pr "Bool.True"
  | Prim_bool false -> pr "Bool.False"

let why3_id s =
  match s.[0] with
  | 'A' .. 'Z' -> "_" ^ s
  | _ when Why3_kw.is_why3_keyword s -> s ^ "_why3"
  | _ -> s

let why3_constr s =
  match s.[0] with
  | 'A' .. 'Z' -> s
  | 'a' .. 'z' -> String.capitalize s
  | _ -> "U_" ^ s

let why3_ident =
  function
  (* booleans *)
  | "not" -> "not"
  | "bool_and" -> "Bool.andb"
  | "bool_or" -> "Bool.orb"
  | "bool_xor" -> "Bool.xorb"
  | "bool_not" -> "Bool.notb"
  (* integers *)
  | "le_int" -> "Int.(<=)"
  | "le_int_" -> "Int.(<=)"
  | "le_int_bool" -> "Int.(<=)"
  | "ge_int" -> "Int.(>=)"
  | "ge_int_" -> "Int.(>=)"
  | "ge_int_bool" -> "Int.(>=)"
  | "lt_int" -> "Int.(<)"
  | "lt_int_" -> "Int.(<)"
  | "lt_int_bool" -> "Int.(<)"
  | "gt_int" -> "Int.(>)"
  | "gt_int_" -> "Int.(>)"
  | "gt_int_bool" -> "Int.(>)"
  | "add_int" -> "Int.(+)"
  | "sub_int" -> "Int.(-)"
  | "neg_int" -> "Int.(-_)"
  | "mul_int" -> "Int.(*)"
  | "computer_div" -> "ComputerDivision.div"
  | "computer_mod" -> "ComputerDivision.mod"
  | "int_min" -> "IntMinMax.min"
  | "int_max" -> "IntMinMax.max"
  (* reals *)
  | "le_real" -> "Real.(<=)"
  | "le_real_" -> "Real.(<=)"
  | "le_real_bool" -> "Real.(<=)"
  | "ge_real" -> "Real.(>=)"
  | "ge_real_" -> "Real.(>=)"
  | "ge_real_bool" -> "Real.(>=)"
  | "lt_real" -> "Real.(<)"
  | "lt_real_" -> "Real.(<)"
  | "lt_real_bool" -> "Real.(<)"
  | "gt_real" -> "Real.(>)"
  | "gt_real_" -> "Real.(>)"
  | "gt_real_bool" -> "Real.(>)"
  | "add_real" -> "Real.(+)"
  | "sub_real" -> "Real.(-)"
  | "neg_real" -> "Real.(-_)"
  | "mul_real" -> "Real.(*)"
  | "div_real" -> "Real.(/)"
  (* real functions *)
  | "real_of_int" -> "FromInt.from_int"
  | "truncate_real_to_int" -> "Truncate.truncate"
  | "real_min" -> "RealMinMax.min"
  | "real_max" -> "RealMinMax.max"
  | "abs_int" -> "AbsInt.abs"
  | "abs_real" -> "AbsReal.abs"
  | "sqrt_real" -> "Square.sqrt"
  | "pow_int" -> "Power.power"
  | "pow_real" -> "PowerReal.pow"
  | "pow_real_int" -> "PowerInt.power"
  | "exp" -> "ExpLog.exp"
  | "log" -> "ExpLog.log"
  | "cos" -> "Trigonometry.cos"
  | "sin" -> "Trigonometry.sin"
  | "tan" -> "Trigonometry.tan"
  | "atan" -> "Trigonometry.atan"
  (* floats *)
  | "nearest_even" -> "Rounding.NearestTiesToEven"
  | "down" -> "Rounding.Down"
  | "single_value" -> "Single.value"
  | "single_exact" -> "Single.exact"
  | "single_round_error" -> "Single.round_error"
  | "round_single" -> "Single.round"
  | "round_single_logic" -> "Single.round_logic"
  | "no_overflow_single" -> "Single.no_overflow"
  | "double_value" -> "Double.value"
  | "double_exact" -> "Double.exact"
  | "double_round_error" -> "Double.round_error"
  | "round_double" -> "Double.round"
  | "round_double_logic" -> "Double.round_logic"
  | "no_overflow_double" -> "Double.no_overflow"
  (* floats full *)
  | "le_double_full" -> "Double.le"
  | "lt_double_full" -> "Double.lt"
  | "ge_double_full" -> "Double.ge"
  | "gt_double_full" -> "Double.gt"
  | "eq_double_full" -> "Double.eq"
  | "ne_double_full" -> "Double.ne"
  | "double_is_finite" -> "Double.is_finite"
  | "double_is_infinite" -> "Double.is_infinite"
  | "double_is_plus_infinity" -> "Double.is_plus_infinity"
  | "double_is_minus_infinity" -> "Double.is_minus_infinity"
  | "double_is_NaN" -> "Double.is_NaN"
  | "double_sign" -> "Double.sign"
  | "Positive" -> "SpecialValues.Pos"
  | "Negative" -> "SpecialValues.Neg"
  | s -> why3_id s

let why3_param =
  function
  | "le_int_" -> "Int.(<=)"
  | "ge_int_" -> "Int.(>=)"
  | "lt_int_" -> "Int.(<)"
  | "gt_int_" -> "Int.(>)"
  (* reals *)
  | "le_real_" -> "Real.(<=)"
  | "ge_real_" -> "Real.(>=)"
  | "lt_real_" -> "Real.(<)"
  | "gt_real_" -> "Real.(>)"
  | s -> why3_ident s

type why3_dependencies = {
  mutable why3_ComputerDivision : bool;
  mutable why3_IntMinMax        : bool;
  mutable why3_reals            : bool;
  mutable why3_FromInt          : bool;
  mutable why3_Truncate         : bool;
  mutable why3_Square           : bool;
  mutable why3_Power            : bool;
  mutable why3_PowerInt         : bool;
  mutable why3_PowerReal        : bool;
  mutable why3_RealMinMax       : bool;
  mutable why3_AbsInt           : bool;
  mutable why3_AbsReal          : bool;
  mutable why3_ExpLog           : bool;
  mutable why3_Trigonometry     : bool;
}

let empty_why3_dependencies =
  {
    why3_ComputerDivision = false;
    why3_IntMinMax        = false;
    why3_reals            = false;
    why3_FromInt          = false;
    why3_Truncate         = false;
    why3_Square           = false;
    why3_Power            = false;
    why3_PowerInt         = false;
    why3_PowerReal        = false;
    why3_RealMinMax       = false;
    why3_AbsInt           = false;
    why3_AbsReal          = false;
    why3_ExpLog           = false;
    why3_Trigonometry     = false
  }

let add_why3_dependencies d f =
  match f with
  | "computer_div"
  | "computer_mod" ->
    d.why3_ComputerDivision <- true
  | "int_min"
  | "int_max" ->
    d.why3_IntMinMax <- true
  | "add_real"
  | "sub_real"
  | "neg_real"
  | "mul_real"
  | "div_real" ->
    d.why3_reals <- true
  | "sqrt_real" ->
    d.why3_Square <- true
  | "pow_int" ->
    d.why3_Power <- true
  | "pow_real_int" ->
    d.why3_PowerInt <- true
  | "pow_real" ->
    d.why3_PowerReal <- true
  | "real_of_int" ->
    d.why3_FromInt <- true
  | "truncate_real_to_int" ->
    d.why3_Truncate <- true
  | "real_min"
  | "real_max" ->
    d.why3_RealMinMax <- true
  | "abs_int" ->
    d.why3_AbsInt <- true
  | "abs_real" ->
    d.why3_AbsReal <- true
  | "exp"
  | "log" ->
    d.why3_ExpLog <- true
  | "cos"
  | "sin"
  | "tan"
  | "atan" ->
    d.why3_Trigonometry <- true
  | _ -> ()

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

let lt_name t =
  match t.lt_name with
  | "unit" -> "()"
  | "bool" -> "Bool.bool"
  | s -> why3_ident s

let rec fprintf_logic_type fmttr t =
  let pr fmt = fprintf fmttr fmt in
  match t.lt_args with
  | [] -> pr "%s" (lt_name t)
  | [x] -> pr "(%s@ %a)" (lt_name t) fprintf_logic_type x
  | l ->
    pr
      "(%s@ %a)"
      (lt_name t)
      (print_list space fprintf_logic_type)
      l

let is_why3_poly_eq, is_why3_poly_neq =
  let eqs = ["eq_int"; "eq_bool"; "eq_real"; "eq_int_"; "eq_bool_"; "eq_real_"; "eq_int_bool"; "eq_pointer_bool"] in
  ListLabels.(mem ~set:eqs, mem ~set:(List.map ((^) "n") eqs))

let why3_builtin_locals = StringSet.singleton "result"

let rec fprintf_term ~locals fmttr =
  let pr fmt = fprintf fmttr fmt in
  let fprintf_term = fprintf_term ~locals
  and fprintf_assertion = fprintf_assertion ~locals
  in
  function
  | LConst c -> fprintf_constant fmttr c
  | LApp (id, [t1; t2]) when id = "eq" || is_why3_poly_eq id ->
    pr "@[(%a@ =@ %a)@]" fprintf_term t1 fprintf_term t2
  | LApp (id, [t1; t2]) when id = "neq" || is_why3_poly_neq id ->
    pr "@[(%a@ <>@ %a)@]" fprintf_term t1 fprintf_term t2
  | LApp (id, t :: tl) ->
    pr "@[(%s@ %a" (why3_ident id) fprintf_term t;
    List.iter (pr "@ %a" fprintf_term) tl;
    pr ")@]"
  | LApp (id, []) -> pr "%s" (why3_ident id)
  | LVar id -> pr "%s" (why3_ident id)
  | LDeref id | LDerefAtLabel (id, _) when StringSet.mem id locals ->
    pr "%s" (why3_ident id)
  | LDeref id ->
    pr "!%s" (why3_ident id)
  | LDerefAtLabel (id, "") ->
    pr "(old@ !%s)" (why3_ident id)
  | LDerefAtLabel (id, l) ->
    pr "(at@ !%s@ '%s)" (why3_ident id) (why3_constr l)
  | TLabeled (l, t) ->
    pr "(%a%a)" fprintf_why_label l fprintf_term t
  | TIf (t1, t2, t3) ->
    pr "@[<hov 1>(if@ %a@ then@ %a@ else@ %a)@]"
      fprintf_assertion (assertion_of_term t1) fprintf_term t2 fprintf_term t3
  | TLet (v, t1, t2) ->
    pr "@[<hov 1>(let@ %s@ =@ %a@ in@ %a)@]"
      v fprintf_term t1 fprintf_term t2

and fprintf_assertion ~locals fmttr =
  let pr fmt = fprintf fmttr fmt in
  let fprintf_term = fprintf_term ~locals
  and fprintf_assertion = fprintf_assertion ~locals
  and fprintf_triggers = fprintf_triggers ~locals
  in
  function
  | LTrue -> pr "true"
  | LFalse -> pr "false"
  | LAnd (a1, a2) ->
    pr "@[(%a@ /\\@ %a)@]" fprintf_assertion a1 fprintf_assertion a2
  | LOr (a1, a2) ->
    pr "@[(%a@ \\/@ %a)@]" fprintf_assertion a1 fprintf_assertion a2
  | LIff (a1, a2) ->
    pr "@[(%a@ <->@ %a)@]" fprintf_assertion a1 fprintf_assertion a2
  | LNot a1 -> pr "@[(not@ %a)@]" fprintf_assertion a1
  | LImpl (a1, a2) ->
    pr "@[<hov 1>(%a@ ->@ %a)@]" fprintf_assertion a1 fprintf_assertion a2
  | LIf (t, a1, a2) ->
    pr "@[<hov 1>(if@ %a@ then@ %a@ else@ %a)@]"
      fprintf_term t fprintf_assertion a1 fprintf_assertion a2
  | LLet (id, t, a) ->
    pr "@[<hov 1>(let@ @[<hov 1>%s@ =@ %a@ in@]@ %a)@]"
      id fprintf_term t fprintf_assertion a
  | LForall (id, t, trigs, a) ->
    pr "@[<hov 1>(forall@ %s:@,%a@,%a@,.@ %a)@]"
      (why3_ident id) fprintf_logic_type t fprintf_triggers trigs fprintf_assertion a
  | LExists (id, t, trigs, a) ->
    pr "@[<hov 1>(exists@ %s:%a%a.@ %a)@]"
      id fprintf_logic_type t fprintf_triggers trigs fprintf_assertion a
  | LPred ("le", [t1; t2]) ->
    pr "@[(%a@ <=@ %a)@]" fprintf_term t1 fprintf_term t2
  | LPred ("ge", [t1; t2]) ->
    pr "@[(%a@ >=@ %a)@]"  fprintf_term t1 fprintf_term t2
  | LPred (id, [t1; t2]) when id = "eq" || is_why3_poly_eq id ->
    pr "@[(%a@ =@ %a)@]" fprintf_term t1 fprintf_term t2
  | LPred (id, [t1; t2]) when id = "neq" || is_why3_poly_neq id ->
    pr "@[(%a@ <>@ %a)@]" fprintf_term t1 fprintf_term t2
  | LPred (id, t :: tl) ->
    pr "@[(%s@ %a" (why3_ident id) fprintf_term t;
    List.iter (pr "@ %a" fprintf_term) tl;
    pr ")@]"
  | LPred (id, []) -> pr "%s" (why3_ident id)
  | LLabeled (l, a) ->
    pr "@[(%a%a)@]" fprintf_why_label l fprintf_assertion a

and fprintf_triggers ~locals fmttr trigs =
  let fprintf_term = fprintf_term ~locals
  and fprintf_assertion = fprintf_assertion ~locals
  in
  let pat fmttr =
    function
    | LPatT t -> fprintf_term fmttr t
    | LPatP p -> fprintf_assertion fmttr p
  in
  print_list_delim lsquare rsquare alt (print_list comma pat) fmttr trigs

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