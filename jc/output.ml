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



open Lexing
open Format
open Pp

let why3syntax = ref false

type constant =
  | Prim_void
  | Prim_int of string
  | Prim_real of string
  | Prim_bool of bool
(*
  | Prim_string of string
*)

let fprintf_constant form e =
  match e with
    | Prim_void ->
        if !why3syntax then
          fprintf form "()"
        else
          fprintf form "void"
    | Prim_int(n) ->
          fprintf form "(%s)" n
    | Prim_real(f) -> fprintf form "%s" f
    | Prim_bool(b) ->
        if !why3syntax then
          fprintf form "%s" (if b then "Bool.True" else "Bool.False")
        else
          fprintf form "%b" b
(*
    | Prim_string s -> fprintf form "\"%s\"" s
*)

type term =
  | LConst of constant
  | LApp of string * term list
  | LVar of string                  (*r immutable logic var *)
  | LDeref of string                     (*r !r *)
  | LDerefAtLabel of string * string     (*r x@L *)
  | Tnamed of string * term
  | TIf of term * term * term
  | TLet of string * term * term

let rec iter_term f t =
  match t with
  | LConst(_c) -> ()
  | LApp(id,l) -> f id; List.iter (iter_term f) l
  | LVar id | LDeref id | LDerefAtLabel(id,_) -> f id
  | Tnamed(_,t) -> iter_term f t
  | TIf(t1,t2,t3) ->
      iter_term f t1; iter_term f t2; iter_term f t3
  | TLet(id,t1,t2) ->
      f id; iter_term f t1; iter_term f t2

let rec match_term acc t1 t2 =
  match t1, t2 with
    | LVar id, _ -> (id,t2)::acc
    | LApp(id1,l1), LApp(id2,l2) when id1 = id2 ->
      List.fold_left2 match_term acc l1 l2
    | _ -> invalid_arg "match_term : t1 is not a valid context"

let why3id s =
  match s.[0] with
  | 'A'..'Z' -> "_" ^ s
  | _ ->
      if Why3_kw.is_why3_keyword s then s ^ "_why3" else s


let why3constr s =
  match s.[0] with
  | 'A'..'Z' -> s
  | 'a'..'z' -> String.capitalize s
  | _ -> "U_" ^ s

let why3id_if s =
  if !why3syntax then why3id s else s

let why3ident s =
  match s with
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
    | _ -> why3id s

let why3ident_if s =
  if !why3syntax then why3ident s else s

let why3param s =
  match s with
    | "le_int_" -> "Int.(<=)"
    | "ge_int_" -> "Int.(>=)"
    | "lt_int_" -> "Int.(<)"
    | "gt_int_" -> "Int.(>)"
        (* reals *)
    | "le_real_" -> "Real.(<=)"
    | "ge_real_" -> "Real.(>=)"
    | "lt_real_" -> "Real.(<)"
    | "gt_real_" -> "Real.(>)"
    | _ -> why3ident s



let why3_ComputerDivision = ref false
let why3_IntMinMax = ref false
let why3_reals = ref false
let why3_FromInt = ref false
let why3_Truncate = ref false
let why3_Square = ref false
let why3_Power = ref false
let why3_PowerInt = ref false
let why3_PowerReal = ref false
let why3_RealMinMax = ref false
let why3_AbsInt = ref false
let why3_AbsReal = ref false
let why3_ExpLog = ref false
let why3_Trigonometry = ref false

let compute_why3_dependencies f =
  match f with
    | "computer_div"
    | "computer_mod" -> why3_ComputerDivision := true
    | "int_min"
    | "int_max" -> why3_IntMinMax := true
    | "add_real"
    | "sub_real"
    | "neg_real"
    | "mul_real"
    | "div_real" -> why3_reals := true
    | "sqrt_real" -> why3_Square := true
    | "pow_int" -> why3_Power := true
    | "pow_real_int" -> why3_PowerInt := true
    | "pow_real" -> why3_PowerReal := true
    | "real_of_int" -> why3_FromInt := true
    | "truncate_real_to_int" -> why3_Truncate := true
    | "real_min"
    | "real_max" -> why3_RealMinMax := true
    | "abs_int" -> why3_AbsInt := true
    | "abs_real" -> why3_AbsReal := true
    | "exp" | "log" -> why3_ExpLog := true
    | "cos"
    | "sin"
    | "tan"
    | "atan" -> why3_Trigonometry := true
    | _ -> ()


(* localization *)

type kind =
  | VarDecr
  | ArithOverflow
  | DownCast
  | IndexBounds
  | PointerDeref
  | UserCall
  | DivByZero
  | AllocSize
  | Pack
  | Unpack
  | FPoverflow


(*
let pos_table :
    (string, (kind option * string option * string option *
             string * int * int * int))
    Hashtbl.t
    = Hashtbl.create 97
*)

let old_pos_table = Hashtbl.create 97

let name_counter = ref 0

let old_reg_pos prefix ?id ?kind ?name ?formula pos =
  let id = match id with
    | None ->
	incr name_counter;
	prefix ^ "_" ^ string_of_int !name_counter
    | Some n -> n
  in
  Hashtbl.add old_pos_table id (kind,name,formula,pos);
  id

let print_kind fmt k =
  fprintf fmt "%s"
    (match k with
       | VarDecr -> "VarDecr"
       | Pack -> "Pack"
       | Unpack -> "Unpack"
       | DivByZero -> "DivByZero"
       | AllocSize -> "AllocSize"
       | UserCall -> "UserCall"
       | PointerDeref -> "PointerDeref"
       | IndexBounds -> "IndexBounds"
       | DownCast -> "DownCast"
       | ArithOverflow -> "ArithOverflow"
       | FPoverflow -> "FPOverflow")

let print_kind_why3 fmt k =
  fprintf fmt "%s"
    (match k with
       | VarDecr -> "variant decreases"
       | Pack -> "pack"
       | Unpack -> "unpack"
       | DivByZero -> "division by zero"
       | AllocSize -> "allocation size"
       | UserCall -> "precondition for call"
       | PointerDeref -> "pointer dereference"
       | IndexBounds -> "index bounds"
       | DownCast -> "downcast"
       | ArithOverflow -> "arithmetic overflow"
       | FPoverflow -> "floating-point overflow")

let abs_fname f =
  if Filename.is_relative f then
    Filename.concat (Unix.getcwd ()) f
  else f

(*
let print_pos fmt =
  Hashtbl.iter
    (fun id (kind,name,formula,f,l,fc,lc) ->
       fprintf fmt "[%s]@\n" id;
       Option_misc.iter
	 (fun k -> fprintf fmt "kind = %a@\n" print_kind k) kind;
       Option_misc.iter
	 (fun n -> fprintf fmt "name = \"%s\"@\n" n) name;
       Option_misc.iter
	 (fun n -> fprintf fmt "formula = \"%s\"@\n" n) formula;
(*
       let f = b.Lexing.pos_fname in
*)
       fprintf fmt "file = \"%s\"@\n"
         (String.escaped (abs_fname f));
(*
       let l = b.Lexing.pos_lnum in
       let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol in
       let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol in
*)
       fprintf fmt "line = %d@\n" l;
       fprintf fmt "begin = %d@\n" fc;
       fprintf fmt "end = %d@\n@\n" lc)
    pos_table
*)

let old_print_pos fmt =
  Hashtbl.iter
    (fun id (kind,name,formula,(f,l,fc,lc)) ->
       fprintf fmt "[%s]@\n" id;
       Option_misc.iter
	 (fun k -> fprintf fmt "kind = %a@\n" print_kind k) kind;
       Option_misc.iter
	 (fun n -> fprintf fmt "name = \"%s\"@\n" n) name;
       Option_misc.iter
	 (fun n -> fprintf fmt "formula = \"%s\"@\n" n) formula;
       fprintf fmt "file = \"%s\"@\n"
         (String.escaped (abs_fname f));
       fprintf fmt "line = %d@\n" l;
       fprintf fmt "begin = %d@\n" fc;
       fprintf fmt "end = %d@\n@\n" lc)
    old_pos_table


let my_pos_table :
    (string, (kind option * string option * string option *
             string * int * int * int))
    Hashtbl.t
    = Hashtbl.create 97

let my_add_pos m pos = Hashtbl.add my_pos_table m pos

let my_print_locs fmt =
  Hashtbl.iter
    (fun id (kind,name,beh,f,l,fc,lc) ->
       fprintf fmt "[%s]@\n" id;
       Option_misc.iter
         (fun k -> fprintf fmt "kind = %a@\n" print_kind k) kind;
       Option_misc.iter
         (fun n -> fprintf fmt "name = \"%s\"@\n" n) name;
       Option_misc.iter
	 (fun b -> fprintf fmt "behavior = \"%s\"@\n" b) beh;
       fprintf fmt "file = \"%s\"@\n" (String.escaped f);
       fprintf fmt "line = %d@\n" l;
       fprintf fmt "begin = %d@\n" fc;
       fprintf fmt "end = %d@\n@\n" lc)
    my_pos_table

let why3_prloc fmt (f,l,fc,lc) =
  fprintf fmt "#\"%s\" %d %d %d#" f l (max fc 0) (max lc 0)

let why3loc ~prog fmt lab =
  try
    let (k,n,beh,f,l,fc,lc) = Hashtbl.find my_pos_table lab in
    begin
      match n,beh,k with
        | Some n, None,_ -> fprintf fmt "\"expl:%s\"@ " n
        | Some n, Some b,_ -> fprintf fmt "\"expl:%s, %s\"@ " n b
        | None, _, Some k -> fprintf fmt "\"expl:%a\"@ " print_kind_why3 k
        | _ -> ()
    end;
(*
    Option_misc.iter (fun n -> fprintf fmt "\"fun:%s\"@ " n) n;
    Option_misc.iter (fun b -> fprintf fmt "\"beh:%s\"@ " b) beh;
    Option_misc.iter (fun k -> fprintf fmt "\"expl:%a\"@ " print_kind_why3 k) k;
*)
    why3_prloc fmt (f,l,fc,lc)
  with
      Not_found ->
        if prog then
          fprintf fmt "'%s: " (why3constr lab)
        else
          fprintf fmt "\"%s\"" lab

let why3_locals = Hashtbl.create 97

let is_why3_local id = Hashtbl.mem why3_locals id

let add_why3_local id = Hashtbl.add why3_locals id ()

let () = add_why3_local "result"

let remove_why3_local id = Hashtbl.remove why3_locals id

type logic_type =
    { logic_type_name : string;
      logic_type_args : logic_type list;
    }
(*r int, float, int list, ... *)

let is_prop t = t.logic_type_name = "prop"

let logic_type_var s = { logic_type_name = "'"^s;
                   logic_type_args = [];
                 }

let rec iter_logic_type f t =
  f t.logic_type_name;
  List.iter (iter_logic_type f) t.logic_type_args

type assertion =
  | LTrue | LFalse
  | LAnd of assertion * assertion
  | LOr of assertion * assertion
  | LIff of assertion * assertion
  | LNot of assertion
  | LImpl of assertion * assertion
  | LIf of term * assertion * assertion
  | LLet of string * term * assertion
      (*r warning: only for Coq assertions *)
  | LForall of string * logic_type * trigger list list * assertion
      (*r forall x:t.a *)
  | LExists of string * logic_type * trigger list list * assertion
      (*r exists x:t.a *)
  | LPred of string * term list
  | LNamed of string * assertion
and trigger =
  |LPatP of assertion
  |LPatT of term


let rec unname a =
  match a with
    | LNamed(_,a) -> unname a
    | _ -> a

let is_not_true a =
  match unname a with
    | LTrue -> false
    | _ -> true

let make_var s = LVar s

let make_not a1 =
  match unname a1 with
    | LTrue -> LFalse
    | LFalse -> LTrue
    | _ -> LNot a1

let make_or a1 a2 =
  match (unname a1,unname a2) with
    | (LTrue,_) -> LTrue
    | (_,LTrue) -> LTrue
    | (LFalse,_) -> a2
    | (_,LFalse) -> a1
    | (_,_) -> LOr(a1,a2)

let make_and a1 a2 =
  match (unname a1,unname a2) with
    | (LTrue, _) -> a2
    | (_,LTrue) -> a1
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
    | (_,_) -> LAnd(a1,a2)

let rec make_and_list l =
  match l with
    | [] -> LTrue
    | f::r -> make_and f (make_and_list r)

let rec make_or_list l =
  match l with
    | [] -> LFalse
    | f::r -> make_or f (make_or_list r)

let rec make_forall_list l triggers assertion =
  match l with
    | [] -> assertion
    | [s,ty] -> LForall(s,ty,triggers,assertion)
    | (s,ty)::l -> LForall(s,ty,[],make_forall_list l triggers assertion)

let make_impl a1 a2 =
  match (unname a1,unname a2) with
    | (LTrue,_) -> a2
    | (_,LTrue) -> LTrue
    | (LFalse,_) -> LTrue
    | (_,LFalse) -> LNot(a1)
    | (_,_) -> LImpl(a1,a2)

let rec make_impl_list conclu = function
  | [] -> conclu
  | a::l -> LImpl(a,make_impl_list conclu l)

let make_equiv a1 a2 =
  match (unname a1,unname a2) with
    | (LTrue,_) -> a2
    | (_,LTrue) -> a1
    | (LFalse,_) -> make_not a2
    | (_,LFalse) -> make_not a1
    | (_,_) -> LIff(a1,a2)

let rec iter_assertion f a =
  match a with
  | LTrue -> ()
  | LFalse -> ()
  | LAnd(a1,a2) -> iter_assertion f a1; iter_assertion f a2
  | LOr(a1,a2) -> iter_assertion f a1; iter_assertion f a2
  | LIff(a1,a2) -> iter_assertion f a1; iter_assertion f a2
  | LNot(a1) -> iter_assertion f a1
  | LImpl(a1,a2) -> iter_assertion f a1; iter_assertion f a2
  | LIf(t,a1,a2) ->
      iter_term f t; iter_assertion f a1; iter_assertion f a2
  | LLet(_id,t,a) -> iter_term f t; iter_assertion f a
  | LForall(_id,t,trigs,a) -> iter_logic_type f t;
      iter_triggers f trigs;
      iter_assertion f a
  | LExists(_id,t,trigs,a) -> iter_logic_type f t;
      iter_triggers f trigs;
      iter_assertion f a
  | LPred(id,l) -> f id; List.iter (iter_term f) l
  | LNamed (_, a) -> iter_assertion f a

and iter_triggers f trigs =
  List.iter (List.iter
               (function
                  | LPatP a -> iter_assertion f a
                  | LPatT t -> iter_term f t)) trigs


let logic_type_name t =
  if !why3syntax then
    match t.logic_type_name with
      | "unit" -> "()"
      | "bool" -> "Bool.bool"
      | s -> why3ident s
  else
    t.logic_type_name

let rec fprintf_logic_type form t =
  match t.logic_type_args with
    | [] -> fprintf form "%s" (logic_type_name t)
    | [x] ->
        if !why3syntax then
	  fprintf form "(%s %a)" (logic_type_name t) fprintf_logic_type x
        else
	  fprintf form "%a %s" fprintf_logic_type x t.logic_type_name
    | l ->
        if !why3syntax then
	  fprintf form "(%s %a)"
	    (logic_type_name t)
	    (print_list space fprintf_logic_type) l
        else
	  fprintf form "(%a) %s"
	    (print_list simple_comma fprintf_logic_type) l
	    t.logic_type_name

let rec bool_to_prop t =
  match t with
    | LConst (Prim_bool true) -> LTrue
    | LConst (Prim_bool false) -> LFalse
    | LApp("bool_not",[t1]) -> LNot(bool_to_prop t1)
    | LApp("bool_and",[t1;t2]) -> LAnd(bool_to_prop t1,bool_to_prop t2)
    | LApp("bool_or",[t1;t2]) -> LOr(bool_to_prop t1,bool_to_prop t2)
    | LApp("lt_int_bool",[t1;t2]) -> LPred("lt_int",[t1;t2])
    | LApp("le_int_bool",[t1;t2]) -> LPred("le_int",[t1;t2])
    | LApp("gt_int_bool",[t1;t2]) -> LPred("gt_int",[t1;t2])
    | LApp("ge_int_bool",[t1;t2]) -> LPred("ge_int",[t1;t2])
    | LApp("lt_real_bool",[t1;t2]) -> LPred("lt_real",[t1;t2])
    | LApp("le_real_bool",[t1;t2]) -> LPred("le_real",[t1;t2])
    | LApp("gt_real_bool",[t1;t2]) -> LPred("gt_real",[t1;t2])
    | LApp("ge_real_bool",[t1;t2]) -> LPred("ge_real",[t1;t2])
      (** by default *)
    | _ -> LPred("eq",[t;LConst(Prim_bool true)])

let is_why3_poly_eq, is_why3_poly_neq =
  let eqs = ["eq_int"; "eq_bool"; "eq_real"; "eq_int_"; "eq_bool_"; "eq_real_"] in
  ListLabels.mem ~set:eqs, ListLabels.mem ~set:(List.map ((^) "n") eqs)

let rec fprintf_term form t =
  match t with
  | LConst(c) -> fprintf_constant form c
  | LApp("eq_pointer",[t1;t2]) ->
      fprintf form "@[(%a=%a)@]"
	fprintf_term t1
	fprintf_term t2
  | LApp("ne_pointer",[t1;t2]) ->
      fprintf form "@[(%a<>%a)@]"
	fprintf_term t1
	fprintf_term t2
  | LApp(id,t::tl) ->
      if !why3syntax then
        begin
          fprintf form "@[(%s@ %a" (why3ident id) fprintf_term t;
          List.iter (fun t -> fprintf form "@ %a" fprintf_term t) tl;
          fprintf form ")@]"
        end
      else
        begin
          fprintf form "@[%s(%a" id fprintf_term t;
          List.iter (fun t -> fprintf form ",@ %a" fprintf_term t) tl;
          fprintf form ")@]"
        end
  | LApp(id,[]) ->
      fprintf form "%s" (why3ident_if id)
  | LVar id ->
      fprintf form "%s" (why3ident_if id)
  | LDeref id ->
      if !why3syntax then
        if is_why3_local id then
          fprintf form "%s" (why3ident_if id)
        else
          fprintf form "!%s" (why3ident id)
      else
        fprintf form "%s" id
  | LDerefAtLabel(id,l) ->
      if !why3syntax then
        if l="" then
          fprintf form "(old !%s)" (why3ident id)
        else
          fprintf form "(at !%s '%s)" (why3ident id) (why3constr l)
      else
        fprintf form "%s@@%s" id l
  | Tnamed(lab,t) ->
      if !why3syntax then
        fprintf form "(%a %a)" (why3loc ~prog:false) lab fprintf_term t
      else
        fprintf form "(%s : %a)" lab fprintf_term t
  | TIf(t1,t2,t3) ->
    if !why3syntax then
      let f = bool_to_prop t1 in
      fprintf form "@[<hov 1>(if %a@ then %a@ else %a)@]"
        fprintf_assertion f fprintf_term t2 fprintf_term t3
    else
      fprintf form "@[<hov 1>(if %a@ then %a@ else %a)@]"
        fprintf_term t1 fprintf_term t2 fprintf_term t3
  | TLet(v,t1,t2) ->
      fprintf form "@[<hov 1>(let %s@ = %a@ in %a)@]" v
	fprintf_term t1 fprintf_term t2

and fprintf_assertion form a =
  match a with
  | LTrue -> fprintf form "true"
  | LFalse -> fprintf form "false"
  | LAnd(a1,a2) ->
      fprintf form "@[(%a@ %s %a)@]"
	fprintf_assertion a1
        (if !why3syntax then "/\\" else "and")
	fprintf_assertion a2
  | LOr(a1,a2) ->
      fprintf form "@[(%a@ %s %a)@]"
	fprintf_assertion a1
        (if !why3syntax then "\\/" else "or")
	fprintf_assertion a2
  | LIff(a1,a2) ->
      fprintf form "@[(%a@ <-> %a)@]"
	fprintf_assertion a1
	fprintf_assertion a2
  | LNot(a1) ->
      fprintf form "@[(not %a)@]"
	fprintf_assertion a1
  | LImpl(a1,a2) ->
      fprintf form "@[<hov 1>(%a ->@ %a)@]"
	fprintf_assertion a1 fprintf_assertion a2
  | LIf(t,a1,a2) when !why3syntax ->
      fprintf form "@[<hov 1>(if %a@ = True@ then %a@ else %a)@]"
	fprintf_term t fprintf_assertion a1 fprintf_assertion a2
  | LIf(t,a1,a2) ->
      fprintf form "@[<hov 1>(if %a@ then %a@ else %a)@]"
	fprintf_term t fprintf_assertion a1 fprintf_assertion a2
  | LLet(id,t,a) ->
      fprintf form "@[<hov 1>(let @[<hov 1>%s =@ %a in@]@ %a)@]" id
	fprintf_term t fprintf_assertion a
  | LForall(id,t,trigs,a) when !why3syntax ->
      fprintf form "@[<hov 1>(forall@ %s:@,%a@,%a@,.@ %a)@]"
	(why3ident id) fprintf_logic_type t
        fprintf_triggers trigs fprintf_assertion a
  | LForall(id,t,trigs,a) ->
      fprintf form "@[<hov 1>(forall@ %s:@,%a@,%a@,.@ %a)@]"
	id fprintf_logic_type t fprintf_triggers trigs fprintf_assertion a
  | LExists(id,t,trigs,a) ->
      fprintf form "@[<hov 1>(exists %s:%a%a.@ %a)@]"
	id fprintf_logic_type t fprintf_triggers trigs fprintf_assertion a
(*
  | LPred(id,[t1;t2]) when is_eq id->
      fprintf form "@[(%a = %a)@]"
	fprintf_term t1
	fprintf_term t2
*)
  | LPred("le",[t1;t2]) ->
      fprintf form "@[(%a <= %a)@]"
	fprintf_term t1
	fprintf_term t2
  | LPred("ge",[t1;t2]) ->
      fprintf form "@[(%a >= %a)@]"
	fprintf_term t1
	fprintf_term t2
  | LPred(id,[t1;t2]) when id = "eq" || !why3syntax && is_why3_poly_eq id ->
      fprintf form "@[(%a = %a)@]"
	fprintf_term t1
	fprintf_term t2
  | LPred("neq",[t1;t2]) ->
      fprintf form "@[(%a <> %a)@]"
	fprintf_term t1
	fprintf_term t2
  | LPred(id,t::tl) ->
      if !why3syntax then
        begin
          fprintf form "@[(%s@ %a" (why3ident id) fprintf_term t;
          List.iter (fun t -> fprintf form "@ %a" fprintf_term t) tl;
          fprintf form ")@]"
        end
      else
        begin
          fprintf form "@[%s(%a" id fprintf_term t;
          List.iter (fun t -> fprintf form ",@ %a" fprintf_term t) tl;
          fprintf form ")@]"
        end
  | LPred (id, []) ->
      fprintf form "%s" (why3ident_if id)
  | LNamed (n, a) ->
      if !why3syntax then
        fprintf form "@[(%a@ %a)@]" (why3loc ~prog:false) n fprintf_assertion a
      else
        fprintf form "@[(%s:@ %a)@]" n fprintf_assertion a

and fprintf_triggers fmt trigs =
  let pat fmt = function
    | LPatT t -> fprintf_term fmt t
    | LPatP p -> fprintf_assertion fmt p in
  print_list_delim lsquare rsquare alt (print_list comma pat) fmt trigs

(*s types *)


type why_type =
  | Prod_type of string * why_type * why_type      (*r (x:t1)->t2 *)
  | Base_type of logic_type
  | Ref_type of why_type
  | Annot_type of
      assertion * why_type *
      string list * string list * assertion * ((string * assertion) list)
	(*r { P } t reads r writes w { Q | E => R } *)
;;

let base_type s = Base_type { logic_type_name = s ; logic_type_args = [] }
let int_type = base_type "int"
let bool_type = base_type "bool"
let unit_type = base_type "unit"

let option_iter f x =
  match x with
    | None -> ()
    | Some y -> f y
;;


let rec iter_why_type f t =
  match t with
    | Prod_type(_,t1,t2) ->
	iter_why_type f t1; iter_why_type f t2
    | Base_type b -> iter_logic_type f b
    | Ref_type(t) -> iter_why_type f t
    | Annot_type (pre,t,reads,writes,post,signals) ->
	iter_assertion f pre;
	iter_why_type f t;
	List.iter f reads;
	List.iter f writes;
	iter_assertion f post;
	List.iter (fun (id,a) -> f id; iter_assertion f a) signals
;;


let rec fprint_comma_string_list form l =
  match l with
    | [] -> ()
    | x::l ->
	fprintf form ",%s" x;
	fprint_comma_string_list form l
;;

let rec fprintf_type ~need_colon anon form t =
  match t with
    | Prod_type(id,t1,t2) ->
	  if !why3syntax then
            let id = if id="" || anon then "_anonymous" else id in
            fprintf form "@[<hov 1>(%s:%a)@ %a@]" (why3ident id)
	    (fprintf_type ~need_colon:false anon) t1
              (fprintf_type ~need_colon anon) t2
          else
	    if id="" || anon then
	      fprintf form "@[<hov 1>%a ->@ %a@]"
	        (fprintf_type ~need_colon:false anon) t1
                (fprintf_type ~need_colon anon) t2
	    else
	      fprintf form "@[<hov 1>%s:%a ->@ %a@]" id
	        (fprintf_type ~need_colon:false anon) t1
                (fprintf_type ~need_colon anon) t2
    | Base_type t  ->
        if need_colon then fprintf form ": ";
	fprintf_logic_type form t
    | Ref_type(t) ->
        if need_colon then fprintf form ": ";
	if !why3syntax then
          fprintf form "ref %a" (fprintf_type ~need_colon:false anon) t
        else
          fprintf form "%a ref" (fprintf_type ~need_colon:false anon) t
    | Annot_type(p,t,reads,writes,q,signals) ->
	begin
          if need_colon then fprintf form ": ";
          if !why3syntax then
            begin
	      fprintf form "%a@ " (fprintf_type ~need_colon:false anon) t;
	      fprintf form "@[@[<hov 2>requires { %a }@]@ "
                fprintf_assertion p;
            end
          else
            begin
	      fprintf form "@[@[<hov 2>{ ";
	      if is_not_true p
	      then fprintf_assertion form p;
	      fprintf form "}@]@ %a@ " (fprintf_type ~need_colon:false anon) t
            end;
	  begin
	    match List.sort compare reads with
	      | [] -> ()
	      | r::l as reads ->
                  if !why3syntax then
		    fprintf form "reads@ { %a } @ "
                      (print_list comma
                         (fun form r -> fprintf form "%s" (why3ident r))) reads
                  else
		  fprintf form "reads %s%a@ " r fprint_comma_string_list l
	  end;
	  begin
	    match List.sort compare writes with
	      | [] -> ()
	      | r::l as writes ->
                  if !why3syntax then
		    fprintf form "writes@ { %a }@ "
                      (print_list comma
                         (fun form r -> fprintf form "%s" (why3ident r))) writes
                  else
		    fprintf form "writes %s%a@ " r fprint_comma_string_list l
	  end;
	  begin
	    match signals with
	      | [] ->
                  if !why3syntax then
		    fprintf form "@[<hov 2> ensures { %a }@]@]" fprintf_assertion q
                  else
		    fprintf form "@[<hov 2>{ %a }@]@]" fprintf_assertion q
	      | l ->
                  if !why3syntax then
		    begin
                      fprintf form "@[<hov 2> ensures { %a@ }@]@ "
		        fprintf_assertion q;
		      List.iter
                         (fun (e,r) ->
			    fprintf form "@[<hov 2>raises { %s result ->@ %a }@]" e
			      fprintf_assertion r)
		        l
                    end
                  else
		    fprintf form
		      "raises%a@ @[<hov 2>{ %a@ | %a }@]@]"
		      (print_list comma (fun fmt (e,_r) -> fprintf fmt " %s" e))
		      l
		      fprintf_assertion q
		      (print_list alt (fun fmt (e,r) ->
				         fprintf fmt "@[<hov 2>%s =>@ %a@]" e
					   fprintf_assertion r))
		      l
	  end

	end
;;


(*s expressions *)

type variant = term * string option

type opaque = bool

type assert_kind = [`ASSERT | `CHECK]

type expr_node =
  | Cte of constant
  | Var of string
  | And of expr * expr
  | Or of expr * expr
  | Not of expr
  | Void
  | Deref of string
  | If of expr * expr * expr
  | While of
      expr (* loop condition *)
      * assertion (* invariant *)
      * variant option (* variant *)
      * expr list (* loop body *)
  | Block of expr list
  | Assign of string * expr
  | MultiAssign of string * Loc.position * (string * expr) list *
      bool * term * expr * string * expr * string *
      (int * bool * bool * string) list
  | Let of string * expr * expr
  | Let_ref of string * expr * expr
 (* optionaly give the return type to enforce *)
  | App of expr * expr * why_type option
  | Raise of string * expr option
  | Try of expr * string * string option * expr
  | Fun of (string * why_type) list *
      assertion * expr * assertion * ((string * assertion) list)
  | Triple of opaque *
      assertion * expr * assertion * ((string * assertion) list)
  | Assert of assert_kind * assertion * expr
  | BlackBox of why_type
  | Absurd
  | Loc of Lexing.position * expr

and expr =
    { expr_labels : string list;
      expr_loc_labels : string list;
      expr_node : expr_node;
    }
;;

let mk_expr e = { expr_labels = []; expr_loc_labels = []; expr_node = e }
let mk_var s = mk_expr (Var s)
let void = mk_expr Void

let rec iter_expr f e =
  match e.expr_node with
    | Cte(_c) -> ()
    | Var(id) -> f id
    | And(e1,e2) -> iter_expr f e1; iter_expr f e2
    | Or(e1,e2) -> iter_expr f e1; iter_expr f e2
    | Not(e1) -> iter_expr f e1
    | Void -> ()
    | Deref(id) -> f id
    | If(e1,e2,e3) ->
	iter_expr f e1; iter_expr f e2; iter_expr f e3
    | While(e1,inv,var,e2) ->
	iter_expr f e1;
	iter_assertion f inv;
	option_iter (fun (var,r) -> iter_term f var;
                       match r with
                         | None -> ()
                         | Some id -> f id
                    ) var;
	List.iter (iter_expr f) e2
    | Block(el) -> List.iter (iter_expr f) el
    | Assign(id,e) -> f id; iter_expr f e
    | MultiAssign _ ->
        eprintf "Fatal error: Output.iter_expr should not be called on MultiAssign@.";
        assert false
    | Let(_id,e1,e2) -> iter_expr f e1; iter_expr f e2
    | Let_ref(_id,e1,e2) -> iter_expr f e1; iter_expr f e2
    | App(e1,e2,_) -> iter_expr f e1; iter_expr f e2
    | Raise (_, None) -> ()
    | Raise(_id,Some e) -> iter_expr f e
    | Try(e1,_exc,_id,e2) -> iter_expr f e1; iter_expr f e2
    | Fun(_params,pre,body,post,signals) ->
	iter_assertion f pre;
	iter_expr f body;
	iter_assertion f post;
	List.iter (fun (_,a) -> iter_assertion f a) signals
    | Triple(_,pre,e,post,exceps) ->
	iter_assertion f pre;
	iter_expr f e;
	iter_assertion f post;
	List.iter (fun (_,a) -> iter_assertion f a) exceps
    | Assert(_,p, e) -> iter_assertion f p; iter_expr f e
    | Loc (_,e) -> iter_expr f e
    | BlackBox(ty) -> iter_why_type f ty
    | Absurd -> ()


let fprintf_variant form = function
  | None -> ()
  | Some (t, None) ->
      if !why3syntax then
        fprintf form "variant { %a }" fprintf_term t
      else
        fprintf form "variant %a" fprintf_term t
  | Some (t, Some r) ->
      if !why3syntax then
        fprintf form "variant { %a } with %s" fprintf_term t r
      else
        fprintf form "variant %a for %s" fprintf_term t r

let rec fprintf_expr_node in_app form e =
  match e with
    | Cte(c) -> fprintf_constant form c
    | Var(id) ->
        fprintf form "%s" (if !why3syntax then why3param id else id)
    | And(e1,e2) ->
	fprintf form "@[(%a && %a)@]"
	  fprintf_expr e1 fprintf_expr e2
    | Or(e1,e2) ->
	fprintf form "@[(%a || %a)@]"
	  fprintf_expr e1 fprintf_expr e2
    | Not(e1) ->
	fprintf form "@[(not %a)@]"
	  fprintf_expr e1
    | Void ->
        if !why3syntax then
          fprintf form "()"
        else
          fprintf form "void"
    | Deref(id) ->
        fprintf form "!%s" (why3id_if id)
    | If(e1,e2,e3) ->
	fprintf form
	  "@[<hov 0>(if %a@ @[<hov 1>then@ %a@]@ @[<hov 1>else@ %a@])@]"
	  fprintf_expr e1 fprintf_expr e2 fprintf_expr e3
    | While(e1,inv,var,e2) when !why3syntax && e1.expr_node = Cte (Prim_bool true) ->
	fprintf form
	  "@[<hov 0>loop@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ end@]"
	  fprintf_assertion inv
	  fprintf_variant var
	  fprintf_expr_list e2
    | While(e1,inv,var,e2) when !why3syntax ->
	fprintf form
	  "@[<hov 0>while %a do@ @[<hov 1>@[<hov 2>@[<hov 2>invariant@ { %a }@]@ @[<hov 2>%a@]@]@ %a@]@ done@]"
	  fprintf_expr e1
	  fprintf_assertion inv
	  fprintf_variant var
	  fprintf_expr_list e2
    | While(e1,inv,var,e2) ->
	fprintf form
	  "@[<hov 0>while %a do@ @[<hov 1>@[<hov 2>{ @[<hov 2>invariant@ %a@]@ @[<hov 2>%a@] }@]@ %a@]@ done@]"
	  fprintf_expr e1
	  fprintf_assertion inv
	  fprintf_variant var
	  fprintf_expr_list e2
    | Block([]) ->
	fprintf form "void"
    | Block(el) ->
	fprintf form "@[<hov 0>begin@ @[<hov 1>  %a@]@ end@]" fprintf_expr_list el
    | Assign(id,e) ->
        fprintf form "@[<hov 1>(%s := %a)@]" (why3id_if id) fprintf_expr e
    | MultiAssign _ ->
	fprintf form "@[<hov 1>(MultiAssign ...)@]"
    | Let(id,e1,e2) ->
        fprintf form "@[<hov 0>(let %s =@ %a in@ %a)@]" (why3id_if id)
	  fprintf_expr e1 fprintf_expr e2
    | Let_ref(id,e1,e2) ->
        fprintf form "@[<hov 0>(let %s =@ ref %a in@ %a)@]" (why3id_if id)
	  fprintf_expr e1 fprintf_expr e2
    | App({expr_node = App({expr_node = Var id},e1,_)},e2,_)
        when !why3syntax && is_why3_poly_eq id ->
	fprintf form "@[<hov 1>(%a = %a)@]" fprintf_expr e1 fprintf_expr e2
    | App({expr_node = App({expr_node = Var id},e1,_)},e2,_)
        when !why3syntax && is_why3_poly_neq id ->
	fprintf form "@[<hov 1>(%a <> %a)@]" fprintf_expr e1 fprintf_expr e2
    | App(e1,e2,ty) when !why3syntax ->
        if in_app then
	  fprintf form "@[<hov 1>%a %a@]"
            (fprintf_expr_gen true) e1 fprintf_expr e2
        else
	  fprintf form "@[<hov 1>(%a %a%a)@]"
            (fprintf_expr_gen true) e1 fprintf_expr e2
            (Pp.print_option (fprintf_type ~need_colon:true false)) ty
    | App(e1,e2,_) ->
	fprintf form "@[<hov 1>(%a %a)@]" fprintf_expr e1 fprintf_expr e2
    | Raise(id,None) ->
	fprintf form "@[<hov 1>(raise@ %s)@]" id
    | Raise(id,Some e) ->
	fprintf form "@[<hov 1>(raise@ (%s@ %a))@]" id fprintf_expr e
    | Try(e1,exc,None,e2) ->
	fprintf form "@[<hov 1>try@ %a@ with@ %s ->@ %a end@]"
	  fprintf_expr e1 exc fprintf_expr e2
    | Try(e1,exc,Some id,e2) ->
	fprintf form "@[<hov 1>try@ %a@ with@ %s %s ->@ %a end@]"
	  fprintf_expr e1 exc id fprintf_expr e2
    | Fun(params,pre,body,post,signals) ->
	fprintf form "@[<hov 1>fun @[";
	List.iter
	  (fun (x,t) ->
             (match t with
               | Ref_type _ -> ()
               | _ -> add_why3_local x);
             fprintf form "(%s : %a) " (why3id_if x)
               (fprintf_type ~need_colon:false false) t)
	  params;
        if !why3syntax then
          begin
	    fprintf form "@]->@ @[<hov 0>requires { %a  }@ "
              fprintf_assertion pre;
            begin
	    match signals with
	      | [] ->
		  fprintf form "@[<hov 2>ensures { %a }@]@]" fprintf_assertion post
	      | l ->
		    fprintf form "@[<hov 2> ensures { %a@ } %a @]"
		      fprintf_assertion post
		      (print_list alt
		         (fun fmt (e,r) ->
			    fprintf fmt "@[<hov 2>raises { %s result ->@ %a }@]" e
			      fprintf_assertion r))
		      l
            end;
	    fprintf form "%a@]@ " fprintf_expr body;
          end
        else
          begin
	    fprintf form "@]->@ @[<hov 0>{ ";
	    if pre <> LTrue
	    then fprintf_assertion form pre;
	    fprintf form " }@ %a@]@ " fprintf_expr body;
	    match signals with
	      | [] ->
		  fprintf form "@[<hov 2>{ %a }@]@]" fprintf_assertion post
	      | l ->
		  fprintf form "@[<hov 2>{ %a@ | %a }@]"
		    fprintf_assertion post
		    (print_list alt
		       (fun fmt (e,r) ->
			  fprintf fmt "@[<hov 2>%s =>@ %a@]" e
			    fprintf_assertion r))
		    l
	  end;
        List.iter
	  (fun (x,t) ->
             (match t with
               | Ref_type _ -> ()
               | _ -> remove_why3_local x))
	  params;

    | Triple(_,pre,e,LTrue,[]) ->
	fprintf form "@[<hov 0>(assert { %a };@ (%a))@]"
	  fprintf_assertion pre
	  fprintf_expr e
    | Triple(o,pre,e,post,exceps) ->
      fprintf form "@[<hov 0>(assert { %a };@ " fprintf_assertion pre;
      if !why3syntax then
        if o then
          begin
            fprintf form "abstract@ ensures {@ %a }@ "
	      fprintf_assertion post;
            List.iter
              (fun (e,r) ->
                fprintf form "@[<hov 2>raises { %s ->@ %a }@]" e fprintf_assertion r)
              exceps;
            fprintf form "@ %a@ end"
              fprintf_expr e
          end
        else
          begin
            match exceps with
	      | [] ->
                fprintf form "let _ = %a in assert { %a }"
                  fprintf_expr e
		  fprintf_assertion post
              | _ -> assert false (* TODO *)
        end
      else
	begin
          fprintf form "(%a)@ " fprintf_expr e;
	  match exceps with
	    | [] ->
		(if o then
                    fprintf form "{{ %a }}" else fprintf form "{ %a }")
		  fprintf_assertion post
	    | l ->
		(if o then
		   fprintf form "@[<hov 2>{{ %a@ | %a }}@]"
		 else
		   fprintf form "@[<hov 2>{ %a@ | %a }@]")
		  fprintf_assertion post
		  (print_list alt
		  (fun fmt (e,r) ->
		     fprintf fmt "@[<hov 2>%s =>@ %a@]" e
		       fprintf_assertion r))
		  l
	end;
      fprintf form ")@]"
    | Assert(k,p, e) ->
	fprintf form "@[<hov 0>(%s@ { %a };@ %a)@]"
          (match k with `ASSERT -> "assert" | `CHECK -> "check")
	  fprintf_assertion p fprintf_expr e
    | BlackBox(t) ->
	if !why3syntax then
          fprintf form "@[<hov 0>any %a @]"
	    (fprintf_type ~need_colon:false false) t
        else
	  fprintf form "@[<hov 0>[ %a ]@]"
	    (fprintf_type ~need_colon:false false) t
    | Absurd ->
	fprintf form "@[<hov 0>absurd@ @]"
    | Loc (_l, e) ->
	fprintf_expr form e
	(*
	fprintf form "@[#%S %d %d#%a@]" l.pos_fname l.pos_lnum
	  (l.pos_cnum - l.pos_bol) fprintf_expr e
	*)

and fprintf_expr_gen in_app form e =
  let rec aux l =
    match l with
      | [] -> fprintf_expr_node in_app form e.expr_node
      | s::l ->
(*
          if s="L2" then Format.eprintf "Output.fprintf_expr: printing label %s for expression %a@." s fprintf_expr_node e.expr_node;
*)
          if !why3syntax then
            fprintf form "@[<hov 0>(%a@ " (why3loc ~prog:true) s
          else
            fprintf form "@[<hov 0>(%s:@ " s;
          aux l;
          fprintf form ")@]"
  in aux e.expr_labels

and fprintf_expr form e = fprintf_expr_gen false form e

and fprintf_expr_list form l =
  match l with
    | [] -> ()
    | e::l ->
	fprintf form "%a" fprintf_expr e;
	fprintf_expr_end_list form l

and fprintf_expr_end_list form l =
  match l with
    | [] -> ()
    | e::l ->
	fprintf form ";@ %a" fprintf_expr e;
	fprintf_expr_end_list form l
;;

let make_or_expr a1 a2 =
  match (a1.expr_node,a2.expr_node) with
    | (Cte (Prim_bool true),_) -> a1
    | (_,Cte (Prim_bool true)) -> a2
    | (Cte (Prim_bool false),_) -> a2
    | (_,Cte (Prim_bool false)) -> a1
    | (_,_) -> mk_expr (Or(a1,a2))

let make_and_expr a1 a2 =
  match (a1.expr_node,a2.expr_node) with
    | (Cte (Prim_bool true),_) -> a2
    | (_,Cte (Prim_bool true)) -> a1
    | (Cte (Prim_bool false),_) -> a1
    | (_,Cte (Prim_bool false)) -> a2
    | (_,_) -> mk_expr (And(a1,a2))


let make_app_rec ~logic f l =
  let rec make_rec accu = function
    | [] -> accu
    | e::r -> make_rec (mk_expr (App(accu,e,None))) r
  in
  match l with
    | [] -> if logic then make_rec f [] else make_rec f [void]
    | l -> make_rec f l
;;

let app_add_ty ?ty e =
  match ty,e.expr_node with
  | None,_ -> e
  | Some _, App(e1,e2,None) -> { e with expr_node = App(e1,e2,ty)}
  | Some _, _ ->
    invalid_arg "Output.app_add_ty: type coercion for constant. To correct."

let make_app ?ty id l =
  let app = make_app_rec ~logic:false (mk_var id) l in
  app_add_ty ?ty app

let make_logic_app ?ty id l =
  let app = make_app_rec ~logic:true (mk_var id) l in
  app_add_ty ?ty app

let make_app_e ?ty e l =
  let app = make_app_rec ~logic:false e l in
  app_add_ty ?ty app

let make_while cond inv var e =
  let body =
    match e.expr_node with
      | Block(l) -> l
      | _ -> [e]
  in mk_expr (While(cond,inv,var,body))

let make_label label e =
(*
  if label = "L2" then Format.eprintf "Output.make_label: adding label %s@." label;
*)
  assert (String.length label > 0);
  if label.[0] = '_' then
  { e with expr_loc_labels = label :: e.expr_loc_labels }
  else
  { e with expr_labels = label :: e.expr_labels }

let make_pre pre e =  mk_expr (Triple(false,pre,e,LTrue,[]))




let compare_parallel_assign (i,_,_,_) (j,_,_,_) =
  let c = Pervasives.compare i j in
  if c = 0 then raise Exit else c


let append_list e l =
(*
  Format.eprintf "Entering append_list@.";
*)
  match l with
    | [] -> [e]
    | e'::rem ->
        match e.expr_node,e'.expr_node with
          | MultiAssign(mark1,pos1,lets1,isrefa1,ta1,a1,tmpe1,e1,f1,l1),
            MultiAssign(_,_,lets2,_isrefa2,_ta2,a2,_tmpe2,e2,f2,l2)
            when e'.expr_labels = [] ->
              (*
                Format.eprintf
                "Found multi-assigns: a1=%a, a2=%a, e1=%a, e2=%a, f1=%s,f2=%s@."
                fprintf_expr a1 fprintf_expr a2
                fprintf_expr e1 fprintf_expr e2 f1 f2;
              *)
              if a1 = a2 && e1 = e2 && f1 = f2 then
                begin
                  try
                    let l = List.merge compare_parallel_assign l1 l2 in
                    (*
                      Format.eprintf "append_list, merge successful!@.";
                    *)
                    { expr_labels = e.expr_labels;
                      expr_loc_labels = e.expr_loc_labels @ e'.expr_loc_labels;
                      expr_node =
                        MultiAssign(mark1,pos1,lets1@lets2,isrefa1,ta1,a1,tmpe1,e1,f1,l) }
                    ::rem
                  with Exit ->
                    (*
                      Format.eprintf "append_list, merge failed...@.";
                    *)
                    e::l
                end
              else
                begin
                  (*
                    Format.eprintf "do not match@.";
                  *)
                  e::l
                end
          | MultiAssign _, _e' ->
              (*
                Format.eprintf "MultiAssign not followed by MultiAssign but by %a@."
                fprintf_expr e';
              *)
              e::l
          | _, MultiAssign _ ->
              (*
                Format.eprintf "MultiAssign not preceeded by MultiAssign@.";
              *)
              e::l
          | _ ->
              (*
                Format.eprintf "no MultiAssign at all@.";
              *)
              e::l


let make_block labels loc_labels l =
  match l with
      | [] -> assert false
      | [e] -> {e with expr_labels = labels @ e.expr_labels ; 
                       expr_loc_labels = loc_labels @ e.expr_loc_labels }
      | _ -> { expr_labels = labels ; expr_loc_labels = loc_labels ; expr_node = Block l }

(** Try hard to keep the labels visible by all the instructions that follow
    but also to remove unneeded block

    The principle is to push e2 inside e1 such that every labels visible for
    the last instruction (not a block) of e1 can be visible for e2
 *)
let rec append' e1 e2 =
  match e1.expr_node,e2.expr_node with
    | Void,_ -> (* assert (e1.expr_labels = []);*) [e2]
    | _,Void -> assert (e2.expr_labels = []); [e1]
    | Block(_),Block([]) -> [e1]
    | Block(l1),_ ->
      [make_block e1.expr_labels e1.expr_loc_labels (concat l1 e2)]
    | _,Block(l2) ->
      begin match e1.expr_labels, e2.expr_labels with
        | [], [] -> append_list e1 l2
        | labels1, [] ->
          [make_block labels1 e1.expr_loc_labels (append_list {e1 with expr_labels = []} l2)]
        | labels1, _ ->
          [make_block labels1 e1.expr_loc_labels (append_list {e1 with expr_labels = []} [e2])]
      end
    | _ ->
      if e1.expr_labels = [] then
        append_list e1 [e2]
      else
        let e1' = {e1 with expr_labels = []} in
        [make_block e1.expr_labels [] (append_list e1' [e2])]

and concat l1 e2 =
  match l1 with
  | [] -> [e2]
  | [a1] -> append' a1 e2
  | a1::l1 -> a1::(concat l1 e2)

let append e1 e2 =
  make_block [] [] (append' e1 e2)

type goal_kind = KAxiom | KLemma | KGoal

type why_id = { name : string ; loc : Loc.floc }

let id_no_loc s = { name = s; loc = Loc.dummy_floc }

type why_decl =
  | Param of bool * why_id * why_type         (*r parameter in why *)
  | Def of why_id * bool * expr               (*r global let in why *)
  | Logic of bool * why_id * (string * logic_type) list * logic_type    (*r logic decl in why *)
  | Predicate of bool * why_id * (string * logic_type) list * assertion
  | Inductive of bool * why_id * (string * logic_type) list *
      (string * assertion) list (*r inductive definition *)
  | Goal of goal_kind * why_id * assertion         (*r Goal *)
  | Function of bool * why_id * (string * logic_type) list * logic_type * term
  | Type of why_id * string list
  | Exception of why_id * logic_type option



let get_why_id d =
  match d with
    | Param(_,id,_)
    | Logic(_,id,_,_)
    | Def(id,_,_)
    | Goal(_,id,_)
    | Predicate(_,id,_,_)
    | Function(_,id,_,_,_)
    | Inductive(_,id,_,_)
    | Type (id,_)
    | Exception(id,_) -> id

let iter_why_decl f d =
  match d with
    | Param(_,_,t) -> iter_why_type f t
    | Def(_id,_,t) -> iter_expr f t
    | Logic(_,_id,args,t) ->
	List.iter (fun (_,t) -> iter_logic_type f t) args;
	iter_logic_type f t
    | Inductive(_,_id,args,cases) ->
	List.iter (fun (_,t) -> iter_logic_type f t) args;
	List.iter (fun (_,a) -> iter_assertion f a) cases
    | Predicate(_,_id,args,p) ->
	List.iter (fun (_,t) -> iter_logic_type f t) args;
	iter_assertion f p
    | Goal(_,_id,t) -> iter_assertion f t
    | Function(_,_id,args,t,p) ->
	List.iter (fun (_,t) -> iter_logic_type f t) args;
	iter_logic_type f t;
	iter_term f p
    | Type(_t,args) -> List.iter f args
    | Exception(_,t) -> Option_misc.iter (iter_logic_type f) t



type state = [`TODO | `RUNNING | `DONE ];;

type 'a decl = { mutable state : state; decl : 'a };;

module StringMap = Map.Make(String);;

(*
exception Recursion;;
*)

let rec do_topo decl_map iter_fun output_fun id d =
  match d.state with
    | `DONE -> ()
    | `RUNNING ->
	eprintf "Warning: recursive definition of %s in generated file@." id
    | `TODO ->
	d.state <- `RUNNING;
	iter_fun
	  (fun id ->
	     try
	       let s = StringMap.find id decl_map in
	       do_topo decl_map iter_fun output_fun id s
	     with
		 Not_found -> ())
	  d.decl;
	output_fun d.decl;
	d.state <- `DONE
;;

let compare_ids
    { name = id1; loc = (_,l1,_,_)}
    { name = id2; loc = (_,l2,_,_)} =
  let c = Pervasives.compare l1 l2 in
  if c = 0 then Pervasives.compare id1 id2 else c

let build_map get_id decl_list =
  let m =
    List.fold_left
      (fun acc decl ->
	 let id = get_id decl in
	 let d = { state = `TODO ; decl = decl } in
	 StringMap.add id.name (id,d) acc)
      StringMap.empty
      decl_list
  in
  let m,l = StringMap.fold
    (fun name (id,d) (m,l) ->
       (StringMap.add name d m, (id,d)::l))
    m (StringMap.empty,[])
  in
  m, List.sort (fun (id1,_) (id2,_) ->
		  compare_ids id1 id2) l
;;

let fprint_logic_arg form (id,t) =
  if !why3syntax then
    fprintf form "(%s:%a)" (why3ident id) fprintf_logic_type t
  else
    fprintf form "%s:%a" id fprintf_logic_type t

let str_of_goal_kind = function
  | KAxiom -> "axiom"
  | KLemma -> "lemma"
  | KGoal -> "goal"

let fprintf_why_decl form d =
  match d with
    | Param(b,id,t) when !why3syntax ->
	fprintf form "@[<hov 1>%sval %s@ %a@]@.@."
	(if b then "external " else "") (why3ident id.name)
	  (fprintf_type ~need_colon:true false) t
    | Param(b,id,t) ->
	fprintf form "@[<hov 1>%sparameter %s :@ %a@]@\n@."
	(if b then "external " else "") id.name
	  (fprintf_type ~need_colon:false false) t
    | Logic(b,id,args,t) when !why3syntax ->
        if is_prop t then
	  fprintf form "@[<hov 1>%spredicate %s %a @.@."
	    (if b then "external " else "")
            (why3ident id.name)
	    (print_list space (fun fmt (_id,t) -> fprintf_logic_type fmt t)) args
        else
	  fprintf form "@[<hov 1>%sfunction %s %a : %a@.@."
	    (if b then "external " else "")
            (why3ident id.name)
	    (print_list space (fun fmt (_id,t) -> fprintf_logic_type fmt t)) args
	    fprintf_logic_type t

    | Logic(b,id,args,t) ->
	fprintf form "@[<hov 1>%slogic %s: %a -> %a@.@."
	  (if b then "external " else "") id.name
	  (print_list comma (fun fmt (_id,t) -> fprintf_logic_type fmt t)) args
	  fprintf_logic_type t
    | Inductive(b,id,args,cases) when !why3syntax ->
	fprintf form "@[<hov 1>%sinductive %s @[%a@] =@\n@[<v 0>%a@]@\n@."
	  (if b then "external " else "") (why3ident id.name)
	  (print_list space (fun fmt (_id,t) -> fprintf_logic_type fmt t)) args
	  (print_list newline
	     (fun _fmt (id,a) ->
		fprintf form "| %s: @[%a@]" id fprintf_assertion a))
	  cases
    | Inductive(b,id,args,cases) ->
	fprintf form "@[<hov 1>%sinductive %s: @[%a -> prop@] =@\n@[<v 0>%a@]@\n@."
	  (if b then "external " else "") id.name
	  (print_list comma (fun fmt (_id,t) -> fprintf_logic_type fmt t)) args
	  (print_list newline
	     (fun _fmt (id,a) ->
		fprintf form "| %s: @[%a@]" id fprintf_assertion a))
	  cases
    | Goal(k,id,p) when !why3syntax ->
	fprintf form "@[<hov 1>%s %s %a:@ %a@]@.@." (str_of_goal_kind k)
          (why3id id.name)
          (why3loc ~prog:false) id.name
	  fprintf_assertion p
    | Goal(k,id,p) ->
	fprintf form "@[<hov 1>%s %s :@ %a@]@.@." (str_of_goal_kind k)
          id.name
	  fprintf_assertion p
    | Def(id,diverges,e) when !why3syntax ->
        fprintf form "@[<hov 1>let %s%s %a=@ %a@]@.@."
          (why3id id.name)
          (if diverges then " \"W:diverges:N\"" else "")
          (why3loc ~prog:false) id.name
          fprintf_expr e
    | Def(id,_,e) ->
        fprintf form "@[<hov 1>let %s =@ %a@]@.@." (why3id_if id.name)
          fprintf_expr e
    | Predicate (b, id, args, p) when !why3syntax ->
        List.iter (fun (id,_) -> add_why3_local id) args;
	fprintf form "@[<hov 1>%spredicate %s%a =@ %a@]@.@."
	  (if b then "external " else "") (why3ident id.name)
	  (print_list space fprint_logic_arg) args
	  fprintf_assertion p;
        List.iter (fun (id,_) -> remove_why3_local id) args
    | Predicate (b, id, args, p) ->
	fprintf form "@[<hov 1>%spredicate %s(%a) =@ %a@]@.@."
	  (if b then "external " else "") id.name
	  (print_list comma fprint_logic_arg) args
	  fprintf_assertion p
    | Function(b,id,args,t,e) when !why3syntax ->
        List.iter (fun (id,_) -> add_why3_local id) args;
	fprintf form "@[<hov 1>%sfunction %s%a : %a =@ %a@]@.@."
	  (if b then "external " else "") (why3ident id.name)
	  (print_list space fprint_logic_arg) args
	  fprintf_logic_type t
	  fprintf_term e;
        List.iter (fun (id,_) -> remove_why3_local id) args
    | Function(b,id,args,t,e) ->
	fprintf form "@[<hov 1>%sfunction %s(%a) : %a =@ %a@]@.@."
	  (if b then "external " else "") id.name
	  (print_list comma fprint_logic_arg) args
	  fprintf_logic_type t
	  fprintf_term e
    | Type (id, []) when !why3syntax ->
	fprintf form "@[type %s@]@.@." (why3ident id.name)
    | Type (id, []) ->
	fprintf form "@[type %s@]@.@." id.name
    | Type (id, [t]) ->
	fprintf form "@[type '%s %s@]@.@." t id.name
    | Type (id, t::l) ->
	fprintf form "@[type ('%s" t;
	List.iter (fun t -> fprintf form ", '%s" t) l;
	fprintf form ") %s@]@.@." id.name
    | Exception(id, None) ->
	fprintf form "@[exception %s@]@.@." id.name
    | Exception(id, Some t) ->
        if !why3syntax then
	  fprintf form "@[exception %s %a@]@.@." id.name
            fprintf_logic_type t
        else
          fprintf form "@[exception %s of %a@]@.@." id.name fprintf_logic_type t


let output_decls get_id iter_decl output_decl decls =
  let map, l = build_map get_id decls in
  List.iter
    (fun (id,decl) ->
       do_topo map iter_decl output_decl id.name decl)
    l

let output_why3_imports form use_floats float_model =
  fprintf form "use import int.Int@\n@\n";
  fprintf form "use bool.Bool@\n@\n";
  if !why3_IntMinMax then
    fprintf form "use int.MinMax as IntMinMax@\n@\n";
  if !why3_ComputerDivision then
    fprintf form "use int.ComputerDivision@\n@\n";
  if !why3_reals then
    fprintf form "use import real.RealInfix@\n@\n";
  if !why3_FromInt then
    fprintf form "use real.FromInt@\n@\n";
  if !why3_Truncate then
    fprintf form "use real.Truncate@\n@\n";
  if !why3_Square then
    fprintf form "use real.Square@\n@\n";
  if !why3_Power then
    fprintf form "use int.Power@\n@\n";
  if !why3_PowerInt then
    fprintf form "use real.PowerInt@\n@\n";
  if !why3_PowerReal then
    fprintf form "use real.PowerReal@\n@\n";
  if !why3_RealMinMax then
    fprintf form "use real.MinMax as RealMinMax@\n@\n";
  if !why3_AbsInt then
    fprintf form "use int.Abs as AbsInt@\n@\n";
  if !why3_AbsReal then
    fprintf form "use real.Abs as AbsReal@\n@\n";
  if !why3_ExpLog then
    fprintf form "use real.ExpLog@\n@\n";
  if !why3_Trigonometry then
    fprintf form "use real.Trigonometry@\n@\n";
  if use_floats then
    begin
      match float_model with
        | Jc_env.FMfull ->
          fprintf form "use import floating_point.SingleFull as Single@\n";
          fprintf form "use import floating_point.DoubleFull as Double@\n@\n"
        | Jc_env.FMdefensive ->
          fprintf form "use import floating_point.Single@\n";
          fprintf form "use import floating_point.Double@\n@\n"
        | Jc_env.FMmultirounding ->
          (* fprintf form "use import floating_point.Single@\n"; *)
          fprintf form "use import floating_point.DoubleMultiRounding as Double@\n@\n"
        | Jc_env.FMmath ->
          assert false (* TODO *)
    end;
  fprintf form "use import jessie3theories.Jessie_memory_model@\n@\n"


let fprintf_why_decls ?(why3=false) ?(use_floats=false)
    ~float_model form decls =
  why3syntax := why3;
  (* Why do we need a partition ?
     because one may have a type and a logic/parameter with the same name,
     and the computation of dependencies is confused in that case

     Type may depend on nothing
     Logic may depend on Type, Logic and Predicate
     Predicate may depend on Type, Predicate and Logic
     Axiom may depend on Type, Predicate and Logic
     Parameter may depend on Type, Predicate and Logic
     Def may depend on Type, Parameter, Predicate, Logic, and Def

     - Claude, 16 nov 2006

  *)

(*
  let (types, defs, others) =
    List.fold_left
      (fun (t,d,o) decl ->
	 match decl with
	   | Type _ -> (decl::t,d,o)
	   | Def _ -> (t,decl::d,o)
	   | _ -> (t,d,decl::o))
      ([],[],[]) decls
  in
    output_decls get_why_id iter_why_decl (fprintf_why_decl form) types;
    output_decls get_why_id iter_why_decl (fprintf_why_decl form) others;
    output_decls get_why_id iter_why_decl (fprintf_why_decl form) defs
*)

  if why3 then List.iter (iter_why_decl compute_why3_dependencies) decls;

  (*
    Additional rules :

    Exception may depend on Type
    Parameter may depend on Exception

    - Nicolas R., 8 nov 2007

  *)

  let (types, params, defs, others) =
    List.fold_left
      (fun (t, p, d, o) decl ->
	 match decl with
	   | Type _ -> (decl::t, p, d, o)
	   | Exception _ | Param _ -> (t, decl::p, d, o)
	   | Def _ -> (t, p, decl::d, o)
	   | _ -> (t, p, d, decl::o))
      ([], [], [], []) decls
  in
  if why3 then
    begin
      fprintf form "theory Jessie_model@\n@\n";
      output_why3_imports form use_floats float_model
    end;
  output_decls get_why_id iter_why_decl (fprintf_why_decl form) types;
  output_decls get_why_id iter_why_decl (fprintf_why_decl form) others;
  if why3 then
    begin
      fprintf form "end@\n@\n";
      fprintf form "module Jessie_program@\n@\n";
      output_why3_imports form use_floats float_model;
      fprintf form "use import Jessie_model@\n@\n";
      fprintf form "use import ref.Ref@\n@\n";
      fprintf form "use import jessie3.JessieDivision@\n@\n";
      if use_floats then
        begin
          fprintf form "use import floating_point.Rounding@\n@\n";
          match float_model with
            | Jc_env.FMfull ->
              fprintf form "use import jessie3.JessieFloatsFull@\n@\n"
            | Jc_env.FMdefensive ->
              fprintf form "use import jessie3.JessieFloats@\n@\n"
            | Jc_env.FMmultirounding ->
              fprintf form "use import jessie3.JessieFloatsMultiRounding@\n@\n"
            | Jc_env.FMmath -> assert false (* TODO *)
        end;
      fprintf form "use import jessie3.Jessie_memory_model_parameters@\n@\n";
      fprintf form "use import jessie3_integer.Integer@\n@\n";
    end;
  output_decls get_why_id iter_why_decl (fprintf_why_decl form) params;
  output_decls get_why_id iter_why_decl (fprintf_why_decl form) defs;
  if why3 then fprintf form "end@\n@\n"



(*
  Local Variables:
  compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
  End:
*)
