(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: cinterp.ml,v 1.19 2002-12-04 10:29:50 filliatr Exp $ i*)

(*s Interpretation of C programs *)

open Format
open Misc
open Util
open Ident
open Logic
open Types
open Cast
open Ptree
open Report
open Error

(*s Interpreting C annotations *)

let parse_annot f = option_app (fun (ofs, s) -> f ofs s)

let interp_c_spec v an = 
  let (p,e,q) = match parse_annot Parser.parse_c_spec an with
    | None -> ([], Effect.bottom, None) 
    | Some k -> k
  in
  { pc_result_name = result; pc_result_type = PVpure v;
    pc_effect = e; pc_pre = p; pc_post = q }

let interp_c_pre an = list_of_some (parse_annot Parser.parse_c_pre an)

let interp_c_post = parse_annot Parser.parse_c_post

let interp_loop_annot (ofs, s) = Parser.parse_c_loop_annot ofs s

(*s Typing C programs *)

type ctype =
  | CTpure of pure_type
  | CTarray of ctype
  | CTpointer of ctype
  | CTfun of ctype list * ctype

let void = CTpure PTunit
let c_int = CTpure PTint
let c_float = CTpure PTfloat
let c_bool = CTpure PTbool

let rec pvtype_of_ctype = function
  | CTpure pt -> PVpure pt
  | CTarray c -> assert false
  | CTpointer c -> PVref (pvtype_of_ctype c)
  | CTfun _ -> assert false

let rec print_ctype fmt = function
  | CTpure PTint -> fprintf fmt "int"
  | CTpure PTfloat -> fprintf fmt "float"
  | CTpure PTbool -> assert false
  | CTpure PTunit -> fprintf fmt "void"
  | CTpure (PTexternal id ) -> Ident.print fmt id
  | CTpure (PTarray pt) -> fprintf fmt "%a[]" print_pure_type pt
  | CTpointer ct -> fprintf fmt "%a*" print_ctype ct
  | CTarray ct -> fprintf fmt "%a[]" print_ctype ct
  | CTfun (ctl, ct) -> 
      fprintf fmt "%a (%a)" print_ctype ct (print_list comma print_ctype) ctl

let loc_of_expr = function
  | CEnop l -> l
  | CEconst (l, _) -> l
  | CEvar (l, _) -> l
  | CEarrget (l, _, _) -> l
  | CEseq (l, _, _) -> l
  | CEassign (l, _, _, _) -> l
  | CEunary (l, _, _) -> l
  | CEbinary (l, _, _, _) -> l
  | CEcall (l, _, _) -> l
  | CEcond (l, _, _, _) -> l

let loc_of_statement = function
  | CSnop l -> l
  | CSexpr (l, _) -> l
  | CScond (l, _, _, _) -> l
  | CSwhile (l, _, _, _) -> l
  | CSdowhile (l, _, _, _) -> l
  | CSfor (l, _, _, _, _, _) -> l
  | CSblock (l, _) -> l
  | CSreturn (l, _) -> l
  | CSbreak l -> l
  | CScontinue l -> l


(* the environment gives the C type, together with a boolean indicating
   if a reference is used in the ML translation *)

type cenv = (ctype * bool) Ident.map

let get_type l cenv id =
  try Idmap.find id cenv with Not_found -> raise_located l (UnboundVariable id)

(*s ML constructors *)

let mk_ptree l d p q = { pdesc = d ; pre = p; post = q; loc = l }
let mk_expr l d = mk_ptree l d [] None

let mk_seq loc e1 e2 = match e1, e2 with
  | { pdesc=Sseq l1 }, { pdesc=Sseq l2 } -> mk_expr loc (Sseq (l1 @ l2))
  | e1, { pdesc=Sseq l2 } -> mk_expr loc (Sseq (Sstatement e1 :: l2))
  | { pdesc=Sseq l1 }, e2 -> mk_expr loc (Sseq (l1 @ [Sstatement e2]))
  | e1, e2 -> mk_expr loc (Sseq [Sstatement e1; Sstatement e2])
let mt_seq l = mk_expr l (Sseq [])

let ml_const l c = mk_expr l (Sconst c)
let ml_true l = ml_const l (ConstBool true)
let ml_false l = ml_const l (ConstBool false)
let ml_var l id = mk_expr l (Svar id)
let ml_refget l id = mk_expr l (Srefget id)
let ml_refset l id e = mk_expr l (Srefset (id, e))
let ml_if l e1 e2 e3 = mk_expr l (Sif (e1, e2, e3))
let ml_let_tmp l e1 k2 = 
  let tmp = fresh_var () in 
  let e2,r = k2 tmp in
  mk_expr l (Sletin (tmp, e1, e2)), r
let ml_arrget l id e = mk_expr l (Sarrget (true, id, e))
let ml_unop l op e = mk_expr l (Sapp (mk_expr l (Svar op), Sterm e))
let ml_letref l x e1 e2 = mk_expr l (Sletref (x, e1, e2))
let ml_app l f x = mk_expr l (Sapp (f, Sterm x))

let return_exception = ref (Ident.create "Return")
let break_exception = Ident.create "Break"
let continue_exception = Ident.create "Continue"

let ml_raise l x e v = 
  let m = mk_expr l (Sraise (x, e, v)) in
  let pfalse = Misc.anonymous { pp_loc = l; pp_desc = PPfalse } in
  { m with post = Some (pfalse, []) }
let ml_raise_return l e v = ml_raise l !return_exception e v
let ml_raise_break l v = ml_raise l break_exception None v
let ml_raise_continue l v = ml_raise l continue_exception None v

let ml_try_with_Ex l e1 exn k2 =
  let tmp = fresh_var () in
  mk_expr l (Stry (e1, [(exn, Some tmp), k2 tmp]))
let ml_try_with_E l e1 exn e2 = mk_expr l (Stry (e1, [(exn, None), e2]))

let c_true l = ml_const l (ConstInt 1)
let c_false l = ml_const l (ConstInt 0)

let int_of_bool l e = ml_if l e (c_true l) (c_false l)

let float_of_int l e = 
  mk_expr l (Sapp (ml_var l t_float_of_int, Sterm e))

(*s C errors *)

let unsupported l =
  raise_located l (AnyMessage "unsupported C construct")

let expected_num l =
  raise_located l (ExpectedType (fun fmt -> fprintf fmt "int or float"))

let invalid_binop l = 
  raise_located l (AnyMessage "invalid operands to binary operator")

(*s Binary operations *)

let interp_int_binop = function
  | Plus -> t_add_int
  | Minus -> t_sub_int
  | Mult -> t_mul_int
  | Div -> t_div_int
  | Mod -> t_mod_int
  | Lt -> t_lt_int
  | Gt -> t_gt_int
  | Le -> t_le_int
  | Ge -> t_ge_int
  | Eq -> t_eq_int
  | Neq -> t_neq_int
  | _ -> assert false

let interp_float_binop = function
  | Plus -> t_add_float
  | Minus -> t_sub_float
  | Mult -> t_mul_float
  | Div -> t_div_float
  | Lt -> t_lt_float
  | Gt -> t_gt_float
  | Le -> t_le_float
  | Ge -> t_ge_float
  | Eq -> t_eq_float
  | Neq -> t_neq_float
  | _ -> assert false

let mk_binop l op e1 e2 =
  mk_expr l (Sapp (mk_expr l (Sapp (mk_expr l (Svar op), Sterm e1)), Sterm e2))

let interp_binop l op (m1,t1) (m2,t2) = match op with
  | Plus | Minus | Mult | Div | Le | Lt | Ge | Gt -> 
    (match t1, t2 with
    | CTpure PTint, CTpure PTint -> 
	mk_binop l (interp_int_binop op) m1 m2, t1
    | CTpure PTfloat, CTpure PTfloat ->
	mk_binop l (interp_float_binop op) m1 m2, t1
    | CTpure PTint, CTpure PTfloat ->
	mk_binop l (interp_float_binop op) (float_of_int m1.loc m1) m2, t2
    | CTpure PTfloat, CTpure PTint ->
	mk_binop l (interp_float_binop op) m1 (float_of_int m2.loc m2), t1
    | CTpure PTbool, _ | _, CTpure PTbool ->
        assert false
    | _ -> 
	expected_num l)
  | Eq | Neq ->
    (match t1, t2 with
    | CTpure PTint, CTpure PTint -> 
	mk_binop l (interp_int_binop op) m1 m2, c_int
    | CTpure PTfloat, CTpure PTfloat ->
	mk_binop l (interp_float_binop op) m1 m2, c_int
    | CTpure PTint, CTpure PTfloat ->
	mk_binop l (interp_float_binop op) (float_of_int m1.loc m1) m2, c_int
    | CTpure PTfloat, CTpure PTint ->
	mk_binop l (interp_float_binop op) m1 (float_of_int m2.loc m2), c_int
    | CTpure pt1, CTpure pt2 when pt1 = pt2 ->
	mk_binop l t_eq m1 m2, c_int
    | _ ->
	invalid_binop l)
  | Mod ->
    (match t1, t2 with
    | CTpure PTint, CTpure PTint -> 
	mk_binop l (interp_int_binop op) m1 m2, c_int
    | _ ->
	invalid_binop l)
  | Or | And ->
      assert false	   
  | Bw_or | Bw_xor | Bw_and ->
      assert false (* TODO *)

(*s Assignment operators *)

let interp_assign_op = function
  | Amul -> Mult 
  | Adiv -> Div
  | Amod -> Mod
  | Aadd -> Plus
  | Asub -> Minus
  | Aleft | Aright | Aand | Axor | Aor -> assert false (* TODO *)
  | Aequal -> assert false

let interp_unary_op = function
  | Prefix_inc | Postfix_inc -> Plus
  | Prefix_dec | Postfix_dec -> Minus
  | _ -> assert false

(*s Coercion of [e] of type [t] to an expected type [et] *)

let coerce l et e t = match et with
  | Some (CTpure PTfloat as et) when t = c_int -> 
      float_of_int l e, et
  | Some et when et <> t ->
      raise_located l (ExpectedType (fun f -> print_ctype f et))
  | _ ->
      e, t

(*s Purity of C expressions (to give a natural interpretation) *)

let rec is_pure = function
  | CEvar _ | CEconst _  -> true
  | CEbinary (_, e1, _, e2) -> is_pure e1 && is_pure e2
  | CEunary (_, (Uplus | Uminus | Not), e) -> is_pure e
  | CEcond (_, e1, e2, e3) -> is_pure e1 && is_pure e2 && is_pure e3
  | _ -> false

(*s Left values *)

type lvalue = 
  | LVid of Loc.t * Ident.t

let interp_lvalue cenv = function
  | CEvar (l, id) ->
      (match get_type l cenv id with
	 | ct, true -> LVid (l, id), ct
	 | _ -> raise_located l (NotAReference id))
  | e ->
      raise_located (loc_of_expr e) (AnyMessage "not a left-value")

(*s C expressions. 
    [cenv : cenv] is the environment. 
    [et : ctype option] is the (possibly) expected type; 
    when [CTpure PTbool] we translate to an ML boolean expression.
    Returns the ML interpretation together with the C type. *)

let rec interp_expr cenv et e =
  if et = Some c_bool then
    interp_boolean cenv e, c_bool
  else 
    let ml,ct = match e with
      | CEvar (l, id) -> 
	  (match get_type l cenv id with
	     | ct, true -> ml_refget l id, ct
	     | ct, _ -> ml_var l id , ct)
      | CEassign (l, lv, op, e) -> 
	  (match interp_lvalue cenv lv with
	     | LVid (_, id), ct -> 
		 let mt = interp_expr cenv (Some ct) e in
		 let getid = ml_refget l id in
		 let m',t = match op with
		   | Aequal -> mt
		   | _ -> interp_binop l (interp_assign_op op) (getid,ct) mt
		 in
		 if et = Some void then
		   ml_refset l id m', void
		 else
		   mk_seq l (ml_refset l id m') getid, t)
      | CEseq (l, e1, e2) -> 
	  let m1,t1 = interp_expr cenv (Some void) e1 in
	  let m2,t2 = interp_expr cenv et e2 in
	  mk_seq l m1 m2, t2
      | CEcond (l, e1, e2, e3) ->
	  let m1 = interp_boolean cenv e1 in
	  let m2,t2 = interp_expr cenv et e2 in
	  let m3,t3 = interp_expr cenv et e3 in
	  assert (t2 = t3); (* TODO: coercion int/float *)
	  ml_if l m1 m2 m3, t2
      | CEcall (l, e, el) ->
	  interp_call l cenv e el
      | CEbinary (l, e1, (Plus | Minus | Mult | Div | Mod as op), e2) ->
	  let m1,t1 as m1t1 = interp_expr cenv None e1 in
	  let m2t2 = interp_expr cenv None e2 in
	  if is_pure e1 then
	    interp_binop l op m1t1 m2t2
	  else
	    (* let tmp = e1 in tmp op e2 *)
	    ml_let_tmp l m1 (fun x -> interp_binop l op (ml_var l x, t1) m2t2)
      | CEbinary (l, e1, (Gt | Lt | Ge | Le | Eq | Neq | And | Or), e2) as e ->
	  int_of_bool l (interp_boolean cenv e), c_int
      | CEbinary (l, e1, (Bw_and | Bw_or | Bw_xor as op), e2) ->
	  assert false
      | CEunary (l, (Prefix_inc | Prefix_dec as op), lv) ->
	  (match interp_lvalue cenv lv with
	     | LVid (_, id), ct -> 
		 let getid = ml_refget l id in
		 let id_1,_ = 
		   interp_binop l (interp_unary_op op) (getid, ct) 
		     (ml_const l (ConstInt 1), c_int)
		 in
		 let incrid = ml_refset l id id_1 in (* id := !id +- 1 *)
		 if et = Some void then 
		   incrid, void
		 else 
		   mk_seq l incrid getid, ct)
      | CEunary (l, (Postfix_inc | Postfix_dec as op), lv) ->
	  (match interp_lvalue cenv lv with
	     | LVid (_, id), ct -> 
		 let getid = ml_refget l id in
		 let id_1,_ = 
		   interp_binop l (interp_unary_op op) (getid, ct) 
		     (ml_const l (ConstInt 1), c_int)
		 in
		 let incrid = ml_refset l id id_1 in (* id := !id +- 1 *)
		 if et = Some void then 
		   incrid, void
		 else 
		   ml_let_tmp l getid 
		     (fun x -> mk_seq l incrid (ml_var l x), ct))
      | CEunary (l, Not, e) ->
	  ml_if l (interp_boolean cenv e) (c_false l) (c_true l), c_int
      | CEunary (l, Uplus, e) ->
	  interp_expr cenv et e
      | CEunary (l, Uminus, e) ->
	  let m,t = interp_expr cenv et e in
	  (match t with
	     | CTpure PTint -> ml_unop l t_neg_int m, t
	     | CTpure PTfloat -> ml_unop l t_neg_float m, t
	     | _ -> expected_num l)
      | CEarrget (l, CEvar (l', id), e) ->
	  let m,_ = interp_expr cenv (Some c_int) e in
	  (match get_type l' cenv id with
	     | CTarray ct, _ -> ml_arrget l id m, ct
	     | _ -> raise_located l' (NotAnArray id))
      | CEarrget (l, _, _) ->
	  unsupported l
      | CEnop l ->
	  ml_const l ConstUnit, void
      | CEconst (l, s) ->
	  (try
	     ml_const l (ConstInt (int_of_string s)), c_int
	   with Failure "int_of_string" ->
	     ml_const l (ConstFloat s), c_float)
    in
    coerce ml.loc et ml ct

(*s [interp_call] translates a function call *)

and interp_call l cenv e el = 
  let f,pt,rt = match e with
    | CEvar (lid, id) ->
	(match get_type lid cenv id with
	   | CTfun (pt, rt), _ -> ml_var lid id, pt, rt
	   | _ -> raise_located lid AppNonFunction)
    | _ -> raise_located l AppNonFunction
  in
  let rec interp_args args = function
    | [], [] ->
	List.fold_right (fun a f -> ml_app l f a) args f, rt
    | [], _ ->
	raise_located l PartialApp
    | _, [] ->
	raise_located l TooManyArguments
    | a :: al, at :: pt ->
	let m,_ = interp_expr cenv (Some at) a in
	if is_pure a then
	  interp_args (m :: args) (al, pt)
	else
	  ml_let_tmp l m (fun x -> interp_args (ml_var l x :: args) (al, pt))
  in
  interp_args [] (el, pt)

 
(*s [interp_boolean] returns an ML expression of type [bool] *)

and interp_boolean cenv = function
  | CEbinary (l, e1, (Gt | Lt | Ge | Le | Eq | Neq as op), e2) ->
      let m1t1 = interp_expr cenv None e1 in
      let m2t2 = interp_expr cenv None e2 in
      let e,_ = interp_binop l op m1t1 m2t2 in
      e
  | CEbinary (l, e1, And, e2) ->
      ml_if l (interp_boolean cenv e1) (interp_boolean cenv e2) (ml_false l)
  | CEbinary (l, e1, Or, e2) ->
      ml_if l (interp_boolean cenv e1) (ml_true l) (interp_boolean cenv e2)
  | CEunary (l, Not, e) ->
      ml_if l (interp_boolean cenv e) (ml_false l) (ml_true l)
  | e ->
      let m,_ as mt = interp_expr cenv None e in 
      let e,_ = 
	(* OPTIM: directement 0.0 quand float *)
	interp_binop m.loc Neq mt (ml_const m.loc (ConstInt 0), c_int) 
      in
      e

let append_to_block l s1 s2 = match s1, s2 with
  | _, None -> s1
  | CSblock (_, (d, bl)), Some s2 -> CSblock (l, (d, bl @ [s2]))
  | _, Some s2 -> CSblock (l, ([], [s1; s2]))

(*s [break] and [continue] are translated using exceptions.
    The following helper functions are used to catch them inside or around
    loops. *)

let break b l e =
  if b then
    ml_try_with_E l e break_exception (ml_const l ConstUnit)
  else 
    e

let continue b l e =
  if b then
    ml_try_with_E l e continue_exception (ml_const l ConstUnit)
  else
    e

(*s [interp_statement] interprets a C statement.
    [et] is the expected type for the returned value (if any).
    [abrupt] indicates if the ML program must return abruptly (with a 
    [raise Return]) i.e. we are not at the end of control flow. *)

type status = { 
  always_return : bool; 
  abrupt_return : bool;
  break : bool; 
  continue : bool }

let mt_status = 
  { always_return = false; 
    abrupt_return = false; break = false; continue = false }

let or_status s1 s2 =
  { always_return = s1.always_return && s2.always_return;
    abrupt_return = s1.abrupt_return || s2.abrupt_return;
    break = s1.break || s2.break;
    continue = s1.continue || s2.continue }

let rec interp_statement cenv et abrupt = function
  | CSexpr (_, e) -> 
      let m,_ = interp_expr cenv (Some void) e in 
      m, mt_status
  | CSblock (l, bl) ->
      interp_block l cenv et abrupt bl
  | CSfor (l, s1, s2, e3, an, s) ->
      let (i,v) = interp_loop_annot an in
      let s3 = option_app (fun e -> CSexpr (loc_of_expr e, e)) e3 in
      let m1,_ = interp_expr cenv (Some void) s1 in
      let bl = append_to_block l s s3 in
      let mbl, st = interp_statement cenv et true bl in
      assert (not (st.break || st.continue));
      mk_seq l m1
	(mk_expr l (Swhile (interp_boolean cenv s2, Some i, v, mbl))),
      { mt_status with abrupt_return = st.abrupt_return }
  | CSdowhile (l, s, an, e) ->
      (* do s while (e) = s ; while (e) s *)
      interp_statement cenv et abrupt
	(CSblock (l, ([], [s; CSwhile (l, e, an, s)])))
  | CSwhile (l, e, an, s) ->
      let (i,v) = interp_loop_annot an in
      let m, st = interp_statement cenv et true s in
      let m = continue st.continue l m in
      let w = mk_expr l (Swhile (interp_boolean cenv e, Some i, v, m)) in
      let w = break st.break l w in
      w, { mt_status with abrupt_return = st.abrupt_return }
  | CScond (l, e1, s2, s3) ->
      let m2, st2 = interp_statement cenv et abrupt s2 in
      let m3, st3 = interp_statement cenv et abrupt s3 in
      mk_expr l (Sif (interp_boolean cenv e1, m2, m3)), or_status st2 st3
  | CSnop l ->
      mk_expr l (Sconst ConstUnit), mt_status
  | CSreturn (l, e) ->
      let m,_ = match e with
	| Some e -> interp_expr cenv (Some et) e
	| None -> ml_const l ConstUnit, void
      in
      if abrupt then
	ml_raise_return l (Some m) (Some (PVpure PTunit)),
	{ mt_status with always_return = true; abrupt_return = true }
      else
	m, { mt_status with always_return = true }
  | CSbreak l ->
      ml_raise_break l (Some (PVpure PTunit)), 
      { mt_status with break = true }
  | CScontinue l -> 
      ml_raise_continue l (Some (PVpure PTunit)), 
      { mt_status with continue = true }
		  

(*s C blocks *)

and interp_block l cenv et abrupt (d,b) =
  let rec interp_locals cenv = function
    | [] ->
	cenv, []
    | Ctypedecl (l, CDvar (id, Some e), v) :: dl ->
	let m,_ = interp_expr cenv (Some (CTpure v)) e in
	let cenv' = Idmap.add id (CTpure v, true) cenv in
	let cenv'',lv = interp_locals cenv' dl in
	cenv'', (id, m) :: lv
    | Ctypedecl (l, CDvar (_, None), _) :: _ -> 
	raise_located l (AnyMessage "Local variables must be initialized")
    | _ ->
	unsupported l
  in
  let cenv',lv = interp_locals cenv d in
  let rec interp_bl = function
    | [] -> 
	mt_seq l, mt_status
    | [s] ->
	let _,st as m = interp_statement cenv' et abrupt s in
	if not abrupt && not st.always_return && not (et = void) then
	  raise_located l (AnyMessage "return required at end of block");
	m
    | s :: bl ->
	let s', st1 = interp_statement cenv' et true s in
	if st1.always_return then 
	  wprintf (loc_of_statement (List.hd bl)) "unreachable statement\n";
	let bl', st2 = interp_bl bl in
	mk_seq l s' bl', or_status st1 st2
  in
  let b', st = interp_bl b in
  List.fold_right (fun (id,e) m -> ml_letref l id e m) lv b', st

(*s C functions *)

let interp_annotated_block cenv et (l, p, bl, q) =
  let bl, st = interp_block l cenv et false bl in
  if st.break || st.continue then
    raise_located l (AnyMessage "unbound break or continue");
  let bl = 
    if st.abrupt_return then
      ml_try_with_Ex l bl !return_exception (ml_var l)
    else 
      bl
  in
  { pdesc = bl.pdesc; pre = interp_c_pre p; post = interp_c_post q; loc=l },
  st.abrupt_return

let interp_binder (pt, id) = (id, BindType (PVpure pt))

let interp_binders = List.map interp_binder

let interp_fun id cenv l bl v bs =
  let cenv' = 
    List.fold_right (fun (v,id) -> Idmap.add id (CTpure v, false)) bl cenv 
  in
  return_exception := Ident.create ("Return_" ^ Ident.string id);
  let bs',ar = interp_annotated_block cenv' (CTpure v) bs in
  mk_ptree l (Slam (interp_binders bl, bs')) [] None, ar
		    

let interp_fun_type bl v =
  CTfun (List.map (fun (v,_) -> CTpure v) bl, CTpure v), false

(*s C declarations *)

let interp_decl cenv = function
  | Ctypedecl (l, CDvar (id, _), v) -> 
      [ Parameter (l, [id], PVref (PVpure v)) ],
      Idmap.add id (CTpure v, true) cenv
  | Ctypedecl (l, CDfun (id, bl, an), v) -> 
      let bl = if bl = [] then [PTunit, anonymous] else bl in
      let k = interp_c_spec v an in
      let blp = List.map (fun (v, id) -> (id, BindType (PVpure v))) bl in
      [ Parameter (l, [id], PVarrow (blp, k)) ],
      Idmap.add id (interp_fun_type bl v) cenv
  | Ctypedecl _ -> 
      assert false
  | Cfundef (l, id, bl, v, bs) ->
      let bl = if bl = [] then [PTunit, anonymous] else bl in
      let e,ar = interp_fun id cenv l bl v bs in
      let d = [ Program (id, e) ] in
      (if ar then (Exception (l, !return_exception, Some v)) :: d else d),
      Idmap.add id (interp_fun_type bl v) cenv

let interp l = 
  let rec interp_list cenv = function
    | [] -> []
    | d :: l -> let d',cenv' = interp_decl cenv d in d' @ interp_list cenv' l
  in
  (Exception (Loc.dummy, break_exception, None)) ::
  (Exception (Loc.dummy, continue_exception, None)) ::
  interp_list Idmap.empty l

