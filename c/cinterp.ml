(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: cinterp.ml,v 1.5 2004-02-03 08:24:43 marche Exp $ i*)

(*****

(*s Interpretation of C programs *)

open Format
open Options
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
  let (p,e,q) = match parse_annot Clexer.parse_spec an with
    | None -> ([], Effect.bottom, None) 
    | Some k -> k
  in
  { pc_result_name = result; pc_result_type = PVpure v;
    pc_effect = e; pc_pre = p; pc_post = q }

let interp_c_pre an = parse_annot Parser.parse_c_pre an

let interp_c_post = parse_annot Parser.parse_c_post

let interp_loop_annot (ofs, s) = Parser.parse_c_loop_annot ofs s

let interp_c_annot = Parser.parse_c_annot

(*s Typing C programs *)

let simple_type t = 
  { ctype_expr = t; ctype_storage = No_storage;
    ctype_const = false; ctype_volatile = false; ctype_signed = true }

let void = CTpure PTunit
let c_int = CTpure PTint
let c_float = CTpure PTfloat
let c_bool = CTpure PTbool

let rec pvtype_of_ctype = function
  | CTpure pt -> PVpure pt
  | CTarray c -> assert false
  | CTpointer c -> PVref (pvtype_of_ctype c)
  | CTfun _ -> assert false

let rec ctype_of_pvtype = function
  | PVpure pt -> CTpure pt
  | PVref v -> CTpointer (ctype_of_pvtype v)
  | PVarray v -> CTarray (ctype_of_pvtype v)
  | PVarrow _ -> assert false

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
  | CEconstant (l, _) -> l
  | CEstring_literal (l, _) -> l
  | CEvar (l, _) -> l
  | CEarrget (l, _, _) -> l
  | CEseq (l, _, _) -> l
  | CEassign (l, _, _, _) -> l
  | CEunary (l, _, _) -> l
  | CEbinary (l, _, _, _) -> l
  | CEcall (l, _, _) -> l
  | CEcond (l, _, _, _) -> l

let loc_of_statement = function
  | CSnop l
  | CSexpr (l, _)
  | CScond (l, _, _, _)
  | CSwhile (l, _, _, _)
  | CSdowhile (l, _, _, _)
  | CSfor (l, _, _, _, _, _)
  | CSblock (l, _)
  | CSreturn (l, _)
  | CSbreak l
  | CScontinue l
  | CSlabel (l, _, _)
  | CSannot (l, _) -> l

(* the environment gives the C type, together with a boolean indicating
   if a reference is used in the ML translation *)

type cenv = (ctype * bool) Ident.map

let get_type l cenv id =
  try Idmap.find id cenv with Not_found -> raise_located l (UnboundVariable id)

(*s ML constructors *)

let mk_ptree l d p q = { pdesc = d ; pre = p; oblig = []; post = q; ploc = l }
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
  let tmp = fresh_c_var () in 
  let e2,r = k2 tmp in
  mk_expr l (Sletin (tmp, e1, e2)), r
let ml_arrget l id e = mk_expr l (Sarrget (true, id, e))
let ml_arrset l id e1 e2 = mk_expr l (Sarrset (true, id, e1, e2))
let ml_unop l op e = mk_expr l (Sapp (mk_expr l (Svar op), Sterm e))
let ml_letref l x e1 e2 = mk_expr l (Sletref (x, e1, e2))
let ml_app l f x = mk_expr l (Sapp (f, Sterm x))

let return_exception = ref (Ident.create "Return")
let break_exception = Ident.create "Break"
let continue_exception = Ident.create "Continue"

let ml_raise l x e v = mk_expr l (Sraise (x, e, v))
let ml_raise_return l e v = ml_raise l !return_exception e v
let ml_raise_break l v = ml_raise l break_exception None v
let ml_raise_continue l v = ml_raise l continue_exception None v

let ml_try_with_Ex l e1 exn k2 =
  let tmp = fresh_c_var () in
  mk_expr l (Stry (e1, [(exn, Some tmp), k2 tmp]))
let ml_try_with_E l e1 exn e2 = mk_expr l (Stry (e1, [(exn, None), e2]))

let ml_assert l p = 
  mk_expr l (Sseq [Sassert p; Sstatement (ml_const l ConstUnit)])
let ml_label l lab =
  mk_expr l (Sseq [Slabel lab; Sstatement (ml_const l ConstUnit)])

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

(*s Declarators *)

let rec interp_declarator l ct = function
  | CDsimple -> ct
  | CDpointer d -> CTpointer (interp_declarator l ct d)
  | CDarray (d, _) -> CTarray (interp_declarator l ct d)
  | CDfunction _ -> unsupported l

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
	mk_binop l (interp_float_binop op) (float_of_int m1.ploc m1) m2, t2
    | CTpure PTfloat, CTpure PTint ->
	mk_binop l (interp_float_binop op) m1 (float_of_int m2.ploc m2), t1
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
	mk_binop l (interp_float_binop op) (float_of_int m1.ploc m1) m2, c_int
    | CTpure PTfloat, CTpure PTint ->
	mk_binop l (interp_float_binop op) m1 (float_of_int m2.ploc m2), c_int
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

(*s Purity of C expressions (to give a natural interpretation).

    When [no_effect e] is true, it means that we know [e] has no side effect.
    Beware: it does not mean that [e] can be left in place without
    enforcing evaluation order; e.g.
    [f(x, x++)] cannot be translated to [f(!x, begin x := !x+1; !x end)] 

    [is_pure] really means that [e] is a substitutable expression *)

let rec no_effect = function
  | CEvar _ | CEconstant _ | CEstring_literal _  -> true
  | CEbinary (_, e1, _, e2) -> no_effect e1 && no_effect e2
  | CEunary (_, (Uplus | Uminus | Not), e) -> no_effect e
  | CEunary (_, (Uamp | Ustar), _) -> true
  | CEcond (_, e1, e2, e3) -> no_effect e1 && no_effect e2 && no_effect e3
  | _ -> false

let rec is_pure cenv = function
  | CEvar (l, id) ->
      (match get_type l cenv id with
	 | (CTarray _ | CTpointer _), _
	 | CTpure _, false -> true
	 | _ -> false)
  | CEconstant _ | CEstring_literal _ -> true
  | CEbinary (_, e1, _, e2) -> 
      is_pure cenv e1 && is_pure cenv e2
  | CEunary (_, (Uplus | Uminus | Not), e) -> 
      is_pure cenv e
  | CEunary (_, Uamp, _) ->
      true
  | CEcond (_, e1, e2, e3) -> 
      is_pure cenv e1 && is_pure cenv e2 && is_pure cenv e3
  | _ -> 
      false

(*s Left values *)

type lvalue = 
  | LVid of Loc.t * Ident.t (* ML reference *)
  | LVarr of Loc.t * Ident.t * cexpr

let interp_lvalue cenv = function
  | CEvar (l, id) ->
      (match get_type l cenv id with
	 | CTpure _ as ct, true -> LVid (l, id), ct
	 | _ -> raise_located l (NotAReference id))
  | CEunary (l, Ustar, CEvar (l', id)) ->
      (match get_type l' cenv id with
	 | CTpointer (CTpure _ as ct), true -> LVid (l, id), ct
	 | _ -> raise_located l (AnyMessage "not a left-value"))
  | CEarrget (l, CEvar(l', id), e) ->
      (match get_type l' cenv id with
	 | CTarray ct, _ -> LVarr (l, id, e), ct
	 | _ -> raise_located l' (NotAnArray id))
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
	     | (CTarray _ | CTpointer _) as ct, _ 
	     | ct, false -> ml_var l id , ct 
	     | ct, true -> ml_refget l id, ct)
      | CEassign (l, lv, op, e) -> 
	  let lv, ct = interp_lvalue cenv lv in
	  let mt = interp_expr cenv (Some ct) e in
	  let f v = match op with
	    | Aequal -> mt
	    | _ -> interp_binop l (interp_assign_op op) (v, ct) mt
	  in
	  interp_assignment l cenv et lv f true
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
	  if no_effect e1 && no_effect e2 then
	    let m1 = interp_expr cenv None e1 in
	    let m2 = interp_expr cenv None e2 in
	    interp_binop l op m1 m2
	  else
	    bind l cenv None e1
	      (fun m1 -> bind l cenv None e2
		   (fun m2 -> interp_binop l op m1 m2))
      | CEbinary (l, e1, (Gt | Lt | Ge | Le | Eq | Neq | And | Or), e2) as e ->
	  int_of_bool l (interp_boolean cenv e), c_int
      | CEbinary (l, e1, (Bw_and | Bw_or | Bw_xor as op), e2) ->
	  assert false
      | CEunary (l, (Prefix_inc | Prefix_dec | 
		     Postfix_inc | Postfix_dec as op), lv) ->
	  let lv,ct = interp_lvalue cenv lv in
	  let f v = 
	    interp_binop l (interp_unary_op op) (v, ct) 
	      (ml_const l (ConstInt 1), c_int)
	  in
	  let after = match op with 
	    | Prefix_inc | Prefix_dec -> true 
	    | _ -> false 
	  in
	  interp_assignment l cenv et lv f after
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
      | CEunary (l, Ustar, CEvar (l', id)) ->
	  (match get_type l' cenv id with
	     | CTpointer ct, true -> ml_refget l id, ct
	     | _ -> unsupported l)
      | CEunary (l, Ustar, _) ->
	  unsupported l
      | CEunary (l, Uamp, CEvar (l', id)) ->
	  (match get_type l' cenv id with
	     | CTpure _ as ct, true -> ml_var l id, CTpointer ct
	     | _ -> unsupported l)
      | CEunary (l, Uamp, _) ->
	  unsupported l
      | CEarrget (l, CEvar (l', id), e) ->
	  let m,_ = interp_expr cenv (Some c_int) e in
	  (match get_type l' cenv id with
	     | CTarray ct, _ -> ml_arrget l id m, ct
	     | _ -> raise_located l' (NotAnArray id))
      | CEarrget (l, _, _) ->
	  unsupported l
      | CEnop l ->
	  ml_const l ConstUnit, void
      | CEconstant (l, s) ->
	  (try
	     ml_const l (ConstInt (int_of_string s)), c_int
	   with Failure "int_of_string" ->
	     ml_const l (ConstFloat s), c_float)
      | CEstring_literal (l, _) ->
	  unsupported l
    in
    coerce ml.ploc et ml ct

(*s [interp_assignment lv f] translates the assignement [lv <- f(lv)];
    [after] indicates if the value to return is the value of [lv] after 
    the assignment *)

and interp_assignment l cenv et lv f after =
  if et = Some void then
    (* v <- f(v) *)
    match lv with
     | LVid (_, id) -> 
	 ml_refset l id (fst (f (ml_refget l id))), void
     | LVarr (l', id, e) when is_pure cenv e ->
	 let m,_ = interp_expr cenv (Some c_int) e in
	 ml_arrset l id m (fst (f (ml_arrget l' id m))), void
     | LVarr (l', id, e) ->
	 let m,_ = interp_expr cenv (Some c_int) e in
	 ml_let_tmp l m
	   (fun v -> 
	      let v = ml_var l v in
	      ml_arrset l id v (fst (f (ml_arrget l' id v))), void)
  else if after then
    (* v <- f(v); v *)
    match lv with
     | LVid (_, id) -> 
	 let getit = ml_refget l id in
	 let m,t = f getit in
	 mk_seq l (ml_refset l id m) getit, t
     | LVarr (l', id, e) when is_pure cenv e ->
	 let mi,_ = interp_expr cenv (Some c_int) e in
	 let getit = ml_arrget l' id mi in
	 let m,t = f getit in
	 mk_seq l (ml_arrset l id mi m) getit, t
     | LVarr (l', id, e) ->
	 let mi,_ = interp_expr cenv (Some c_int) e in
	 ml_let_tmp l mi
	   (fun v -> 
	      let v = ml_var l v in
	      let getit = ml_arrget l' id v in
	      let m,t = f getit in
	      mk_seq l (ml_arrset l id v m) getit, t)
  else 
    (* let v0 = v in v <- f(v0); v0 *)
    match lv with
      | LVid (_, id) -> 
	  ml_let_tmp l (ml_refget l id)
	    (fun v0 -> 
	       let m,t = f (ml_refget l id) in
	       mk_seq l (ml_refset l id m) (ml_var l v0), t)
      | LVarr (l', id, e) when is_pure cenv e ->
	  let mi,_ = interp_expr cenv (Some c_int) e in
	  ml_let_tmp l (ml_arrget l' id mi)
	    (fun v0 ->
	       let m,t = f (ml_arrget l' id mi) in
	       mk_seq l (ml_arrset l id mi m) (ml_var l v0), t)
      | LVarr (l', id, e) ->
	  let mi,_ = interp_expr cenv (Some c_int) e in
	  ml_let_tmp l mi
	    (fun vi -> 
	       let vi = ml_var l vi in
	       ml_let_tmp l (ml_arrget l' id vi)
		 (fun v0 ->
		    let m,t = f (ml_arrget l' id vi) in
		    mk_seq l (ml_arrset l id vi m) (ml_var l v0), t))

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
	bind l cenv (Some at) a
	  (fun (m,_) -> interp_args (m :: args) (al, pt))
  in
  match el with
    | [] (* no argument *) ->
	(match pt with 
	   | [] -> assert false
	   | [CTpure PTunit] -> ml_app l f (ml_const l ConstUnit), rt
	   | _ -> raise_located l PartialApp)
    | [e] (* one argument *) ->
	(match pt with 
	   | [] -> assert false
	   | [ct] -> let m,_ = interp_expr cenv (Some ct) e in ml_app l f m, rt
	   | _ -> raise_located l PartialApp)
    | _ ->
	interp_args [] (el, pt)

(*s Monadic operator to enforce evaluation order when needed *)

and bind l cenv et e f =
  let m,t as mt = interp_expr cenv et e in
  if is_pure cenv e then
    f mt
  else
    ml_let_tmp l m (fun x -> f (ml_var l x, t))
    
(*s [interp_boolean] returns an ML expression of type [bool] *)

and interp_boolean cenv = function
  | CEbinary (l, e1, (Gt | Lt | Ge | Le | Eq | Neq as op), e2) ->
      let e,_ = 
	if no_effect e1 && no_effect e2 then
	  let m1 = interp_expr cenv None e1 in
	  let m2 = interp_expr cenv None e2 in
	  interp_binop l op m1 m2
	else
	  bind l cenv None e1
	    (fun m1 -> bind l cenv None e2 (fun m2 -> interp_binop l op m1 m2))
      in
      e
  | CEbinary (l, e1, And, e2) ->
      ml_if l (interp_boolean cenv e1) (interp_boolean cenv e2) (ml_false l)
  | CEbinary (l, e1, Or, e2) ->
      ml_if l (interp_boolean cenv e1) (ml_true l) (interp_boolean cenv e2)
  | CEunary (l, Not, e) ->
      ml_if l (interp_boolean cenv e) (ml_false l) (ml_true l)
  | e ->
      let l = loc_of_expr e in
      let zero = ml_const l (ConstInt 0), c_int in
      let e,_ = 
	if no_effect e then
	  let m,_ as mt = interp_expr cenv None e in 
	  (* OPTIM: directement 0.0 quand float *)
	  interp_binop m.ploc Neq mt zero
	else
	  bind l cenv None e (fun m -> interp_binop l Neq m zero)
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
      let mbl = continue st.continue l mbl in
      let w = mk_expr l (Swhile (interp_boolean cenv s2, i, v, mbl)) in
      let w = break st.break l w in
      mk_seq l m1 w,
      { mt_status with abrupt_return = st.abrupt_return }
  | CSdowhile (l, s, an, e) ->
      (* do s while (e) = s ; while (e) s *)
      interp_statement cenv et abrupt
	(CSblock (l, ([], [s; CSwhile (l, e, an, s)])))
(*** EXP
  | CSwhile (l, e, an, s) when not (no_effect e) ->
      (* turned into [{ v = e; while(v) { s; v = e; } }] *)
      let v = fresh_c_var () in
      let v_e = CSexpr (l, CEassign (l, CEvar (l, v), Aequal, e)) in
      interp_statement cenv et abrupt
	(CSblock (l, ([Ctypedecl (l, CDvar (v, Some e), PTint)],
		      [CSwhile (l, CEvar (l, v), an, 
				CSblock (l, ([], [s; v_e])))])))
***)
  | CSwhile (l, e, an, s) ->
      let (i,v) = interp_loop_annot an in
      let m, st = interp_statement cenv et true s in
      let m = continue st.continue l m in
      let w = mk_expr l (Swhile (interp_boolean cenv e, i, v, m)) in
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
  | CSlabel (l, lab, s) ->
      let m, st = interp_statement cenv et abrupt s in
      mk_seq l (ml_label l lab) m, st
  | CSannot (l, (ofs, a)) ->
      (match interp_c_annot ofs a with
	 | Sassert a -> ml_assert l a, mt_status
	 | Slabel lab -> ml_label l lab, mt_status
	 | _ -> assert false)

(*s C blocks *)

and interp_block l cenv et abrupt (d,b) =
  let rec interp_locals cenv = function
    | [] ->
	cenv, []
    | Cdecl (l, v, d, id , b) :: dl ->
	let v = interp_declarator l v d in
	let m = match b with 
	  | None -> 
	      (match v with
		 | CTpure PTint ->
		     ml_app l (ml_var l any_int) (ml_const l ConstUnit)
		 | CTpure PTunit ->
		     ml_app l (ml_var l any_unit) (ml_const l ConstUnit)
		 | CTpure PTfloat ->
		     ml_app l (ml_var l any_float) (ml_const l ConstUnit)
		 | _ -> 
		     assert false)
	  | Some e -> 
	      let m,_ = interp_expr cenv (Some v) e in m
	in
	let cenv' = Idmap.add id (v, true) cenv in
	let cenv'',lv = interp_locals cenv' dl in
	cenv'', (id, m) :: lv
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
	if st1.always_return then begin
	  wprintf (loc_of_statement (List.hd bl)) "unreachable statement\n";
	  if werror then exit 1
	end;
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
  { pdesc = bl.pdesc; pre = p; oblig = []; post = q; ploc=l }, st.abrupt_return

let interp_binder l (v, d, id) = 
  let t = match interp_declarator l v d with
    | CTpure pt -> PVpure pt
    | CTpointer (CTpure pt) -> PVref (PVpure pt)
    | CTarray (CTpure pt) -> PVarray (PVpure pt)
    | _ -> assert false
  in
  id, BindType t

let interp_binders l = List.map (interp_binder l)

let interp_fun_type l bl v =
  CTfun (List.map (fun (v,d,_) -> interp_declarator l v d) bl, CTpure v), false

let interp_fun id cenv l bl v (l,p,bs,q) =
  let bs,var = 
    let p,var = match interp_c_pre p with
      | None -> [], None
      | Some (p, var) -> list_of_some p, var
    in 
    let q = match interp_c_post q with None -> None | Some q -> q in
    (l, p, bs, q), var 
  in
  let isrec = var <> None in
  let cenv' = 
    let blv = interp_fun_type l bl v in
    let cenv = if isrec then Idmap.add id blv cenv else cenv in
    List.fold_right 
      (fun (v,d,id) -> match interp_declarator l v d with
	 | (CTpure _ as v) -> Idmap.add id (v, false)
	 | (CTpointer _ | CTarray _ as v) -> Idmap.add id (v, true)
	 | _ -> assert false)
      bl cenv 
  in
  return_exception := Ident.create ("Return_" ^ Ident.string id);
  let bs',ar = interp_annotated_block cenv' (CTpure v) bs in
  let e = match var with
    | Some var ->
	mk_ptree l (Srec (id, interp_binders l bl, PVpure v, var, bs')) [] None
    | None -> 
	mk_ptree l (Slam (interp_binders l bl, bs')) [] None
  in
  e, ar
		    
let add_many ids t = List.fold_right (fun id -> Idmap.add id t) ids

let interp_why_decl d cenv = match d with
  | Parameter (_, ids, PVref (PVpure pt)) 
  | External  (_, ids, PVref (PVpure pt)) -> 
      add_many ids (CTpure pt, true) cenv
  | Parameter (_, ids, PVarray (PVpure pt))
  | External  (_, ids, PVarray (PVpure pt)) -> 
      add_many ids (CTarray (CTpure pt), true) cenv
  | Parameter (_, ids, PVpure pt)
  | External  (_, ids, PVpure pt) ->
      add_many ids (CTpure pt, false) cenv
  | Parameter (l, ids, PVarrow (bl, k))
  | External  (l, ids, PVarrow (bl, k)) ->
      let pt = match k.pc_result_type with
	| PVpure pt -> pt
	| _ -> unsupported l
      in
      let binder = function
	| _, BindType v -> ctype_of_pvtype v
	| _ -> unsupported l
      in
      add_many ids (CTfun (List.map binder bl, CTpure pt), false) cenv
  | Parameter (l, _, _) | External (l, _, _) ->
      unsupported l
  | Exception _ | Logic _ -> 
      cenv
  | Program (_, p) ->
      unsupported p.ploc

(*s C declarations *)

let interp_decl cenv = function
  | Cdecl (l, ct, (CDsimple | CDpointer _ | CDarray _ as d), id, _) ->
      (match interp_declarator l ct d with
	 (* pt id; *)
	 | CTpure pt as v -> 
	     [ Parameter (l, [id], PVref (PVpure pt)) ],
	     Idmap.add id (v, true) cenv
         (* pt* id; *)
	 | CTpointer (CTpure pt) as v -> 
	     [ Parameter (l, [id], PVref (PVpure pt)) ],
	     Idmap.add id (v, true) cenv
         (* pt id[]; *)
	 | CTarray (CTpure pt as v) ->
	     [ Parameter (l, [id], PVarray (PVpure pt)) ],
	     Idmap.add id (CTarray v, true) cenv
	 | _ -> 
	     assert false)
  (* pt id(bl); *)
  | Cdecl (l, CTpure pt, CDfunction (CDsimple, bl, an), id, _) -> 
      let bl = if bl = [] then [CTpure PTunit, CDsimple, anonymous] else bl in
      let k = interp_c_spec pt an in
      let blp = interp_binders l bl in
      [ Parameter (l, [id], PVarrow (blp, k)) ],
      Idmap.add id (interp_fun_type l bl pt) cenv
  | Cdecl _ ->
      assert false
  | Cfundef (l, CTpure pt, CDsimple, id, bl, bs) ->
      let bl = if bl = [] then [CTpure PTunit, CDsimple, anonymous] else bl in
      let blv = interp_fun_type l bl pt in
      let e,ar = interp_fun id cenv l bl pt bs in
      let d = [ Program (id, e) ] in
      (if ar then (Exception (l, !return_exception, Some pt)) :: d else d),
      Idmap.add id blv cenv
  | Cfundef _ ->
      assert false
  | Cspecdecl (l,wd) ->
      let d = Parser.parse_c_decl l wd in
      [d], interp_why_decl d cenv

let interp l = 
  let rec interp_list cenv = function
    | [] -> []
    | d :: l -> let d',cenv' = interp_decl cenv d in d' @ interp_list cenv' l
  in
  (Exception (Loc.dummy, break_exception, None)) ::
  (Exception (Loc.dummy, continue_exception, None)) ::
  interp_list Idmap.empty l

***)

open Cast
open Format
open Output
open Info

let interp_type ctype =
  match ctype.ctype_node with
  | CTvoid -> unit_type
  | CTint(sign,cint) -> int_type
  | CTfloat(cfloat) -> assert false (* TODO *)
  | CTarray(t,None) -> base_type "pointer"      
  | CTarray(t,Some e) ->     assert false (* TODO *)
  | _ -> assert false (* TODO *)
(*
  | CTvar of string
  | CTpointer of 'expr ctype
  | CTstruct_named of string
  | CTstruct of string * 'expr field list
  | CTunion_named of string
  | CTunion of string * 'expr field list
  | CTenum_named of string
  | CTenum of string * (string * 'expr option) list
  | CTfun of 'expr parameter list * 'expr ctype
*)

let interp_param (t,id) =
  (* TODO : tester si param is assigned *)
  (id,interp_type t)

let interp_predicate pred =
  match pred with
    | None -> LTrue
    | Some p -> 
	match p with
	  | Clogic.Ptrue -> LTrue
	  | _ -> assert false (* TODO *)

let interp_bin_op op =
  match op with
  | Badd_int -> "add_int"
  | Bsub_int -> "sub_int"
  | Bmul_int -> "mul_int"
  | _ -> assert false (* TODO *)

let rec interp_expr e =
  match e.texpr_node with
    | TEconstant(c) -> Cte(Prim_int(int_of_string c))
    | TEvar(v) -> 
	if v.var_is_assigned then Deref(v.var_name) else Var(v.var_name)
    | TEbinary(e1,op,e2) ->
	App(App(Var(interp_bin_op op),interp_expr e1),interp_expr e2)
    | TEarrget(e1,e2) ->
	let te1 = interp_expr e1
	and te2 = interp_expr e2 
	in
	App(App(Var("acc"),Var("intA")),App(App(Var("shift"),te1),te2))
    | _ -> assert false (* TODO *)
(*
  | TEnop
  | TEstring_literal of string
  | TEdot of lvalue * string
  | TEarrow of lvalue * string
  | TEarrget of lvalue * texpr
  | TEseq of texpr * texpr
  | TEassign of lvalue * assign_operator * texpr
  | TEunary of unary_operator * texpr
  | TEcall of texpr * texpr list
  | TEcond of texpr * texpr * texpr
  | TEcast of texpr ctype * texpr
  | TEsizeof_expr of texpr
  | TEsizeof of texpr ctype
*)

let interp_decl d acc = 
  match d.node with 
    | Tdecl(ctype,v,init) -> 
	fprintf Coptions.log 
	  "translating local declaration of %s@." v.var_name;
	let tinit =
	  match init with 
	    | Inothing ->
(*
		if ctype = c_int then TODO
*)
		  App(Var("any_int"),Var("void"))
	    | Iexpr e -> interp_expr e		
	    | Ilist _ -> assert false (* TODO *)
	in
	if v.var_is_assigned then
	  Let_ref(v.var_name,tinit,acc)
	else
	  Let(v.var_name,tinit,acc)
    | _ -> assert false (* TODO *)

let interp_statement_expr e accu =
  match e.texpr_node with
    | TEassign(l,Aequal,e) ->
	begin
	  match l.texpr_node with
	    | TEvar(v) ->
		append (Assign(v.var_name,interp_expr e)) accu
	    | _ -> assert false (* TODO *)
	end 
    | _ -> assert false (* TODO *)

let rec interp_statement stat acc =
  match stat.st_node with
    | TSexpr e ->
	interp_statement_expr e acc
    | TSreturn eopt ->
	(* TODO: abrupt return *)
	begin
	  match eopt with
	    | None -> Void
	    | Some e -> interp_expr e
	end
    | TSfor(e1,e2,e3,body,info,annot) ->
	let (inv,dec) =
	  match annot with
	    | None -> (LTrue,LConst (Prim_int 0))
	    | Some(i,d) -> assert false (* TODO *)
	in
	append (interp_expr e1)
	  (make_while (interp_expr e2) inv dec 
	     (interp_statement body (interp_expr e3)))
    | _ -> assert false (* TODO *)

and interp_block (decls,stats) =
  let b = List.fold_right interp_statement stats Void in
  List.fold_right interp_decl decls b 

let interp_annotated_block (pre,block,post) =
  let tpre = interp_predicate pre
  and tpost = interp_predicate post
  and tblock = interp_block block 
  in (tpre,tblock,tpost)
      

let interp_located_tdecl why_decls decl =
  match decl.node with
  | Tlogic(idlist,ltype) -> assert false (* TODO *)
  | Ttypedef(ctype,id) -> assert false (* TODO *)
  | Ttypedecl(ctype) -> assert false (* TODO *)
  | Tdecl(ctype,v,init) -> 
      fprintf Coptions.log 
        "translating global declaration of %s@." v.var_name;
      let t = interp_type ctype in
      begin
	match init with 
	  | Inothing ->
	      (Param(v.var_name,Ref_type(t)))::why_decls
	  | _ -> assert false (* TODO *)
      end
  | Tfundef(ctype,id,params,block,info) ->      
      fprintf Coptions.log "translating function %s@." id;
      let tparams = List.map interp_param params in
      let (pre,tblock,post) = interp_annotated_block block in
      (Def(id,Fun(tparams,pre,tblock,post,None)))::why_decls


let interp l =
  List.fold_left interp_located_tdecl [] l


