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

(*i $Id: cinterp.ml,v 1.7 2002-11-20 16:57:04 filliatr Exp $ i*)

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
let c_bool = CTpure PTbool

let rec print_ctype fmt = function
  | CTpure PTint -> fprintf fmt "int"
  | CTpure PTfloat -> fprintf fmt "float"
  | CTpure PTbool -> assert false
  | CTpure PTunit -> fprintf fmt "void"
  | CTpure (PTexternal id ) -> Ident.print fmt id
  | CTpure (PTarray (s, pt)) -> 
      fprintf fmt "%a[%a]" print_pure_type pt print_term s
  | CTpointer ct -> fprintf fmt "%a*" print_ctype ct
  | CTarray ct -> fprintf fmt "%a[]" print_ctype ct
  | CTfun (ctl, ct) -> 
      fprintf fmt "%a (%a)" print_ctype ct (print_list comma print_ctype) ctl

(* the environment gives the C type, together with the type of the variable
   in the ML translation *)

type cenv = (ctype * type_v) Ident.map

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

let ml_const c = mk_expr Loc.dummy (Sconst c)
let ml_var l id = mk_expr l (Svar id)
let ml_refget l id = mk_expr l (Srefget id)
let ml_refset l id e = mk_expr l (Srefset (id, e))
let ml_if l e1 e2 e3 = mk_expr l (Sif (e1, e2, e3))
let ml_let_tmp l e1 e2 = 
  let tmp = fresh_var () in mk_expr l (Sletin (tmp, e1, e2 tmp))

let c_true = ml_const (ConstInt 1)
let c_false = ml_const (ConstInt 0)

let int_of_bool l e = mk_expr l (Sif (e, c_true, c_false))

let ml_float_of_int l e = 
  mk_expr l (Sapp (ml_var Loc.dummy t_float_of_int, Sterm e))

(*s Binary operations *)

let interp_binop = function
  | Plus -> t_add
  | Minus -> t_sub
  | Mult -> t_mul
  | Div -> t_div
  | Mod -> t_mod_int
  | Lt -> t_lt
  | Gt -> t_gt
  | Le -> t_le
  | Ge -> t_ge
  | Eq -> t_eq
  | Neq -> t_neq
  | _ -> assert false

let mk_binop l op e1 e2 =
  mk_expr l (Sapp (mk_expr l (Sapp (mk_expr l (Svar op), Sterm e1)), Sterm e2))

(*s Coercion of [e] of type [t] to an expected type [et] *)

let coerce l et e t = match et with
  | Some (CTpure PTfloat as et) when t = c_int -> 
      ml_float_of_int l e, et
  | Some et when et <> t ->
      raise_located l (ExpectedType (fun f -> print_ctype f et))
  | _ ->
      e, t

(*s Purity of C expressions (to give a natural interpretation) *)

let rec is_pure = function
  | CEvar _ | CEconst _  -> true
  | CEbinary (_, e1, _, e2) -> is_pure e1 && is_pure e2
  | CEunary (_, _, e) -> is_pure e
  | CEcond (_, e1, e2, e3) -> is_pure e1 && is_pure e2 && is_pure e3
  | _ -> false

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
	     | ct, Ref _ -> ml_refget l id, ct
	     | ct, _ -> ml_var l id , ct)
      | CEassign (l, CEvar (_,id), Aequal, e) -> 
	  (match get_type l cenv id with
	     | ct, Ref _ -> 
		 let m,t = interp_expr cenv (Some ct) e in
		 if et = Some void then
		   ml_refset l id m, void
		 else
		   mk_seq l (ml_refset l id m) (ml_refget l id), t
	     | _ -> 
		 raise_located l (NotAReference id))
      | CEassign _ ->
	  assert false
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
	  assert false;
(***
	  List.fold_left 
	    (fun f a -> mk_expr l (Sapp (f, Sterm (interp_expr a))))
	    (interp_expr e) el
***)
      | CEbinary (l, e1, (Plus | Minus | Mult | Div | Mod as op), e2) ->
	  let m1,t1 = interp_expr cenv None e1 in
	  let m2,t2 = interp_expr cenv None e2 in
	  assert (t1 = t2); (* TODO: int/float *)
	  let op = interp_binop op in
	  if is_pure e1 then
	    mk_binop l op m1 m2, t1
	  else
	    (* let tmp = e1 in tmp op e2 *)
	    ml_let_tmp l m1 (fun x -> mk_binop l op (ml_var l x) m2), t1
      | CEbinary (l, e1, (Gt | Lt | Ge | Le | Eq | Neq | And | Or), e2) as e ->
	  int_of_bool l (interp_boolean cenv e), c_int
      | CEbinary (l, e1, (Bw_and | Bw_or | Bw_xor as op), e2) ->
	  assert false
      | CEunary (l, Prefix_inc, CEvar (_, id)) ->
	  (match get_type l cenv id with
	     | ct, Ref _ -> 
		 let getid = ml_refget l id in
		 let incrid = (* id := !id + 1 *)
		   ml_refset l id 
		     (mk_binop l (interp_binop Plus) 
			getid (ml_const (ConstInt 1)))
		 in
		 if et = Some void then 
		   incrid, void
		 else 
		   mk_seq l incrid getid, ct
	     | _ -> 
		 raise_located l (NotAReference id))
      | CEunary _ ->
	  assert false
      | CEarrget _ ->
	  assert false
      | CEconst (l, s) ->
	  ml_const (ConstInt (int_of_string s)), c_int
    in
    coerce ml.loc et ml ct

and interp_boolean cenv = function
  | CEbinary (l, e1, (Gt | Lt | Ge | Le | Eq | Neq as op), e2) ->
      let m1,t1 = interp_expr cenv None e1 in
      let m2,t2 = interp_expr cenv None e2 in
      assert (t1 = t2); (* TODO: int/float *)
      mk_binop l (interp_binop op) m1 m2
  | CEbinary (l, e1, And, e2) ->
      ml_if l (interp_boolean cenv e1) (interp_boolean cenv e2) c_false
  | CEbinary (l, e1, Or, e2) ->
      ml_if l (interp_boolean cenv e1) c_true (interp_boolean cenv e2)
  | e ->
      let e,t = interp_expr cenv None e in 
      assert (t = c_int); (* TODO: float *)
      mk_binop e.loc t_neq e (ml_const (ConstInt 0))

let append_to_block l s1 s2 = match s1, s2 with
  | _, None -> s1
  | CSblock (_, (d, bl)), Some s2 -> CSblock (l, (d, bl @ [s2]))
  | _, Some s2 -> CSblock (l, ([], [s1; s2]))

(* TODO: vérifier [et] *)
let rec interp_statement cenv et = function
  | CSexpr (_, e) -> 
      let m,_ = interp_expr cenv et e in m
  | CSblock (l, bl) ->
      mk_expr l (interp_block cenv bl)
  | CSfor (l, s1, s2, e3, an, s) ->
      let (i,v) = interp_loop_annot an in
      let s3 = option_app (fun e -> CSexpr (l, e)) e3 in
      let bl = append_to_block l s s3 in
      mk_seq l 
	(interp_statement cenv (Some void) s1) 
	(mk_expr l (Swhile (interp_statement cenv (Some c_bool) s2, Some i, v, 
			    interp_statement cenv (Some void) bl)))
  | CSdowhile _ ->
      assert false
  | CSwhile (l, e, an, s) ->
      let (i,v) = interp_loop_annot an in
      mk_expr l
	(Swhile (interp_boolean cenv e, Some i, v, 
		 interp_statement cenv (Some void) s))
  | CScond (l, e1, s2, s3) ->
      mk_expr l 
	(Sif (interp_boolean cenv e1, 
	      interp_statement cenv et s2, interp_statement cenv et s3))
  | CSnop l ->
      mk_expr l (Sconst ConstUnit)
  | CSreturn _ ->
      assert false

(* TODO: passer un [et] *)
and interp_block cenv (d,b) =
   assert (d = []);
   Sseq (List.map 
	   (fun s -> Sstatement (interp_statement cenv (Some void) s)) b)

let interp_annotated_block cenv (l, p, bl, q) =
  { pdesc = interp_block cenv bl;
    pre = interp_c_pre p; post = interp_c_post q; loc = l }

let interp_binder (pt, id) = (id, BindType (PVpure pt))

let interp_binders = List.map interp_binder

let interp_fun cenv l bl v bs =
  mk_ptree l (Slam (interp_binders bl, interp_annotated_block cenv bs)) [] None

let interp_decl cenv = function
  | Ctypedecl (l, CDvar id, v) -> 
      Parameter (l, [id], PVref (PVpure v)),
      Idmap.add id (CTpure v, Ref (PureType v)) cenv
  | Ctypedecl (l, CDfun (id, bl, an), v) -> 
      let bl = if bl = [] then [PTunit, anonymous] else bl in
      let k = interp_c_spec v an in
      let bl = List.map (fun (v, id) -> (id, BindType (PVpure v))) bl in
      Parameter (l, [id], PVarrow (bl, k)),
      cenv (* TODO *)
  | Ctypedecl _ -> 
      assert false
  | Cfundef (l, id, bl, v, bs) ->
      let bl = if bl = [] then [PTunit, anonymous] else bl in
      Program (id, interp_fun cenv l bl v bs),
      cenv (* TODO *)

let interp = 
  let rec interp_list cenv = function
    | [] -> []
    | d :: l -> let d',cenv' = interp_decl cenv d in d' :: interp_list cenv' l
  in
  interp_list Idmap.empty
