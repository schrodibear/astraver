(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filli�tre - Claude March�
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

(*i $Id: ctyping.ml,v 1.8 2003-12-24 15:06:42 filliatr Exp $ i*)

open Format
open Coptions
open Cast
open Cerror
open Creport

(* Typing C programs *)

let located_app f x = { node = f x.node; loc = x.loc }

let option_app f = function Some x -> Some (f x) | None -> None

let error l s = raise (Error (Some l, AnyMessage s))
let warning l s = 
  Format.eprintf "%a warning: %s\n" Loc.report_line (fst l) s

(*s Pretty-printing of types *)

let rec print_type fmt t = match t.ctype_node with
  | CTvoid -> fprintf fmt "void"
  | CTint (s, i) -> fprintf fmt "%a %a" print_sign s print_integer i
  | CTfloat f -> print_float fmt f
  | CTvar x -> fprintf fmt "%s" x
  | CTarray (ty, None) -> fprintf fmt "%a[]" print_type ty
  | CTarray (ty, Some e) -> fprintf fmt "%a[_]" print_type ty
  | CTpointer ty -> fprintf fmt "%a*" print_type ty
  | CTstruct_named x -> fprintf fmt "struct %s" x
  | CTstruct_decl (_, fl) -> fprintf fmt "struct _ { %a}" print_fields fl
  | CTunion_named x -> fprintf fmt "union %s" x
  | CTunion_decl (_, fl) -> fprintf fmt "union _ { %a}" print_fields fl
  | CTenum_named x -> fprintf fmt "enum %s" x
  | CTenum_decl (_, el) -> fprintf fmt "enum _ { %a}" print_enums el
  | CTfun (pl, ty) -> fprintf fmt "%a fun(...)" print_type ty

and print_sign fmt = function
  | Signed -> fprintf fmt "signed"
  | Unsigned -> fprintf fmt "unsigned"

and print_integer fmt = function
  | Char -> fprintf fmt "char"
  | Short -> fprintf fmt "short"
  | Int -> fprintf fmt "int"
  | Long -> fprintf fmt "long"
  | LongLong -> fprintf fmt "long long"

and print_float fmt = function
  | Float -> fprintf fmt "float"
  | Double -> fprintf fmt "double"
  | LongDouble -> fprintf fmt "long double"

and print_fields fmt = function
  | [] -> ()
  | (ty, x, _) :: fl -> fprintf fmt "%a %s; %a" print_type ty x print_fields fl

and print_enums fmt = function
  | [] -> ()
  | (x, _) :: el -> fprintf fmt "%s, %a" x print_enums el

(*s Some predefined types, subtype relation, etc. *)

let noattr tyn = { ctype_node = tyn; 
		   ctype_storage = No_storage;
		   ctype_const = false;
		   ctype_volatile = false }
let c_void = noattr CTvoid
let c_int = noattr (CTint (Signed, Int))
let c_char = noattr (CTint (Unsigned, Char))
let c_float = noattr (CTfloat Float)
let c_string = noattr (CTpointer c_char)

let int_op = function
  | Badd -> Badd_int
  | Bsub -> Bsub_int
  | Bmul -> Bmul_int
  | Bdiv -> Bdiv_int
  | Bmod -> Bmod_int
  | _ -> assert false

let float_op = function
  | Badd -> Badd_float
  | Bsub -> Bsub_float
  | Bmul -> Bmul_float
  | Bdiv -> Bdiv_float
  | _ -> assert false

(* Type equality (i.e. structural equality, but ignoring attributes) *)
(* TODO: pointers = arrays *)

let rec eq_type ty1 ty2 = 
  eq_type_node ty1.ctype_node ty2.ctype_node

and eq_type_node tn1 tn2 = match tn1, tn2 with
  | CTvoid, CTvoid
  | CTint _, CTint _ 
  | CTfloat _, CTfloat _ ->
      true
  | CTvar x1, CTvar x2 ->
      x1 = x2
  | CTarray (ty1, _), CTarray (ty2, _) ->
      eq_type ty1 ty2 (* TODO: taille? *)
  | CTpointer ty1, CTpointer ty2 ->
      eq_type ty1 ty2
  | CTstruct_named s1, CTstruct_named s2 ->
      s1 = s2
  | CTstruct_decl _, _ | _, CTstruct_decl _ ->
      assert false
  | CTunion_named u1, CTunion_named u2 ->
      u1 = u2
  | CTunion_decl _, _ | _, CTunion_decl _ ->
      assert false
  | CTenum_named e1, CTenum_named e2 ->
      e1 = e2
  | CTenum_decl _, _ | _, CTenum_decl _ ->
      assert false
  | CTfun (pl1, ty1), CTfun (pl2, ty2) ->
      eq_type ty1 ty2 &&
      (try List.for_all2 (fun (ty1,_) (ty2,_) -> eq_type ty1 ty2) pl1 pl2
       with Invalid_argument _ -> false)
  | _ ->
      false

(* [sub_type ty1 ty2] is true if type [ty1] can be coerced
   to type [ty2] (with function [coerce] below) *)

let sub_type ty1 ty2 = match ty1.ctype_node, ty2.ctype_node with
  | CTint _, CTfloat _ -> true
  | _ -> eq_type ty1 ty2

let compatible ty1 ty2 = sub_type ty1 ty2 || sub_type ty2 ty1

(* Coercions (ints to floats, floats to int) *)

let coerce ty e = match e.texpr_type.ctype_node, ty.ctype_node with
  | CTint _, CTfloat _ -> 
      { e with texpr_node = TEunary (Ufloat_of_int, e); texpr_type = ty }
  | CTfloat _, CTint _ ->
      { e with texpr_node = TEunary (Uint_of_float, e); texpr_type = ty }
  | ty1, ty2 when eq_type_node ty1 ty2 ->
      e
  | _ ->
      if verbose || debug then eprintf 
	"expected %a, found %a@." print_type e.texpr_type print_type ty;
      error e.texpr_loc "incompatible type"

(*s Environments for local variables *)

module Env = Map.Make(String)

(*s Logic *)

let rec type_predicate env p = 
  assert false (*TODO*)

let type_loop_annot env a =
  assert false (*TODO*)

(*s Types *)

let rec type_type ty = { ty with ctype_node = type_type_node ty.ctype_node }

and type_type_node = function
  | CTvoid | CTint _ | CTfloat _ as ty -> 
      ty
  | CTvar _ as ty -> 
      ty (* TODO: qq chose � v�rifier ici ? *)
  | CTarray (tyn, eo) -> 
      (* TODO: v�rifier type int *)
      CTarray (type_type tyn, type_int_expr_option Env.empty eo)
  | CTpointer tyn -> 
      CTpointer (type_type tyn)
  | CTstruct_named x | CTunion_named x | CTenum_named x as ty ->
      (* TODO: v�rifier existence *)
      ty
  | CTstruct_decl (x, fl) ->
      CTstruct_decl (x, List.map type_field fl)
  | CTunion_decl (x, fl) ->
      CTunion_decl (x, List.map type_field fl)
  | CTenum_decl (x, fl) ->
      let type_enum_field (f, eo) = (f, type_int_expr_option Env.empty eo) in
      CTenum_decl (x, List.map type_enum_field fl)
  | CTfun (pl, tyn) ->
      CTfun (List.map type_parameter pl, type_type tyn)

(*s Expressions *)

and type_expr env e = 
  let tn,ty = type_expr_node e.loc env e.node in
  { texpr_node = tn; texpr_type = ty; texpr_loc = e.loc }

and type_expr_node loc env = function
  | CEnop ->
      TEnop, c_void
  | CEconstant s ->
      (try 
	 let _ = int_of_string s in TEconstant s, c_int
       with _ -> 
	 TEconstant s, c_float)
  | CEstring_literal s ->
      TEstring_literal s, c_string
  | CEvar x ->
      (* TODO: global *)
      (try TEvar x, Env.find x env 
       with Not_found -> error loc (x ^ " undeclared"))
  | CEdot (e, x) ->
      let te = type_lvalue env e in
      assert false (*TODO type_of_field te.texpr_type x *)
  | CEarrow (e, x) ->
      let te = type_lvalue env e in
      assert false (*TODO type_of_field te.texpr_type x *)
  | CEarrget (e1, e2) ->
      let te1 = type_lvalue env e1 in
      (match te1.texpr_type.ctype_node with
	 | CTarray (ty, _) | CTpointer ty ->
	     let te2 = type_int_expr env e2 in
	     TEarrget (te1, te2), ty
	 | _ ->
	     error loc "subscripted value is neither array nor pointer")
  | CEseq (e1, e2) ->
      let e1 = type_expr env e1 in
      let e2 = type_expr env e2 in
      TEseq (e1, e2), e2.texpr_type
  | CEcond (e1, e2, e3) ->
      let e1 = type_boolean env e1 in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      let e3 = type_expr env e3 in
      let ty3 = e3.texpr_type in
      if sub_type ty2 ty3 then
	TEcond (e1, coerce ty3 e2, e3), ty3
      else if sub_type ty3 ty2 then
	TEcond (e1, e2, coerce ty2 e3), ty2
      else
	error loc "type mismatch in conditional expression"
  | CEassign (e1, op, e2) ->
      let e1 = type_lvalue env e1 in
      let e2 = type_expr env e2 in
      begin match op with
	| Aequal ->
	    assert false (*TODO*)
	| Amul | Adiv | Aadd | Asub -> 
            assert false (*TODO*)
	| Amod | Aleft | Aright 
	| Aand | Axor | Aor ->
	    assert false (*TODO*)
      end
  | CEunary ((Uprefix_inc|Uprefix_dec|Upostfix_inc|Upostfix_dec as op), e) ->
      let e = type_lvalue env e in
      begin match e.texpr_type.ctype_node with
	| CTint _ | CTfloat _ | CTpointer _ -> TEunary (op, e), e.texpr_type
	| _ -> error loc "wrong type to {de,in}crement"
      end
  | CEunary (Unot, e) ->
      let e = type_boolean env e in
      TEunary (Unot, e), c_int
  | CEunary ((Uplus | Uminus as op), e) ->
      let e = type_expr env e in
      begin match e.texpr_type.ctype_node with
	| CTint _ | CTfloat _ -> TEunary (op, e), e.texpr_type
	| _ -> error loc "wrong type argument to unary plus/minus"
      end
  | CEunary (Uamp, e) ->
      (* TODO: cas o� e est une fonction *)
      (* TODO: exclure champ de bit et register *)
      let e = type_lvalue env e in
      TEunary (Uamp, e), noattr (CTpointer e.texpr_type)
  | CEunary (Ustar, e) ->
      let e = type_lvalue env e in
      begin match e.texpr_type.ctype_node with
	| CTpointer ty | CTarray (ty, _) -> TEunary (Ustar, e), ty
	| _ -> error loc "invalid type argument of `unary *'"
      end
  | CEunary (Utilde, e) ->
      let e = type_int_expr env e in
      TEunary (Utilde, e), e.texpr_type
  (* these other unops cannot be built by the parser *)
  | CEunary ((Uint_of_float | Ufloat_of_int), _) ->
      assert false
  | CEbinary (e1, (Bmul | Bdiv as op), e2) ->
      let e1 = type_arith_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_arith_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| CTint _, CTint _ -> TEbinary (e1, int_op op, e2), ty1
	| CTfloat _, CTint _ -> TEbinary (e1, float_op op, coerce ty1 e2), ty1
	| CTint _, CTfloat _ -> TEbinary (coerce ty2 e1, float_op op, e2), ty2
	| CTfloat _, CTfloat _ -> TEbinary (e1, float_op op, e2), ty1
	| _ -> assert false
      end
  | CEbinary (e1, Bmod, e2) ->
      let e1 = type_int_expr env e1 in
      let e2 = type_int_expr env e2 in
      TEbinary (e1, Bmod, e2), e1.texpr_type (* TODO: max ty1 ty2 ? *)
  | CEbinary (e1, Badd, e2) ->
      let e1 = type_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| CTint _, CTint _ -> TEbinary (e1, Badd_int, e2), ty1
	| CTint _ , CTfloat _ -> TEbinary (coerce ty2 e1, Badd_float, e2), ty2
	| CTfloat _ , CTint _ -> TEbinary (e1, Badd_float, coerce ty1 e2), ty1
	| CTfloat _ , CTfloat _ -> TEbinary (e1, Badd_float, e2), ty2
	| (CTpointer _ | CTarray _), CTint _ -> 
	    TEbinary (e1, Badd_pointer_int, e2), ty1
	| CTint _, (CTpointer _ | CTarray _) ->
	    TEbinary (e1, Badd_int_pointer, e2), ty2
	| _ -> error loc "invalid operands to binary +"
      end
  | CEbinary (e1, Bsub, e2) ->
      let e1 = type_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| CTint _, CTint _ -> TEbinary (e1, Bsub_int, e2), ty1
	| CTint _ , CTfloat _ -> TEbinary (coerce ty2 e1, Bsub_float, e2), ty2
	| CTfloat _ , CTint _ -> TEbinary (e1, Bsub_float, coerce ty1 e2), ty1
	| CTfloat _ , CTfloat _ -> TEbinary (e1, Bsub_float, e2), ty2
	| (CTpointer _ | CTarray _), CTint _ -> 
	    TEbinary (e1, Bsub_pointer_int, e2), ty1
	| (CTpointer _ | CTarray _), (CTpointer _ | CTarray _) ->
	    TEbinary (e1, Bsub_pointer, e2), ty2
	| _ -> error loc "invalid operands to binary -"
      end
  | CEbinary (e1, (Blt | Bgt | Ble | Bge | Beq | Bneq as op), e2) ->
      let e1 = type_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| CTint _, CTint _ -> TEbinary (e1, op, e2), c_int
	| CTint _ , CTfloat _ -> TEbinary (coerce ty2 e1, op, e2), c_int
	| CTfloat _ , CTint _ -> TEbinary (e1, op, coerce ty1 e2), c_int
	| CTfloat _ , CTfloat _ -> TEbinary (e1, op, e2), c_int
	| (CTpointer _  | CTarray _), (CTpointer _  | CTarray _) ->
	    (* TODO: warning pointeurs types diff�rents *)
	    TEbinary (e1, op, e2), c_int
	| (CTpointer _  | CTarray _), (CTint _ | CTfloat _)
	| (CTint _ | CTfloat _), (CTpointer _  | CTarray _) ->
	    warning loc "comparison between pointer and integer";
	    TEbinary (e1, op, e2), c_int
	| _ ->
	    error loc "invalid operands to comparison"
      end
  | CEbinary (e1, (Band | Bor as op), e2) ->
      let e1 = type_boolean env e1 in
      let e2 = type_boolean env e2 in
      TEbinary (e1, op, e2), c_int
  | CEbinary (e1, ( Bbw_and | Bbw_xor | Bbw_or 
		  | Bshift_left | Bshift_right as op), e2) ->
      (* TODO: max types pour "&" "|" "^" ? *)
      let e1 = type_int_expr env e1 in
      let e2 = type_int_expr env e2 in
      TEbinary (e1, op, e2), e1.texpr_type
  (* these other binops cannot be built by the parser *)
  | CEbinary (_, (Bdiv_float|Bmul_float|Bsub_float|Badd_float
		 |Bmod_int|Bdiv_int|Bmul_int|Bsub_int|Badd_int
		 |Bsub_pointer|Bsub_pointer_int
		 |Badd_int_pointer|Badd_pointer_int), _) ->
      assert false
  | CEcall (e, el) ->
      assert false (*TODO*)
  | CEcast (ty, e) ->
      let ty = type_type ty in
      let e = type_expr env e in
      TEcast (ty, e), ty
  | CEsizeof_expr e ->
      let e = type_expr env e in
      TEsizeof_expr e, c_int
  | CEsizeof ty ->
      let ty = type_type ty in
      TEsizeof ty, c_int

and type_lvalue env e = type_expr env e (*TODO*)

and type_expr_option env eo = option_app (type_expr env) eo

and type_parameter (ty, x) = (type_type ty, x)

and type_field (ty, x, bf) = (type_type ty, x, type_expr_option Env.empty bf)

(*s Typing of integers expressions: to be used when coercion is not allowed
    (array subscript, array size, enum value, etc.) *)

and type_int_expr_option env eo = option_app (type_int_expr env) eo

and type_int_expr env e = match type_expr env e with
  | { texpr_type = { ctype_node = CTint _ } } as te -> te
  | _ -> error e.loc "invalid operand (expected integer)"

(*s Typing of arithmetic expressions: integers or floats *)

and type_arith_expr env e = match type_expr env e with
  | { texpr_type = { ctype_node = CTint _ | CTfloat _ } } as te -> te
  | _ -> error e.loc "invalid operand (expected integer or float)"

(*s Typing of ``boolean'' expressions *)

and type_boolean env e = 
  let e' = type_expr env e in
  let ty = e'.texpr_type in
  match ty.ctype_node with
    | CTint _ | CTfloat _ | CTpointer _ | CTarray _ -> e'
    | _ -> error e.loc "invalid operand (expected arith or pointer)"

(*s Typing of initializers *)

let rec type_initializer env ty = function
  | Inothing -> 
      Inothing
  | Iexpr e -> 
      let e = type_expr env e in
      Iexpr (coerce ty e)
  | Ilist el -> 
      assert false (* TODO *)
      (* Ilist (List.map (type_initializer env ty) el) (* FAUX! *) *)

(*s Statements *)

type status = { 
  always_return : bool; 
  abrupt_return : bool;
  break : bool; 
  continue : bool }

let mt_status = 
  { always_return = false; abrupt_return = false; 
    break = false; continue = false }

let or_status s1 s2 =
  { always_return = s1.always_return && s2.always_return;
    abrupt_return = s1.abrupt_return || s2.abrupt_return;
    break = s1.break || s2.break;
    continue = s1.continue || s2.continue }

let rec type_statement env et s =
  let sn,st = type_statement_node s.loc env et s.node in
  { st_node = sn; st_abrupt_return = st.abrupt_return; st_loc = s.loc }, st

and type_statement_node loc env et = function
  | CSnop -> 
      TSnop, mt_status
  | CSexpr e ->
      let e = type_expr env e in
      TSexpr e, mt_status
  | CSif (e, s1, s2) ->
      let e = type_boolean env e in
      let s1,st1 = type_statement env et s1 in
      let s2,st2 = type_statement env et s2 in
      TSif (e, s1, s2), or_status st1 st2
  | CSbreak ->
      TSbreak, { mt_status with break = true }
  | CScontinue -> 
     TScontinue, { mt_status with continue = true }
  | CSlabel (lab, s) ->
      let s, st = type_statement env et s in
      TSlabel (lab, s), st
  | CSblock bl ->
      let bl,st = type_block env et bl in
      TSblock bl, st
  | CSgoto lab ->
      (* TODO: v�rifier existence label *)
      TSgoto lab, mt_status
  | CSfor (e1, e2, e3, an, s) ->
      let an = type_loop_annot env an in
      let e1 = type_expr env e1 in
      let e2 = type_boolean env e2 in
      let e3 = type_expr env e3 in
      let s,st = type_statement env et s in
      let li = { loop_break = st.break; loop_continue = st.continue } in
      TSfor (e1, e2, e3, s, li, an),
      { mt_status with abrupt_return = st.abrupt_return }
  | CSdowhile (s, an, e) ->
      let an = type_loop_annot env an in
      let s, st = type_statement env et s in
      let e = type_boolean env e in
      let li = { loop_break = st.break; loop_continue = st.continue } in
      TSdowhile (s, e, li, an), 
      { mt_status with abrupt_return = st.abrupt_return }
  | CSwhile (e, an, s) ->
      let an = type_loop_annot env an in
      let e = type_boolean env e in
      let s, st = type_statement env et s in
      let li = { loop_break = st.break; loop_continue = st.continue } in
      TSwhile (e, s, li, an), 
      { mt_status with abrupt_return = st.abrupt_return }
  | CSreturn None ->
      if et <> None then warning loc 
	      "`return' with no value, in function returning non-void";
      TSreturn None,{ mt_status with always_return = true } 
  | CSreturn (Some e) ->
      let e' = type_expr env e in
      let e' = match et with
	| None -> 
	    warning e.loc "`return' with a value, in function returning void";
	    None
	| Some ty ->
	    Some (coerce ty e')
      in
      TSreturn e', { mt_status with always_return = true }
  | CSswitch (e, s) ->
      assert false (*TODO*)
  | CScase (e, s) ->
      assert false (*TODO*)
  | CSannot an ->
      assert false (*TODO*)

and type_block env et (dl,sl) = 
  let rec type_decls env = function
    | [] -> 
	[], env
    | { node = Cdecl (ty, x, i) } as d :: dl ->
	(* TODO: ty = void interdit *)
	let ty = type_type ty in
	let i = type_initializer env ty i in
	let env' = Env.add x ty env in
	let dl',env'' = type_decls env' dl in
	{ d with node = Tdecl (ty, x, i) } :: dl', env''
    | { loc = l } :: _ ->
	error l "unsupported local declaration"
  in
  let dl',env' = type_decls env dl in
  let rec type_bl = function
    | [] -> 
	[], mt_status
    | [s] ->
	let s',st = type_statement env' et s in
	if not st.always_return && et <> None then
	  warning s.loc "control reaches end of non-void function";
	[s'], st
    | s :: bl ->
	let s', st1 = type_statement env' et s in
	if st1.always_return then begin
	  warning (List.hd bl).loc "unreachable statement";
	  if werror then exit 1
	end;
	let bl', st2 = type_bl bl in
	s' :: bl', or_status st1 st2
  in
  let sl', st = type_bl sl in
  (dl', sl'), st


and type_annotated_block env et (p,bl,q) =
  let bl,st = type_block env et bl in
  let p = option_app (type_predicate env) p in
  let q = option_app (type_predicate env) q in
  (p, bl, q), st

let type_parameters pl =
  List.fold_right
    (fun (ty,x) (pl,env) ->
       let ty = type_type ty in (ty,x)::pl, Env.add x ty env)
    pl 
    ([], Env.empty)
  
let type_decl d = match d.node with
  | Cspecdecl a -> 
      assert false (*TODO*)
  | Ctypedef (ty, x) -> 
      Ttypedef (type_type ty, x)
  | Ctypedecl ty -> 
      Ttypedecl (type_type ty)
  | Cdecl (ty, x, i) -> 
      let ty = type_type ty in
      Tdecl (ty, x, type_initializer Env.empty ty i)
  | Cfundef (ty, f, pl, bl) -> 
      let ty = type_type ty in
      let et = if ty = c_void then None else Some ty in
      let pl,env = type_parameters pl in
      (* TODO: ajouter f plutot comme global + v�rif si d�j� d�clar�e *)
      let env = Env.add f (noattr (CTfun (pl, ty))) env in
      let bl,st = type_annotated_block env et bl in
      if st.break then 
	error d.loc "break statement not within a loop or switch";
      if st.continue then 
	error d.loc "continue statement not within a loop";
      let fi = { fun_abrupt_return = st.abrupt_return } in
      Tfundef (ty, f, pl, bl, fi)

let type_file = List.map (fun d -> { d with node = type_decl d })

