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

(*i $Id: ctyping.ml,v 1.29 2004-02-13 08:42:08 filliatr Exp $ i*)

open Format
open Coptions
open Clogic
open Cast
open Cerror
open Cltyping
open Creport
open Info
open Cenv

(* Typing C programs *)

let located_app f x = { node = f x.node; loc = x.loc }

let option_app f = function Some x -> Some (f x) | None -> None

let offset ofs (ls, le) = (ofs + ls, ofs + le)

let with_offset ofs f x =
  try
    f x
  with 
    | Stdpp.Exc_located (loc, e) -> 
	raise (Stdpp.Exc_located (offset ofs loc, e))
    | Error (Some loc, e) ->
	raise (Error (Some (offset ofs loc), e))

let type_predicate ofs env p = with_offset ofs (type_predicate env) p
let type_spec ty env (ofs,s) = with_offset ofs (type_spec ~result:ty env) s
let type_loop_annot env (ofs,a) = with_offset ofs (type_loop_annot env) a

(*s Some predefined types, subtype relation, etc. *)

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


(* Coercions (ints to floats, floats to int) *)

let coerce ty e = match e.texpr_type.ctype_node, ty.ctype_node with
  | CTint _, CTfloat _ -> 
      { e with texpr_node = TEunary (Ufloat_of_int, e); texpr_type = ty }
  | CTfloat _, CTint _ ->
      { e with texpr_node = TEunary (Uint_of_float, e); texpr_type = ty }
  | ty1, ty2 when eq_type_node ty1 ty2 ->
      e
  | CTpointer { ctype_node = CTvoid }, CTpointer _ ->
      e
  | _ ->
      if verbose || debug then eprintf 
	"expected %a, found %a@." print_type e.texpr_type print_type ty;
      error e.texpr_loc "incompatible type"

(* warns for assigments over read-only left-value *)

let warn_for_read_only loc e = 
  let pointer_on_read_only ty = match ty.ctype_node with
    | CTpointer ty -> ty.ctype_const 
    | _ -> false
  in
  match e.texpr_node with
  | TEarrow (_, x) | TEdot (_, x) when e.texpr_type.ctype_const  ->
      warning loc ("assigment of read-only member `" ^ x ^ "'")
  | TEarrow (e1, x) when pointer_on_read_only e1.texpr_type ->
      warning loc ("assigment of read-only member `" ^ x ^ "'")
  | TEdot (e1, x) when e1.texpr_type.ctype_const ->
      warning loc ("assigment of read-only member `" ^ x ^ "'")
  | TEvar x when e.texpr_type.ctype_const ->
      warning loc ("assigment of read-only variable `" ^ x.var_name ^ "'")
  | TEvar x ->
      Loc.report Coptions.log loc;
      fprintf Coptions.log "Variable %s is assigned@." x.var_name;
      x.var_is_assigned <- true
  | _ when e.texpr_type.ctype_const ->
      warning loc "assigment of read-only location"
  | _ -> 
      ()

(*s Types *)

let rec type_type loc env ty = 
  { ty with ctype_node = type_type_node loc env ty.ctype_node }

and type_type_node loc env = function
  | CTvoid | CTint _ | CTfloat _ as ty -> 
      ty
  | CTvar x -> 
      (* TODO: les attributs sont perdus *)
      (try (find_typedef x).ctype_node with Not_found -> assert false)
  | CTarray (tyn, eo) -> 
      CTarray (type_type loc env tyn, type_int_expr_option env eo)
  | CTpointer tyn -> 
      CTpointer (type_type loc env tyn)
  | CTstruct_named x | CTunion_named x | CTenum_named x as ty ->
      begin 
	try 
	  (Env.find_tag_type x env).ctype_node
	with Not_found -> 
	  (* TODO: may fail on "storage size of `x' isn't known" *)
	  ty
      end
  | CTstruct (x, fl) ->
      CTstruct (x, List.map (type_field loc env) fl)
  | CTunion (x, fl) ->
      CTunion (x, List.map (type_field loc env) fl)
  | CTenum (x, fl) ->
      let type_enum_field (f, eo) = (f, type_int_expr_option env eo) in
      CTenum (x, List.map type_enum_field fl)
  | CTfun (pl, tyn) ->
      CTfun (List.map (type_parameter loc env) pl, type_type loc env tyn)

(* type a type and adds it to the local env if it is a declaration *)
and declare_local_type l ty env = 
  let ty' = type_type l env ty in
  match ty.ctype_node with
    | CTstruct (n,_) | CTunion (n,_) | CTenum (n,_) -> 
	ty', Env.add_tag_type l n ty' env
    | _ -> 
	ty', env

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
      let (t,var_info) =
	try Env.find x env with Not_found -> 
	  try find_sym x with Not_found -> 
	    error loc (x ^ " undeclared")
      in
      (TEvar var_info),t
  | CEdot (e, x) ->
      let te = type_lvalue env e in
      begin match te.texpr_type.ctype_node with
	| CTstruct (_,fl) ->
	    TEdot (te, x), type_of_struct_field loc x fl
	| CTunion (_,fl) -> 
	    TEdot (te, x), type_of_union_field loc x fl
	| CTstruct_named _ | CTunion_named _ ->
            error loc "use of incomplete type"
	| _ -> 
	    error loc ("request for member `" ^ x ^ 
		       "' in something not a structure or union")
      end
  | CEarrow (e, x) ->
      let te = type_lvalue env e in
      begin match te.texpr_type.ctype_node with
	| CTpointer { ctype_node = CTstruct (_,fl) } -> 
	    TEarrow (te, x), type_of_struct_field loc x fl
	| CTpointer { ctype_node = CTunion (_,fl) } -> 
	    TEarrow (te, x), type_of_union_field loc x fl
	| CTpointer { ctype_node = CTstruct_named _ | CTunion_named _ } ->
	    error loc "dereferencing pointer to incomplete type"
	| CTpointer _ ->
	    error loc ("request for member `" ^ x ^ 
		       "' in something not a structure or union")
	| _ -> 
	    error loc "invalid type argument of `->'"
      end
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
  | CEassign (e1, e2) ->
      let e1loc = e1.loc in
      let e1 = type_lvalue env e1 in
      warn_for_read_only e1loc e1;
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      if (arith_type ty1 && arith_type ty2) || 
	(sub_type ty2 ty1) || 
	(pointer_type ty1 && is_null e2) 
      then
	TEassign (e1, coerce ty1 e2), ty1
      else
	error loc "incompatible types in assignment"
  | CEassign_op (e1, ( Badd | Bsub | Bmul | Bdiv | Bmod 
		     | Bbw_and | Bbw_xor | Bbw_or 
		     | Bshift_left | Bshift_right as op), e2) ->
      (match type_expr_node loc env (CEbinary (e1, op, e2)) with
	 | TEbinary (te1, op', te2), ty -> 
	     check_lvalue e1.loc te1;
	     TEassign_op (te1, op', te2), te1.texpr_type (* TODO type ok? *)
	 | _ -> 
	     assert false)
  | CEassign_op _ ->
      assert false
  | CEincr (op, e) ->
      let e = type_lvalue env e in
      begin match e.texpr_type.ctype_node with
	| CTint _ | CTfloat _ | CTpointer _ -> TEincr (op, e), e.texpr_type
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
      (* TODO: cas où e est une fonction *)
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
	    (* TODO: warning pointeurs types différents *)
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
      let e = type_expr env e in
      let el = List.map (type_expr env) el in
      begin match e.texpr_type.ctype_node with
	| CTfun (tl, ty) ->
	    let rec check_args i el' = function
	      | [], [] -> 
		  TEcall (e, List.rev el'), ty
	      | e :: el, (t, _) :: tl when sub_type e.texpr_type t ->
		  check_args (succ i) (coerce t e :: el') (el, tl)
	      | e :: _, _ :: _ ->
		  error loc ("incompatible type for argument " ^ 
			     string_of_int i)
	      | [], _ :: _ ->
		  error loc "too few arguments"
	      | el, [] ->
		  (* too many arguments is OK *)
		  TEcall (e, List.rev_append el' el), ty
	    in
	    check_args 1 [] (el, tl)
	| _ ->
	    (* TODO should be: warning: implicit declaration of function *)
	    error loc "not a function"
      end
  | CEcast (ty, e) ->
      let ty = type_type loc env ty in
      let e = type_expr env e in
      TEcast (ty, e), ty
  | CEsizeof_expr e ->
      let e = type_expr env e in
      TEsizeof_expr e, c_int
  | CEsizeof ty ->
      let ty = type_type loc env ty in
      TEsizeof ty, c_int

and type_lvalue env e = 
  let loc = e.loc in
  let e = type_expr env e in
  check_lvalue loc e;
  e

and check_lvalue loc e = match e.texpr_node with
  | TEvar _ | TEunary _ | TEarrget _ -> ()
  | _ -> error loc "invalid lvalue"

and type_expr_option env eo = option_app (type_expr env) eo

and type_parameter loc env (ty, x) = (type_type loc env ty, x)

and type_field loc env (ty, x, bf) = 
  (type_type loc env ty, x, type_expr_option env bf)

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

let seq_status s1 s2 =
  { always_return = s1.always_return || s2.always_return;
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
      (* TODO: vérifier existence label *)
      TSgoto lab, mt_status
  | CSfor (an, e1, e2, e3, s) -> 
      let an = type_loop_annot env an in
      let e1 = type_expr env e1 in
      let e2 = type_boolean env e2 in
      let e3 = type_expr env e3 in
      let s,st = type_statement env et s in
      let li = { loop_break = st.break; loop_continue = st.continue } in
      TSfor (an, e1, e2, e3, s, li),
      { mt_status with abrupt_return = st.abrupt_return }
  | CSdowhile (an, s, e) ->
      let an = type_loop_annot env an in
      let s, st = type_statement env et s in
      let e = type_boolean env e in
      let li = { loop_break = st.break; loop_continue = st.continue } in
      TSdowhile (an, s, e, li), 
      { mt_status with abrupt_return = st.abrupt_return }
  | CSwhile (an, e, s) ->
      let an = type_loop_annot env an in
      let e = type_boolean env e in
      let s, st = type_statement env et s in
      let li = { loop_break = st.break; loop_continue = st.continue } in
      TSwhile (an, e, s, li), 
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
  | CSannot (ofs, Assert p) ->
      let p = type_predicate ofs env p in
      TSassert p, mt_status
  | CSannot (_, Label l) ->
      TSlogic_label l, mt_status

and type_block env et (dl,sl) = 
  let rec type_decls env = function
    | [] -> 
	[], env
    | { node = Cdecl (ty, x, i) } as d :: dl ->
	(* TODO: ty = void interdit *)
	let ty',env' = declare_local_type d.loc ty env in
	let i = type_initializer env ty' i in
	let info = default_var_info x in
	let env' = Env.add x ty' info env' in
	let dl',env'' = type_decls env' dl in
	{ d with node = Tdecl (ty', info, i) } :: dl', env''
    | { node = Ctypedecl ty } as d :: dl ->
	let ty',env' = declare_local_type d.loc ty env in
	let dl',env'' = type_decls env' dl in
	{ d with node = Ttypedecl ty' } :: dl', env''
    | { loc = l } :: _ ->
	error l "unsupported local declaration"
  in
  let dl',env' = type_decls env dl in
  let rec type_bl = function
    | [] -> 
	[], mt_status
    | [s] ->
	let s',st = type_statement env' et s in
	[s'], st
    | s :: bl ->
	let s', st1 = type_statement env' et s in
	if st1.always_return then begin
	  warning (List.hd bl).loc "unreachable statement";
	  if werror then exit 1
	end;
	let bl', st2 = type_bl bl in
	s' :: bl', seq_status st1 st2
  in
  let sl', st = type_bl sl in
  (dl', sl'), st


let type_parameters loc env pl =
  List.fold_right
    (fun (ty,x) (pl,env) ->
       let info = default_var_info x in
       let ty = type_type loc env ty in (ty,x) :: pl, Env.add x ty info env)
    pl 
    ([], env)
  
let declare_type l ty = 
  let ty' = type_type l Env.empty ty in
  match ty.ctype_node with
  | CTstruct (n,_) | CTunion (n,_) | CTenum (n,_) -> add_tag_type l n ty'; ty'
  | _ -> ty'

let type_logic_parameters env = 
  List.map (fun (ty, _) -> type_logic_type env ty)

let type_spec_decl ofs = function
  | LDaxiom (id, p) -> 
      Taxiom (id, type_predicate ofs Env.empty p)
  | LDlogic (s, ty, pl) ->
      let ty = type_logic_type Env.empty ty in
      let pl = type_logic_parameters Env.empty pl in
      Cenv.add_fun s (pl, ty);
      Tlogic (s, Function (pl, ty))
  | LDpredicate (s, pl) ->
      let pl = type_logic_parameters Env.empty pl in
      Cenv.add_pred s pl;
      Tlogic (s, Predicate pl)

let type_decl d = match d.node with
  | Cspecdecl (ofs, s) -> 
      type_spec_decl ofs s
  | Ctypedef (ty, x) -> 
      let ty = declare_type d.loc ty in
      add_typedef d.loc x ty;
      Ttypedef (ty, x)
  | Ctypedecl ty -> 
      let ty = declare_type d.loc ty in
      Ttypedecl ty
  | Cdecl (ty, x, i) -> 
      let ty = declare_type d.loc ty in
      add_sym d.loc x ty;
      let info = default_var_info x in
      Tdecl (ty, info, type_initializer Env.empty ty i)
  | Cfunspec (s, ty, f, pl) ->
      let ty = type_type d.loc Env.empty ty in
      let pl,env = type_parameters d.loc Env.empty pl in
      let s = type_spec ty env s in
      add_sym d.loc f (noattr (CTfun (pl, ty)));
      Tfunspec (s, ty, f, pl)
  | Cfundef (s, ty, f, pl, bl) -> 
      let ty = type_type d.loc Env.empty ty in
      let et = if ty = c_void then None else Some ty in
      let pl,env = type_parameters d.loc Env.empty pl in
      let s = option_app (type_spec ty env) s in
      add_sym d.loc f (noattr (CTfun (pl, ty)));
      let bl,st = type_block env et bl in
      if not st.always_return && et <> None then
	warning d.loc "control reaches end of non-void function";
      if st.break then 
	error d.loc "break statement not within a loop or switch";
      if st.continue then 
	error d.loc "continue statement not within a loop";
      let fi = { fun_abrupt_return = st.abrupt_return } in
      Tfundef (s, ty, f, pl, bl, fi)

let type_file = List.map (fun d -> { d with node = type_decl d })

