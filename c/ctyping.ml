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

(*i $Id: ctyping.ml,v 1.46 2004-03-17 17:07:15 filliatr Exp $ i*)

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

let type_location ofs env l = with_offset ofs (type_location env) l
let type_predicate ofs env p = with_offset ofs (type_predicate env) p
let type_spec ?result env (ofs,s) = with_offset ofs (type_spec result env) s
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

let type_op op ty = match ty.ctype_node with 
  | CTint _ | CTenum _ -> int_op op 
  | CTfloat _ -> float_op op 
  | _ -> assert false 

let is_bitfield ty = match ty.ctype_node with
  | CTint (_, Bitfield _) -> true
  | _ -> false

let va_list = Cltyping.noattr (CTvar "va_list")
let _ = add_typedef Loc.dummy "__builtin_va_list" va_list

(* Coercions (ints to floats, floats to int) *)

let coerce ty e = match e.texpr_type.ctype_node, ty.ctype_node with
  | (CTint _ | CTenum _), CTfloat _ -> 
      { e with texpr_node = TEunary (Ufloat_of_int, e); texpr_type = ty }
  | CTfloat _, (CTint _ | CTenum _) ->
      { e with texpr_node = TEunary (Uint_of_float, e); texpr_type = ty }
  | ty1, ty2 when eq_type_node ty1 ty2 ->
      e
  | CTpointer { ctype_node = CTvoid }, CTpointer _ ->
      e
  | _ ->
      if verbose || debug then eprintf 
	"expected %a, found %a@." print_type e.texpr_type print_type ty;
      error e.texpr_loc "incompatible type"

let compat_pointers ty1 ty2 = 
  (ty1.ctype_node = CTvoid) || (ty2.ctype_node = CTvoid) || eq_type ty1 ty2

(* convert [e1] and [e2] to the same arithmetic type *)
let conversion e1 e2 =
  let ty1 = e1.texpr_type in
  let ty2 = e2.texpr_type in
  match ty1.ctype_node, ty2.ctype_node with
    | (CTint _ | CTenum _), (CTint _ | CTenum _) -> e1, e2, ty1
    | CTfloat _, (CTint _ | CTenum _) -> e1, coerce ty1 e2, ty1
    | (CTint _ | CTenum _), CTfloat _ -> coerce ty2 e1, e2, ty2
    | CTfloat _, CTfloat _ -> e1, e2, ty1
    | _ -> assert false

(* type the assignment of [e2] into a left value of type [ty1] *)
let type_assignment loc ty1 e2 =
  let ty2 = e2.texpr_type in
  if (arith_type ty1 && arith_type ty2) || 
     (sub_type ty2 ty1) || 
     (pointer_type ty1 && is_null e2) 
  then
    coerce ty1 e2
  else
    error loc "incompatible types in assignment"

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
  | CTvoid | CTfloat _ as ty -> 
      ty
  | CTint (s,i) ->
      CTint (s, type_integer loc env i)
  | CTvar x -> 
      (* TODO: les attributs sont perdus *)
      (try (find_typedef x).ctype_node with Not_found -> assert false)
  | CTarray (tyn, eo) -> 
      CTarray (type_type loc env tyn, type_int_expr_option env eo)
  | CTpointer tyn -> 
      CTpointer (type_type loc env tyn)
  | CTstruct (_, Tag) | CTunion (_, Tag) | CTenum (_, Tag) as tyn ->
       Env.find_tag_type loc env tyn		       
  | CTstruct (x, Decl fl) ->
      let tyn = CTstruct (x, Decl (List.map (type_field loc env) fl)) in
      Env.find_tag_type loc env tyn
  | CTunion (x, Decl fl) ->
      let tyn = CTunion (x, Decl (List.map (type_field loc env) fl)) in
      Env.find_tag_type loc env tyn
  | CTenum (x, Decl fl) ->
      let type_enum_field (f, eo) = (f, type_int_expr_option env eo) in
      let fl = List.map type_enum_field fl in
      let tyn = Env.find_tag_type loc env (CTenum (x, Decl fl)) in
      let ty = noattr tyn in
      List.iter (fun (f,_) -> add_sym loc f ty (default_var_info f)) fl;
      tyn
  | CTfun (pl, tyn) ->
      let pl = List.map (type_parameter loc env) pl in
      let pl = match pl with
	| [{ctype_node = CTvoid},_] -> []
	| _ -> pl
      in
      CTfun (pl, type_type loc env tyn)

and type_integer loc env = function
  | Char | Short | Int | Long | LongLong as i -> i
  | Bitfield e -> Bitfield (type_expr env e)

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
      let (t,info) =
	try Env.find x env with Not_found -> 
	  try find_sym x with Not_found -> 
	    error loc (x ^ " undeclared")
      in
      (TEvar info,t)
  | CEdot (e, x) ->
      let te = type_expr env e in
      TEdot (te, x), type_of_field loc env x te.texpr_type
  | CEarrow (e, x) ->
      let te = type_expr env e in
      begin match te.texpr_type.ctype_node with
	| CTpointer ty ->
	    TEarrow (te, x), type_of_field loc env x ty
	| _ -> 
	    error loc "invalid type argument of `->'"
      end
  | CEarrget (e1, e2) ->
      let te1 = type_expr env e1 in
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
      let e1_loc = e1.loc in
      let e1 = type_lvalue env e1 in
      warn_for_read_only e1_loc e1;
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let e2 = type_assignment loc ty1 e2 in
      TEassign (e1, e2), ty1
  | CEassign_op (e1, ( Badd | Bsub | Bmul | Bdiv | Bmod 
		     | Bbw_and | Bbw_xor | Bbw_or 
		     | Bshift_left | Bshift_right as op), e2) ->
      let b = { node = CEbinary (e1, op, e2); loc = loc } in
      let b = type_expr env b in
      (match b.texpr_node with
	 | TEbinary (te1, op', te2) -> 
	     check_lvalue e1.loc te1;
	     warn_for_read_only e1.loc te1;
	     let ty1 = te1.texpr_type in
	     let _ = type_assignment loc ty1 b in
	     TEassign_op (te1, op', te2), ty1
	 | _ -> 
	     assert false)
  | CEassign_op _ ->
      assert false
  | CEincr (op, e) ->
      let e_loc = e.loc in
      let e = type_lvalue env e in
      warn_for_read_only e_loc e;
      begin match e.texpr_type.ctype_node with
	| CTenum _ | CTint _ | CTfloat _ | CTpointer _ -> 
            TEincr (op, e), e.texpr_type
	| _ -> error loc "wrong type to {de,in}crement"
      end
  | CEunary (Unot, e) ->
      let e = type_boolean env e in
      TEunary (Unot, e), c_int
  | CEunary ((Uplus | Uminus as op), e) ->
      let e = type_expr env e in
      begin match e.texpr_type.ctype_node with
	| CTenum _ | CTint _ | CTfloat _ -> TEunary (op, e), e.texpr_type
	| _ -> error loc "wrong type argument to unary plus/minus"
      end
  | CEunary (Uamp, e) ->
      (* TODO: cas o� e est une fonction *)
      let e = type_lvalue env e in
      let ty = e.texpr_type in
      if is_bitfield ty then error loc "cannot take address of bitfield";
      if ty.ctype_storage = Register then 
	warning loc "address of register requested";
      TEunary (Uamp, e), noattr (CTpointer ty)
  | CEunary (Ustar, e) ->
      let e = type_expr env e in
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
      let e2 = type_arith_expr env e2 in
      let e1,e2,ty = conversion e1 e2 in
      let op = type_op op ty in 
      TEbinary (e1, op, e2), ty
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
	| (CTenum _ | CTint _ | CTfloat _), (CTint _ | CTfloat _) ->
	    let e1,e2,ty = conversion e1 e2 in
	    TEbinary (e1, type_op Badd ty, e2), ty
	| (CTpointer _ | CTarray _), (CTint _ | CTenum _) -> 
	    TEbinary (e1, Badd_pointer_int, e2), ty1
	| (CTenum _ | CTint _), (CTpointer _ | CTarray _) ->
	    TEbinary (e1, Badd_int_pointer, e2), ty2
	| _ -> error loc "invalid operands to binary +"
      end
  | CEbinary (e1, Bsub, e2) ->
      let e1 = type_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (CTint _ | CTenum _ | CTfloat _), (CTint _ | CTenum _ | CTfloat _) ->
	    let e1,e2,ty = conversion e1 e2 in
	    TEbinary (e1, type_op Bsub ty, e2), ty
	| (CTpointer _ | CTarray _), (CTint _ | CTenum _) -> 
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
	| (CTint _ | CTenum _ | CTfloat _), (CTint _ | CTenum _ | CTfloat _) ->
	    let e1,e2,_ = conversion e1 e2 in
	    TEbinary (e1, op, e2), c_int
	| (CTpointer ty1  | CTarray (ty1,_)), 
	  (CTpointer ty2 | CTarray (ty2,_)) ->
	    if not (compat_pointers ty1 ty2) then
	      warning loc "comparison of distinct pointer types lacks a cast";
	    TEbinary (e1, op, e2), c_int
	| (CTpointer _  | CTarray _), (CTint _ | CTenum _ | CTfloat _)
	| (CTint _ | CTenum _ | CTfloat _), (CTpointer _  | CTarray _) ->
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
  | TEvar _ 
  | TEunary (Ustar, _)
  | TEarrget _ 
  | TEarrow _ 
  | TEdot _ ->
      ()
  | TEcast (_, e) ->
      check_lvalue loc e
  | _ -> 
      error loc "invalid lvalue"

and type_expr_option env eo = option_app (type_expr env) eo

and type_parameter loc env (ty, x) = (type_type loc env ty, x)

and type_field loc env (ty, x, bf) = 
  let ty = type_type loc env ty in
  let bf = type_expr_option env bf in
  match bf, ty.ctype_node with
    | _, CTvoid ->
	error loc ("field `"^x^"' declared void")
    | None, _ ->
	(ty, x, bf)
    | Some e, (CTenum _ | CTint _ as tyn) -> 
	let s = match tyn with
	  | CTenum _ -> Unsigned (* TODO: verif assez de bits pour l'enum *)
	  | CTint (s, Int) -> s
	  | CTint (s, _) ->
	      warning loc ("bit-field `"^x^"' type invalid in ANSI C"); s
	  | _ -> assert false
	in
	({ty with ctype_node = CTint (s, Bitfield e)}, x, bf)
    | Some _, _ -> 
	error loc ("bit-field `"^x^"' has invalid type")

(*s Typing of integers expressions: to be used when coercion is not allowed
    (array subscript, array size, enum value, etc.) *)

and type_int_expr_option env eo = option_app (type_int_expr env) eo

and type_int_expr env e = match type_expr env e with
  | { texpr_type = { ctype_node = CTint _ | CTenum _ } } as te -> te
  | _ -> error e.loc "invalid operand (expected integer)"

(*s Typing of arithmetic expressions: integers or floats *)

and type_arith_expr env e = match type_expr env e with
  | { texpr_type = { ctype_node = CTint _ | CTenum _ | CTfloat _ } } as te -> 
      te
  | _ -> error e.loc "invalid operand (expected integer or float)"

(*s Typing of ``boolean'' expressions *)

and type_boolean env e = 
  let e' = type_expr env e in
  let ty = e'.texpr_type in
  match ty.ctype_node with
    | CTint _ | CTenum _ | CTfloat _ | CTpointer _ | CTarray _ -> e'
    | _ -> error e.loc "invalid operand (expected arith or pointer)"

(*s Typing of initializers *)

let rec type_initializer loc env ty = function
  | Inothing -> 
      Inothing
  | Iexpr e -> 
      let e = type_expr env e in
      Iexpr (coerce ty e)
  | Ilist el -> 
      (match ty.ctype_node with
	 | CTarray (ty, _) ->
	     Ilist (List.map (type_initializer loc env ty) el)
	 | CTstruct (n, _) ->
	     (match tag_type_definition n with
		| Incomplete -> 
		    error loc "initializer but incomplete type"
		| Defined (CTstruct (_, Decl fl)) -> 
		    Ilist (type_struct_initializer loc env fl el)
		| Defined _ -> 
		    assert false)
	 | _ -> 
	     (match el with
		| [] -> error loc "empty initializer"
		| e :: el -> 
		    if el <> [] then 
		      warning loc "excess elements in initializer";
		    Ilist [type_initializer loc env ty e]))

and type_struct_initializer loc env fl el = match fl, el with
  | _, [] -> 
      []
  | (ty,_,_) :: fl, e :: el ->
      let e = type_initializer loc env ty e in
      e :: type_struct_initializer loc env fl el
  | [], _ ->
      error loc "excess elements in struct initializer"

(*s Statements *)

type status = { 
  break : bool; 
  continue : bool; 
  return : bool;
  term : bool
}

let mt_status = 
  { return = false; break = false; continue = false; term = true }

let or_status s1 s2 =
  { return = s1.return || s2.return;
    break = s1.break || s2.break;
    continue = s1.continue || s2.continue;
    term = s1.term || s2.term }

let rec unreachable = function
  | [] -> ()
  | { node = CSlabel _ } :: _ -> ()
  | { node = CSnop } :: bl -> unreachable bl
  | { loc = loc } :: _ ->
      warning loc "unreachable statement";
      if werror then exit 1

let rec type_statement env et s =
  let sn,st = type_statement_node s.loc env et s.node in
  { st_node = sn; 
    st_return = st.return; 
    st_break = st.break;
    st_continue = st.continue;
    st_term = st.term;
    st_loc = s.loc }, st

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
      TSbreak, { mt_status with term = false; break = true }
  | CScontinue -> 
     TScontinue, { mt_status with term = false; continue = true }
  | CSlabel (lab, s) ->
      (* TODO: %default% label not within a switch statement *)
      let s, st = type_statement env et s in
      TSlabel (lab, s), st
  | CSblock bl ->
      let bl,st = type_block env et bl in
      TSblock bl, st
  | CSgoto lab ->
      (* TODO: v�rifier existence label *)
      TSgoto lab, mt_status
  | CSfor (an, e1, e2, e3, s) -> 
      let an = type_loop_annot env an in
      let e1 = type_expr env e1 in
      let e2 = type_boolean env e2 in
      let e3 = type_expr env e3 in
      let s,st = type_statement env et s in
      TSfor (an, e1, e2, e3, s),
      { mt_status with return = st.return }
  | CSdowhile (an, s, e) ->
      let an = type_loop_annot env an in
      let s, st = type_statement env et s in
      let e = type_boolean env e in
      TSdowhile (an, s, e), 
      { mt_status with return = st.return }
  | CSwhile (an, e, s) ->
      let an = type_loop_annot env an in
      let e = type_boolean env e in
      let s, st = type_statement env et s in
      TSwhile (an, e, s), 
      { mt_status with return = st.return }
  | CSreturn None ->
      if et <> None then warning loc 
	      "`return' with no value, in function returning non-void";
      TSreturn None,{ mt_status with term = false; return = true } 
  | CSreturn (Some e) ->
      let e' = type_expr env e in
      let e' = match et with
	| None -> 
	    warning e.loc "`return' with a value, in function returning void";
	    None
	| Some ty ->
	    Some (coerce ty e')
      in
      TSreturn e', { mt_status with term = false; return = true }
  | CSswitch (e, s) ->
      let e = type_int_expr env e in
      let s,st = type_statement env et s in
      TSswitch (e, s), { st with break = false }
  | CScase (e, s) ->
      (* TODO: duplicate case value *)
      let e = type_int_expr env e in
      let s,st = type_statement env et s in
      TScase (e, s), st
  | CSannot (ofs, Assert p) ->
      let p = type_predicate ofs env p in
      TSassert p, mt_status
  | CSannot (_, Label l) ->
      TSlogic_label l, mt_status
  | CSspec (spec, s) ->
      let spec = type_spec env spec in
      let s,st = type_statement env et s in
      TSspec (spec, s), st

and type_block env et (dl,sl) = 
  let rec type_decls env = function
    | [] -> 
	[], env
    | { node = Cdecl (ty, x, i) } as d :: dl ->
	let ty = type_type d.loc env ty in	
	if eq_type_node ty.ctype_node CTvoid then 
	  error d.loc ("variable `"^x^"' declared void");
	let i = type_initializer d.loc env ty i in
	let info = default_var_info x in
	if ty.ctype_storage = Static then info.var_is_static <- true;
	let env' = Env.add x ty info env in
	let dl',env'' = type_decls env' dl in
	{ d with node = Tdecl (ty, info, i) } :: dl', env''
    | { node = Ctypedecl ty } as d :: dl ->
	let ty' = type_type d.loc env ty in
	let dl',env' = type_decls env dl in
	{ d with node = Ttypedecl ty' } :: dl', env'
    | { loc = l } :: _ ->
	error l "unsupported local declaration"
  in
  let dl',env' = type_decls (Env.new_block env) dl in
  let rec type_bl = function
    | [] -> 
	[], mt_status
    | [s] ->
	let s',st = type_statement env' et s in
	[s'], st
    | s :: bl ->
	let s', st1 = type_statement env' et s in
	if not st1.term then unreachable bl;
	let bl', st2 = type_bl bl in
	let st = or_status st1 st2 in
	s' :: bl', { st with term = st2.term }
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
  
let type_logic_parameters env pl = 
  List.fold_right
    (fun (ty,x) (pl,env) ->
       let info = default_var_info x in
       let ty = type_logic_type env ty in 
	       ty :: pl, Env.add x ty info env)
    pl 
    ([], env)

let type_spec_decl ofs = function
  | LDaxiom (id, p) -> 
      Taxiom (id, type_predicate ofs Env.empty p)
  | LDlogic (id, ty, pl, ll) ->
      let ty = type_logic_type Env.empty ty in
      let pl,env' = type_logic_parameters Env.empty pl in
      let ll = List.map (type_location ofs env') ll in
      Cenv.add_fun id.logic_name (pl, ty, id);
      Tlogic (id, Function (pl, ty, ll))
  | LDpredicate_reads (id, pl, ll) ->
      let pl,env' = type_logic_parameters Env.empty pl in
      let ll = List.map (type_location ofs env') ll in
      Cenv.add_pred id.logic_name (pl,id);
      Tlogic (id, Predicate_reads (pl, ll))
  | LDpredicate_def (id, pl, p) ->
      let pl,env' = type_logic_parameters Env.empty pl in
      let p = type_predicate ofs env' p in
      Cenv.add_pred id.logic_name (pl,id);
      Tlogic (id, Predicate_def (pl, p))

let type_decl d = match d.node with
  | Cspecdecl (ofs, s) -> 
      type_spec_decl ofs s
  | Ctypedef (ty, x) -> 
      let ty = type_type d.loc Env.empty ty in
      add_typedef d.loc x ty;
      Ttypedef (ty, x)
  | Ctypedecl ty -> 
      let ty = type_type d.loc Env.empty ty in
      Ttypedecl ty
  | Cdecl (ty, x, i) -> 
      let ty = type_type d.loc Env.empty ty in
      let info = default_var_info x in
      info.var_is_static <- true;
      Loc.report Coptions.log d.loc;
      fprintf Coptions.log "Variable %s is assigned@." info.var_name;
      info.var_is_assigned <- true;
      add_sym d.loc x ty info;
      Tdecl (ty, info, type_initializer d.loc Env.empty ty i)
  | Cfunspec (s, ty, f, pl) ->
      let ty = type_type d.loc Env.empty ty in
      let pl,env = type_parameters d.loc Env.empty pl in
      let s = type_spec ~result:ty env s in
      let info = default_var_info f in
      add_sym d.loc f (noattr (CTfun (pl, ty))) info;
      Tfunspec (s, ty, info, pl)
  | Cfundef (s, ty, f, pl, bl) -> 
      let ty = type_type d.loc Env.empty ty in
      let et = if eq_type ty c_void then None else Some ty in
      let pl,env = type_parameters d.loc Env.empty pl in
      let s = option_app (type_spec ~result:ty env) s in
      let info = default_var_info f in
      add_sym d.loc f (noattr (CTfun (pl, ty))) info;
      let bl,st = type_statement env et bl in
      if st.term && et <> None then
	warning d.loc "control reaches end of non-void function";
      if st.break then 
	error d.loc "break statement not within a loop or switch";
      if st.continue then 
	error d.loc "continue statement not within a loop";
      Tfundef (s, ty, info, pl, bl)

let type_file = List.map (fun d -> { d with node = type_decl d })

