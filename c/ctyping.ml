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

(*i $Id: ctyping.ml,v 1.100 2005-11-08 14:55:14 filliatr Exp $ i*)

open Format
open Coptions
open Clogic
open Cast
open Cerror
open Cltyping
open Creport
open Info
open Cenv
open Lib
open Ctypes
open Int64


let int_teconstant n = 
  { texpr_node = TEconstant (IntConstant n); 
    texpr_loc = Loc.dummy_position;
    texpr_type = c_int }

let tezero = int_teconstant "0"


(* evaluation static *)
let rec sizeof loc = 
  let incomplete_type () = 
    error loc "invalid application of `sizeof' to an incomplete type"
  in
  let warned = ref false in
  let architecture () =
    if not !warned then begin 
      warned := true;
      warning loc "compiler/architecture-dependent sizeof"
    end
  in
  let rec sizeof ?(field=false) (ty : tctype) = match ty.ctype_node with
    | Tvoid -> of_int 1
    | Tint (_, Char) -> of_int 1 
    | Tint (_, Short) -> of_int 2
    | Tint (_, Int) -> architecture (); of_int 4
    | Tint (_, Long) -> of_int 4
    | Tint (_, LongLong) -> of_int 8
    | Tint (_, Bitfield n) -> 
	architecture ();
	let d = div n (of_int 8) in
	if rem n (of_int 8) = zero then d else succ d
    | Tfloat Float -> of_int 4
    | Tfloat Double -> of_int 8
    | Tfloat LongDouble -> of_int 12
    | Tvar x -> assert false (* should be expansed *)
    | Tarray (ty, Some e) -> 
	mul e (sizeof ty)
    | Tarray (ty, None) -> if field then of_int 0 else of_int 1
    | Tpointer _ -> of_int 4
    | Tstruct n ->
	(match tag_type_definition n with
	   | TTIncomplete -> 
	       incomplete_type ()
	   | TTStructUnion (Tstruct _, fl) -> 
	       List.fold_left 
		 (fun s v -> add s (sizeof ~field:true v.var_type)) 
		 (of_int 0) fl
	   | _ -> 
	       assert false)
    | Tunion n ->
	(match tag_type_definition n with
	   | TTIncomplete -> 
	       incomplete_type ()
	   | TTStructUnion (Tunion _, fl) -> 
	       List.fold_left 
		 (fun s v -> max s (sizeof ~field:true v.var_type)) 
		 (of_int 0) fl
	   | _ -> 
	       assert false)
    | Tenum _ -> of_int 4
    | Tfun _ -> of_int 4 (* function pointer? *)
  in
  sizeof

and eval_const_expr (e : texpr) = match e.texpr_node with
  | TEconstant (IntConstant c) -> Cconst.int e.texpr_loc c
  | TEunary (Uplus, t) -> eval_const_expr t
  | TEunary (Cast.Uminus, t) -> Int64.neg (eval_const_expr t)
  | TEbinary (t1, Cast.Badd_int, t2) -> 
      Int64.add (eval_const_expr t1)  (eval_const_expr t2)
  | TEbinary (t1, Cast.Bsub_int, t2) -> 
      Int64.sub (eval_const_expr t1)  (eval_const_expr t2)
  | TEbinary (t1, Cast.Bmul_int, t2) -> 
      Int64.mul (eval_const_expr t1)  (eval_const_expr t2)
  | TEbinary (t1, Cast.Bdiv_int, t2) -> 
      Int64.div (eval_const_expr t1)  (eval_const_expr t2)
  | TEcast (_, e) -> eval_const_expr e
  | TEsizeof (t,n) -> n
  | TEvar (Var_info v) ->
      if e.texpr_type.Ctypes.ctype_const 
      then v.enum_constant_value
      else error e.texpr_loc "not a const variable"
  | _ -> error e.texpr_loc "not a constant expression"

(* Typing C programs *)

let located_app f x = { node = f x.node; loc = x.loc }

let option_app f = function Some x -> Some (f x) | None -> None

let type_spec ?result env s = type_spec result env s


(*s Some predefined types, subtype relation, etc. *)

let int_op = function
  | Badd -> Badd_int
  | Bsub -> Bsub_int
  | Bmul -> Bmul_int
  | Bdiv -> Bdiv_int
  | Bmod -> Bmod_int
  | Blt -> Blt_int
  | Ble -> Ble_int
  | Bgt -> Bgt_int
  | Bge -> Bge_int
  | Beq -> Beq_int
  | Bneq -> Bneq_int
  | _ -> assert false

let float_op = function
  | Badd -> Badd_float
  | Bsub -> Bsub_float
  | Bmul -> Bmul_float
  | Bdiv -> Bdiv_float
  | Blt -> Blt_float
  | Ble -> Ble_float
  | Bgt -> Bgt_float
  | Bge -> Bge_float
  | Beq -> Beq_float
  | Bneq -> Bneq_float
  | _ -> assert false

let pointer_op = function
  | Blt -> Blt_pointer
  | Ble -> Ble_pointer
  | Bgt -> Bgt_pointer
  | Bge -> Bge_pointer
  | Beq -> Beq_pointer
  | Bneq -> Bneq_pointer
  | _ -> assert false

let type_op op ty = match ty.ctype_node with 
  | Tint _ | Tenum _ -> int_op op 
  | Tfloat _ -> float_op op 
  | Tpointer _ | Tarray _ -> pointer_op op
  | _ -> assert false 

let is_bitfield ty = match ty.ctype_node with
  | Tint (_, Bitfield _) -> true
  | _ -> false

let va_list = Ctypes.noattr (Ctypes.Tvar "va_list")
let _ = add_typedef Loc.dummy_position "__builtin_va_list" va_list

(* Coercions (ints to floats, floats to int) *)

let coerce ty e = match e.texpr_type.ctype_node, ty.ctype_node with
  | (Tint _ | Tenum _), Tfloat _ -> 
      { e with texpr_node = TEunary (Ufloat_of_int, e); texpr_type = ty }
  | Tfloat _, (Tint _ | Tenum _) ->
      { e with texpr_node = TEunary (Uint_of_float, e); texpr_type = ty }
  | ty1, ty2 when eq_type_node ty1 ty2 ->
      e
  | Tpointer { ctype_node = Tvoid }, Tpointer _ ->
      e
  | _ ->
      if verbose || debug then eprintf 
	"expected %a, found %a@." print_type ty print_type e.texpr_type;
      error e.texpr_loc "incompatible type"

let compat_pointers ty1 ty2 = 
  (ty1.ctype_node = Tvoid) || (ty2.ctype_node = Tvoid) || eq_type ty1 ty2

(* convert [e1] and [e2] to the same arithmetic type *)
let conversion e1 e2 =
  let ty1 = e1.texpr_type in
  let ty2 = e2.texpr_type in
  match ty1.ctype_node, ty2.ctype_node with
    | (Tint _ | Tenum _), (Tint _ | Tenum _) -> e1, e2, ty1
    | Tfloat _, (Tint _ | Tenum _) -> e1, coerce ty1 e2, ty1
    | (Tint _ | Tenum _), Tfloat _ -> coerce ty2 e1, e2, ty2
    | Tfloat _, Tfloat _ -> e1, e2, ty1
    | _ -> assert false

let is_null e = 
  match e.texpr_node with
    | TEconstant (IntConstant s) -> (try int_of_string s = 0 with _ -> false)
    | _ -> false


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
    | Tpointer ty -> ty.ctype_const 
    | _ -> false
  in
  match e.texpr_node with
  | TEarrow (_, x) | TEdot (_, x) when e.texpr_type.ctype_const  ->
      warning loc ("assignment of read-only member `" ^ x.var_name ^ "'")
  | TEarrow (e1, x) when pointer_on_read_only e1.texpr_type ->
      warning loc ("assignment of read-only member `" ^ x.var_name ^ "'")
  | TEdot (e1, x) when e1.texpr_type.ctype_const ->
      warning loc ("assignment of read-only member `" ^ x.var_name ^ "'")
  | TEvar (Var_info x) when e.texpr_type.ctype_const ->
      warning loc ("assignment of read-only variable `" ^ x.var_name ^ "'")
  | TEvar (Var_info x) ->
      Loc.report_position Coptions.log loc;
      fprintf Coptions.log "Variable %s is assigned@." x.var_name;
      set_assigned x
  | TEvar (Fun_info f) ->
      warning loc ("function assignment (ignored)")
  | _ when e.texpr_type.ctype_const ->
      warning loc "assigment of read-only location"
  | _ -> 
      ()

let set_referenced e = match e.texpr_node with
  | TEvar (Var_info x) -> set_is_referenced x
  | TEdot (_,f) | TEarrow(_,f) -> set_is_referenced f
  | _ -> ()

(*s Types *)

let rec type_type loc env ty = 
  { Ctypes.ctype_node = type_type_node loc env ty.Cast.ctype_node;
    ctype_storage = ty.Cast.ctype_storage ;
    ctype_const = ty.Cast.ctype_const ;
    ctype_volatile = ty.Cast.ctype_volatile;
    ctype_ghost = false;
  }

and type_type_node loc env = function
  | CTvoid -> Tvoid
  | CTfloat x -> Tfloat x
  | CTint (s,i) ->
      Tint (s, type_integer loc env i)
  | CTvar x -> 
      (* TODO: les attributs sont perdus *)
      (try (find_typedef x).ctype_node with Not_found -> assert false)
  | CTarray (tyn, None) ->
      Tarray (type_type loc env tyn, None)
  | CTarray (tyn, Some e) -> 
      Tarray (type_type loc env tyn , 
	      Some (eval_const_expr  (type_int_expr env e)))
  | CTpointer tyn -> 
      Tpointer (type_type loc env tyn)
  | CTstruct (x,Tag) -> Env.find_tag_type loc env (Tstruct x)  
  | CTunion (x,Tag)  -> Env.find_tag_type loc env (Tunion x)
  | CTenum (x,Tag)  -> Env.find_tag_type loc env (Tenum x)
  | CTstruct (x, Decl fl) ->
      let fl = List.map (type_field x loc env) fl in
      let tyn = 
	Env.set_struct_union_type loc env (Tstruct x) (List.map snd fl) in
      declare_fields tyn fl;
      tyn
  | CTunion (x, Decl fl) ->
      let fl = List.map (type_field x loc env) fl in
      let tyn = Env.set_struct_union_type loc env (Tunion x) (List.map snd fl) in
      declare_fields tyn fl;
      tyn
  | CTenum (x, Decl fl) ->
      let tyn = Env.find_tag_type loc env (Tenum x) in
      let ty = noattr tyn in
      let ty = { ty with ctype_const = true } in
      let rec enum_fields v = function
	| [] -> 
	    []
	| (f, op) :: fl ->
	     let i = default_var_info f in
	     ignore (add_sym loc f ty (Var_info i)); 
	     let v = match op with
	       | None -> 
		   v
	       | Some e -> 
		   let e = type_int_expr env e in
		   eval_const_expr e
	     in
	     set_const_value i v;
	     (i, v) :: enum_fields (Int64.succ v) fl
      in
      let fl = enum_fields Int64.zero fl in
      Env.set_enum_type loc env (Tenum x) fl 
  | CTfun (pl, tyn) ->
      let pl = List.map (fun (ty,x) -> type_type loc env ty) pl in
      let pl = match pl with
	| [{ctype_node = Tvoid}] -> []
	| _ -> pl
      in
      Tfun (pl, type_type loc env tyn)

and type_integer loc env = function
  | Cast.Char -> Char
  | Cast.Short -> Short
  | Cast.Int -> Int 
  | Cast.Long -> Long
  | Cast.LongLong -> LongLong
  | Cast.Bitfield e -> 
      let e = type_int_expr env e in
      Bitfield (eval_const_expr e)

(*s Expressions *)

and type_expr env e = 
  let tn,ty = type_expr_node e.loc env e.node in
  { texpr_node = tn; texpr_type = ty; texpr_loc = e.loc }

and type_expr_node loc env = function
  | CEnop ->
      TEnop, c_void
  | CEconstant (IntConstant _ as c) ->
      TEconstant c, c_int
  | CEconstant (FloatConstant _ as c) ->
      TEconstant c, c_float
  | CEstring_literal s ->
      TEstring_literal s, c_string
  | CEvar x ->
      let var =
	try Env.find x env with Not_found -> 
	  try find_sym x with Not_found -> 
	    error loc (x ^ " undeclared")
      in
      (TEvar var,var_type var)
  | CEdot (e, x) ->
      let te = type_expr env e in
      let x = type_of_field loc x te.texpr_type in
      let te_dot_x = match te.texpr_node with
	| TEunary (Ustar, e) -> TEarrow (e, x)
	| TEarrget (e1, e2) -> 
	    let a = 
	      { te with 
		  texpr_node = TEbinary (e1, Badd_pointer_int, e2);
		  texpr_type = e1.texpr_type }
	    in
	    TEarrow (a, x)
	| _ -> TEdot (te, x)
      in
      te_dot_x, x.var_type
  | CEarrow (e, x) ->
      let te = type_expr env e in
      begin match te.texpr_type.ctype_node with
	| Tarray (ty,_) | Tpointer ty ->
	    let x = type_of_field loc x ty in
	    TEarrow (te, x), x.var_type
	| _ -> 
	    error loc "invalid type argument of `->'"
      end
  | CEarrget (e1, e2) ->
      let te1 = type_expr env e1 in
      (match te1.texpr_type.ctype_node with
	 | Tarray (ty,_) | Tpointer ty ->
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
	| Tenum _ | Tint _ | Tfloat _ | Tpointer _ -> 
            TEincr (op, e), e.texpr_type
	| _ -> error loc "wrong type to {de,in}crement"
      end
  | CEunary (Unot, e) ->
      let e = type_boolean env e in
      TEunary (Unot, e), c_int
  | CEunary ((Uplus | Uminus as op), e) ->
      let e = type_expr env e in
      begin match e.texpr_type.ctype_node with
	| Tenum _ | Tint _ | Tfloat _ -> TEunary (op, e), e.texpr_type
	| _ -> error loc "wrong type argument to unary plus/minus"
      end
  | CEunary (Uamp, e) ->
      (* TODO: cas où e est une fonction *)
      let e = type_lvalue env e in
      let ty = e.texpr_type in
      if is_bitfield ty then error loc "cannot take address of bitfield";
      if ty.ctype_storage = Register then 
	warning loc "address of register requested";
      set_referenced e;
      TEunary (Uamp, e), noattr (Tpointer ty)
  | CEunary (Ustar, e) ->
      let e = type_expr env e in
      begin match e.texpr_type.ctype_node with
	| Tpointer ty | Tarray (ty,_) -> TEunary (Ustar, e), ty
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
      TEbinary (e1, Bmod_int, e2), e1.texpr_type (* TODO: max ty1 ty2 ? *)
  | CEbinary (e1, Badd, e2) ->
      let e1 = type_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (Tenum _ | Tint _ | Tfloat _), (Tint _ | Tfloat _) ->
	    let e1,e2,ty = conversion e1 e2 in
	    TEbinary (e1, type_op Badd ty, e2), ty
	| (Tpointer _ | Tarray _), (Tint _ | Tenum _) -> 
	    TEbinary (e1, Badd_pointer_int, e2), ty1
	| (Tenum _ | Tint _), (Tpointer _ | Tarray _) ->
	    TEbinary (e2, Badd_pointer_int, e1), ty2
	| _ -> error loc "invalid operands to binary +"
      end
  | CEbinary (e1, Bsub, e2) ->
      let e1 = type_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (Tint _ | Tenum _ | Tfloat _), (Tint _ | Tenum _ | Tfloat _) ->
	    let e1,e2,ty = conversion e1 e2 in
	    TEbinary (e1, type_op Bsub ty, e2), ty
	| (Tpointer _ | Tarray _), (Tint _ | Tenum _) -> 
	    let me2 = { e2 with texpr_node = TEunary (Uminus, e2);
			  texpr_type = ty2 } in
	    TEbinary (e1, Badd_pointer_int, me2), ty1
	| (Tpointer _ | Tarray _), (Tpointer _ | Tarray _) ->
	    TEbinary (e1, Bsub_pointer, e2), c_int (* TODO check types *)
	| _ -> error loc "invalid operands to binary -"
      end
  | CEbinary (e1, (Blt | Bgt | Ble | Bge | Beq | Bneq as op), e2) ->
      let e1 = type_expr env e1 in
      let ty1 = e1.texpr_type in
      let e2 = type_expr env e2 in
      let ty2 = e2.texpr_type in
      begin match ty1.ctype_node, ty2.ctype_node with
	| (Tint _ | Tenum _ | Tfloat _), (Tint _ | Tenum _ | Tfloat _) ->
	    let e1,e2,ty = conversion e1 e2 in
	    TEbinary (e1, type_op op ty, e2), c_int
	| (Tpointer ty1  | Tarray (ty1,_)), 
	  (Tpointer ty2 | Tarray (ty2,_)) ->
	    if not (compat_pointers ty1 ty2) then
	      warning loc "comparison of distinct pointer types lacks a cast";
	    TEbinary (e1, pointer_op op, e2), c_int
	| (Tpointer _  | Tarray _), (Tint _ | Tenum _ | Tfloat _)
	| (Tint _ | Tenum _ | Tfloat _), (Tpointer _  | Tarray _) ->
	    warning loc "comparison between pointer and integer";
	    TEbinary (e1, pointer_op op, e2), c_int
	| Tvar t1, Tvar t2 when t1 = t2 && (op = Beq || op = Bneq) ->
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
		 |Blt_pointer|Bgt_pointer|Ble_pointer|Bge_pointer
		 |Bneq_pointer|Beq_pointer
		 |Bneq_float|Beq_float|Bge_float|Ble_float|Bgt_float|Blt_float
		 |Bneq_int|Beq_int|Bge_int|Ble_int|Bgt_int|Blt_int
		 |Bsub_pointer|Badd_pointer_int), _) ->
      assert false
  | CEcall (e, el) ->
      let e = type_expr env e in
      let el = List.map (type_expr env) el in
      begin match e.texpr_type.ctype_node with
	| Tfun (tl, ty) ->
	    let rec check_args i el' = function
	      | [], [] -> 
		  TEcall (e, List.rev el'), ty
	      | e :: el, t :: tl when compatible_type e.texpr_type t ->
		  check_args (i+1) (coerce t e :: el') (el, tl)
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
      let n = sizeof e.texpr_loc e.texpr_type in
      TEsizeof (e.texpr_type,n), c_int
  | CEsizeof ty ->
      let ty = type_type loc env ty in
      let n = sizeof loc ty in
      TEsizeof(ty,n), c_int

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
      (* TODO: check that e is not of enum type *)
      ()
  | TEcast (_, e) ->
      check_lvalue loc e
  | _ -> 
      error loc "invalid lvalue"

and type_expr_option env eo = option_app (type_expr env) eo

and type_field n loc env (ty, x, bf) = 
  let ty = type_type loc env ty in
  let bf = type_expr_option env bf in
  let info = find_field n x in
  match bf, ty.ctype_node with
    | _, Tvoid ->
	error loc ("field `"^x^"' declared void")
    | None, _ ->
	(ty, info)
    | Some e, (Tenum _ | Tint _ as tyn) -> 
	let s = match tyn with
	  | Tenum _ -> Unsigned (* TODO: verif assez de bits pour l'enum *)
	  | Tint (s, Int) -> s
	  | Tint (s, _) ->
	      warning loc ("bit-field `"^x^"' type invalid in ANSI C"); s
	  | _ -> assert false
	in
	let v = eval_const_expr e in
	({ty with ctype_node = Tint (s, Bitfield v)}, info)
    | Some _, _ -> 
	error loc ("bit-field `"^x^"' has invalid type")

(*s Typing of integers expressions: to be used when coercion is not allowed
    (array subscript, array size, enum value, etc.) *)

and type_int_expr_option env eo = option_app (type_int_expr env) eo

and type_int_expr env e = match type_expr env e with
  | { texpr_type = { ctype_node = Tint _ | Tenum _ } } as te -> te
  | _ -> error e.loc "invalid operand (expected integer)"

(*s Typing of arithmetic expressions: integers or floats *)

and type_arith_expr env e = match type_expr env e with
  | { texpr_type = { ctype_node = Tint _ | Tenum _ | Tfloat _ } } as te -> 
      te
  | _ -> error e.loc "invalid operand (expected integer or float)"

(*s Typing of ``boolean'' expressions *)

and type_boolean env e = 
  let e' = type_expr env e in
  let ty = e'.texpr_type in
  match ty.ctype_node with
    | Tint _ | Tenum _ | Tfloat _ | Tpointer _ | Tarray _ -> e'
    | _ -> error e.loc "invalid operand (expected arith or pointer)"

let int_to_init loc env ty i=
  (Iexpr 
     (coerce ty 
	(type_expr env 
	   { node = (CEconstant 
		       (IntConstant (sprintf "%d" i)));
	     loc = loc})))


(*s Typing of initializers *)

let rec type_initializer loc env ty = function
  | Iexpr e -> 	      
      begin
	match e.node with
	  | CEstring_literal s ->
	      let ty = 
		match ty.ctype_node with
		  | Tpointer ty | Tarray (ty,_) -> ty
		  | _ ->  ty
	      in
	      let l = ref [int_to_init e.loc env ty 0] in 
	      let n = (String.length s) -1 in
	      for i = 1 to n-1  do
		l := int_to_init e.loc env ty 
		  (Char.code (String.get s (n-i)))::!l
	      done; 
	      Ilist !l
	  | _ -> 
	      let e = type_expr env e in
	      Iexpr (coerce ty e)
      end
  | Ilist el -> 
      (match ty.ctype_node with
	 | Tarray (ty,_) ->   
	     Ilist (List.map (type_initializer loc env ty) el)
	 | Tstruct (n) ->
	     (match tag_type_definition n with
		| TTIncomplete -> 
		    error loc "initializer but incomplete type"
		| TTStructUnion (Tstruct n, fl) -> 
		    Ilist (type_struct_initializer loc env fl el)
		| _ -> 
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
  | v :: fl, e :: el ->
      let e = type_initializer loc env v.var_type e in
      e :: type_struct_initializer loc env fl el
  | [], _ ->
      error loc "excess elements in struct initializer"

and type_initializer_option loc env ty = function
  | None -> None
  | Some i -> Some (type_initializer loc env ty i)

let type_initializer_option loc env ty = function
  | None -> None
  | Some i -> Some (type_initializer loc env ty i)

let array_size_from_initializer loc ty i = match ty.ctype_node, i with
  | Tarray (ety, None), Some (Ilist l) -> 
      let s = of_int (List.length l) in
      { ty with ctype_node = Tarray (ety, Some s) }
  | _ -> 
      ty

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
      (* TODO: vérifier existence label *)
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
      TSswitch (e, s), { st with break = false ; term = true }
  | CScase (e, s) ->
      let e = type_int_expr env e in
      let s,st = type_statement env et s in
      TScase (e, s), st
  | CSdefault (s) ->
      let s,st = type_statement env et s in
      TSdefault (s), st
  | CSannot (Assert p) ->
      let p = type_predicate env p in
      TSassert p, mt_status
  | CSannot (Label l) ->
      TSlogic_label l, mt_status
  | CSannot (GhostSet(x,t)) ->
      TSset (type_ghost_lvalue env x,type_term env t), mt_status
  | CSspec (spec, s) ->
      let spec = type_spec env spec in
      let s,st = type_statement env et s in
      TSspec (spec, s), st

and type_block env et (dl,sl) = 
  let rec type_decls vs env = function
    | [] -> 
	[], env
    | { node = Cdecl (ty, x, i) } as d :: dl ->
	if Sset.mem x vs then error d.loc ("redeclaration of `" ^ x ^ "'");
	let ty = type_type d.loc env ty in	
	if eq_type_node ty.ctype_node Tvoid then 
	  error d.loc ("variable `" ^ x ^ "' declared void");
	let i = type_initializer_option d.loc env ty i in
	let ty = array_size_from_initializer d.loc ty i in
	let info = default_var_info x in
	if ty.ctype_storage = Static then set_static info;
	let env' = Env.add x ty (Var_info info) env in
	let dl',env'' = type_decls (Sset.add x vs) env' dl in
	{ d with node = Tdecl (ty, info, i) } :: dl', env''
    | { node = Ctypedecl ty } as d :: dl ->
	let ty' = type_type d.loc env ty in
	let dl',env' = type_decls vs env dl in
	{ d with node = Ttypedecl ty' } :: dl', env'
    | { loc = l } :: _ ->
	error l "unsupported local declaration"
  in
  let dl',env' = type_decls Sset.empty (Env.new_block env) dl in
  let rec type_bl = function
    | [] -> 
	[], mt_status
    | [s] ->
	let s',st = type_statement env' et s in
	[s'], st
    | s :: bl ->
	let s', st1 = type_statement env' et s in
	let bl', st2 = type_bl bl in
	let st = or_status st1 st2 in
	s' :: bl', { st with term = st2.term }
  in
  let sl', st = type_bl sl in
  (dl', sl'), st

let type_parameters loc env pl =
  let type_one (ty,x) (pl,env) =
    let info = default_var_info x in
    let ty = type_type loc env ty in 
    set_formal_param info;
    let env = Env.add x ty (Var_info info) env in
    Coptions.lprintf 
      "Parameter %s added in env with unique name %s@." x info.var_unique_name;
    (ty,info) :: pl, env 
  in
  let is_void (ty,_) = ty.ctype_node = Tvoid in
  let pl, env = List.fold_right type_one pl ([], env) in
  match pl with
    | [p] when is_void p -> 
	[], env
    | _ -> 
	if List.exists is_void pl then 
	  error loc "`void' in parameter list must be the entire list";
	pl, env
  
let type_logic_parameters env pl = 
  List.fold_right
    (fun (ty,x) (pl,env) ->
       let info = default_var_info x in
       let ty = type_logic_type env ty in 
       (info,ty) :: pl, Env.add x ty (Var_info info) env)
    pl 
    ([], env)

let type_spec_decl loc = function
  | LDaxiom (id, p) -> 
      Taxiom (id, type_predicate (Env.empty ()) p)
  | LDinvariant (id, p) -> 
      Tinvariant (id, type_predicate (Env.empty ()) p)
  | LDlogic (id, ty, pl, ll) ->
      let ty = type_logic_type (Env.empty ()) ty in
      let pl,env' = type_logic_parameters (Env.empty ()) pl in
      id.logic_args <- List.map fst pl;
      let ll = List.map (type_location env') ll in
      Cenv.add_fun id.logic_name (List.map snd pl, ty, id);
      Tlogic (id, Function (pl, ty, ll))
  | LDlogic_def (id, ty, pl, t) ->
      let ty = type_logic_type (Env.empty ()) ty in
      let pl,env' = type_logic_parameters (Env.empty ()) pl in
      id.logic_args <- List.map fst pl;
      let t = type_term env' t in
      Cenv.add_fun id.logic_name (List.map snd pl, ty, id);
      Tlogic (id, Function_def (pl, ty, t))
  | LDpredicate_reads (id, pl, ll) ->
      let pl,env' = type_logic_parameters (Env.empty ()) pl in
      id.logic_args <- List.map fst pl;
      let ll = List.map (type_location env') ll in
      Cenv.add_pred id.logic_name (List.map snd pl,id);
      Tlogic (id, Predicate_reads (pl, ll))
  | LDpredicate_def (id, pl, p) ->
      let pl,env' = type_logic_parameters (Env.empty ()) pl in
      id.logic_args <- List.map fst pl;
      let p = type_predicate env' p in
      Cenv.add_pred id.logic_name (List.map snd pl,id);
      Tlogic (id, Predicate_def (pl, p))
  | LDghost (ty,x,cinit) -> 
      let ty = type_type loc (Env.empty ()) ty in
      let info = add_ghost loc x ty (default_var_info x) in 
      set_static info;
      set_var_type (Var_info info) {ty with Ctypes.ctype_ghost = true};
      let cinit = 
	match cinit with
	  | None -> None
	  | Some (Iexpr t) -> Some(Iexpr (type_term (Env.empty()) t))
	  | _ -> assert false(*TODO*)
      in
      Tghost (info, cinit)
  | LDtype (id, loc) ->
      if Cenv.mem_type id then error loc ("clash with previous type " ^ id);
      Cenv.add_type id;
      Ttype id

(* table storing function specifications *)
let function_specs = Hashtbl.create 97

let empty_spec () = 
  { requires = None; assigns = None; ensures = None; decreases = None } 

let is_empty_spec s = 
  s.requires = None && s.assigns = None && 
  s.ensures = None && s.decreases = None

let function_spec loc f = function
  (* no spec given; we return the current spec if any, or [empty_spec] *)
  | None ->
      (try 
	 Hashtbl.find function_specs f
       with Not_found -> 
	 let s = empty_spec () in Hashtbl.add function_specs f s; s)
  (* a spec is given; we update the current spec only if [empty_spec] *)
  | Some s ->
      (try 
	 let s' = Hashtbl.find function_specs f in
	 if not (is_empty_spec s') then 
	   error loc ("already a specification for " ^ f);
	 s'.requires <- s.requires;
	 s'.assigns <- s.assigns;
	 s'.ensures <- s.ensures;
	 s'.decreases <- s.decreases;
	 s'
       with Not_found -> 
	 Hashtbl.add function_specs f s; s)

let type_decl d = match d.node with
  | Cspecdecl s -> 
      type_spec_decl d.loc s
  | Ctypedef (ty, x) -> 
      let ty = type_type d.loc (Env.empty ()) ty in
      add_typedef d.loc x ty;
      Ttypedef (ty, x)
  | Ctypedecl ty -> 
      let ty = type_type d.loc (Env.empty ()) ty in
      Ttypedecl ty
  | Cdecl (ty, x, i) -> 
      begin match ty.Cast.ctype_node with
	| CTfun(pl,ty_res) ->
	    let pl,env = type_parameters d.loc (Env.empty ()) pl in
	    let ty_res = type_type d.loc (Env.empty ()) ty_res in
	    let info = default_fun_info x in
	    let spl = List.map fst pl in
	    let info = 
	      match add_sym d.loc x (noattr (Tfun (spl, ty_res))) 
		(Fun_info info) with
		| Var_info _ -> assert false
		| Fun_info f -> 
		    if f.args = [] then f.args <- List.map snd pl;
		    f
	    in
	    Tfunspec (function_spec d.loc x None, ty_res, info)
	| _ -> 
	    let ty = type_type d.loc (Env.empty ()) ty in
	    let info = 
	      match add_sym d.loc x ty (Var_info (default_var_info x)) with
		| Var_info v -> v
		| Fun_info _ -> assert false
	    in
	    set_static info;
	    Loc.report_position Coptions.log d.loc;
	    fprintf Coptions.log "Variable %s is assigned@." info.var_name;
	    set_assigned info; (* ????? *)
	    let i = type_initializer_option d.loc (Env.empty ()) ty i in
	    let ty = array_size_from_initializer d.loc ty i in
	    Tdecl (ty, info,i)(* type_initializer_option d.loc (Env.empty ()) ty i*)
      end
  | Cfunspec (s, ty, f, pl) ->
      let ty = type_type d.loc (Env.empty ()) ty in
      let pl,env = type_parameters d.loc (Env.empty ()) pl in
      let s = type_spec ~result:ty env s in
      let s = function_spec d.loc f (Some s) in
      let info = default_fun_info f in
      info.has_assigns <- (s.assigns <> None);
      let spl = List.map fst pl in
      let info = 
	match add_sym d.loc f (noattr (Tfun (spl, ty))) (Fun_info info) with 
	  | Var_info _ -> assert false
	  | Fun_info f -> f.args <- List.map snd pl; f
      in
      Tfunspec (s, ty, info)
  | Cfundef (s, ty, f, pl, bl) -> 
      let ty = type_type d.loc (Env.empty ()) ty in
      let et = if eq_type ty c_void then None else Some ty in
      let pl,env = type_parameters d.loc (Env.empty ()) pl in
      let s = option_app (type_spec ~result:ty env) s in
      let s = function_spec d.loc f s in
      let info = default_fun_info f in
      info.has_assigns <- (s.assigns <> None);
      let spl = List.map fst pl in
      let info = 
	match add_sym d.loc f (noattr (Tfun (spl, ty))) (Fun_info info) with
	  | Var_info v -> assert false
	  | Fun_info f -> f.args <- List.map snd pl; f
      in
      let bl,st = type_statement env et bl in
      if st.term && et <> None then
	warning d.loc "control reaches end of non-void function";
      if st.break then 
	error d.loc "break statement not within a loop or switch";
      if st.continue then 
	error d.loc "continue statement not within a loop";
      Tfundef (s, ty, info, bl)

let type_file = List.map (fun d -> { d with node = type_decl d })

