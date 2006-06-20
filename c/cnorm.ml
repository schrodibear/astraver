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

(*i $Id: cnorm.ml,v 1.63 2006-06-20 09:50:30 filliatr Exp $ i*)

open Creport
open Cconst
open Info
open Cenv
open Cltyping
open Ctypes
open Cast
open Clogic
open Int64


let int_nconstant n = 
  { nterm_node = NTconstant (IntConstant n); 
    nterm_loc = Loc.dummy_position;
    nterm_type = c_int;}

let nzero = int_nconstant "0"

(*
let eval_array_size e = 
  { nterm_node = NTconstant (IntConstant (Int64.to_string (eval_const_expr e))); 
    nterm_loc = e.nexpr_loc;
    nterm_type = c_int }
*)


let noption f o =
  match o with
    | None -> None
    | Some x -> Some (f x)


let var_requires_indirection v =
  v.var_is_referenced && 
  (match v.var_type.Ctypes.ctype_node with
     | Tstruct _ | Tunion _ -> false
     | Tarray (_,ty,_) -> (match ty.Ctypes.ctype_node with 
			     | Tstruct _ | Tunion _ -> false
			     | _ -> true)
     | _ -> true)

let var_is_referenced_or_struct_or_union v =
  v.var_is_referenced || 
  (match v.var_type.Ctypes.ctype_node with
     | Tstruct _ | Tunion _ -> true
     | _ -> false)

open Cast


let noattr2 loc ty e =
  { nexpr_node = e;
    nexpr_type = ty;
    nexpr_loc  = loc
  }

let arrow_vars = Hashtbl.create 97
  
let declare_arrow_var info =
  try  let info' = Hashtbl.find arrow_vars info.var_name in
  if not (same_why_type_no_zone info.var_why_type info'.var_why_type)
  then
    assert false
  else
    info'
  with
      Not_found ->
	begin
	  Hashtbl.add arrow_vars info.var_name info;
	  info
	end

let make_field ty =
  let rec name ty =
    match ty.Ctypes.ctype_node with 
      | Tvoid -> "void"
      | Tint  _ | Tenum _ -> "int"
      | Tfloat _ -> "float"
      | Ctypes.Tvar s -> s
      | Tarray (_, ty ,_) | Tpointer (_,ty) -> (name ty) ^"P" 
      | Tstruct s | Tunion s-> s^"P" (* "P" for "pointer" *)
      | Tfun _ -> "fun"
  in
  let n = (name ty) ^ "M" in (* "M" for "memory" *)
  let info = default_var_info n in
  set_var_type (Info.Var_info info)  ty  false;
  info

let rename_zone assoc ty =
  match ty with
    | Pointer z ->
	let z = repr z in
	begin
	  try
	    Pointer(List.assoc z assoc)
	  with
	      Not_found -> ty
	end
    | _ -> ty

(* table qui a tout couple zone champ associe le type why des elements pointers par p->champ ou p est un pointeur sur zone*)
let type_why_table = Hashtbl.create 97 

let rec type_why e =
  match e.nexpr_node with
    | NEvar e -> 
	begin match e with
	  | Var_info v -> v.var_why_type
	  | Fun_info f -> f.type_why_fun
	end
    | NEarrow (_,z,f) -> 
	begin
	  try
	    let z = repr z in
	    let t = Hashtbl.find type_why_table z  in
	    Hashtbl.find t f
	  with Not_found -> 
	    Format.eprintf "no  why type for %a@\n" Cprint.nexpr e;
	    assert false
	end
    | NEnop -> Unit
    | NEconstant (IntConstant _) -> Info.Int    
    | NEconstant (RealConstant x) -> 
	let _,fk = Ctyping.float_constant_type x in Info.Float fk
    | NEstring_literal _ -> assert false
    | NEseq (e1,e2) -> type_why e2 
    | NEassign (l,e) -> type_why e
    | NEassign_op (l,op,e) -> type_why e
    | NEbinary (e1,Bsub_pointer,e2) | NEbinary (e1,Blt_pointer,e2) 
    | NEbinary (e1,Bgt_pointer,e2) | NEbinary (e1,Ble_pointer,e2)     
    | NEbinary (e1,Bge_pointer,e2) | NEbinary (e1,Beq_pointer,e2)     
    | NEbinary (e1,Bneq_pointer,e2) -> Info.Int
    | NEcast (_,e) | NEunary (_,e) | NEincr (_,e) 
    | NEbinary (e,_,_) | NEcond (_,_,e) -> type_why e
    | NEcall {ncall_fun = e; ncall_zones_assoc = assoc } ->
	rename_zone assoc (type_why e)
    | NEmalloc _ -> Info.Pointer (make_zone true)
	
let find_zone e = 
  match type_why e with
    | Pointer z -> repr z
    | _ -> assert false

let why_type_for_float t =
  if Coptions.floats then match t.Ctypes.ctype_node with
    | Tfloat Float -> "single"
    | Tfloat Double -> "double"
    | Tfloat LongDouble -> "quad"
    | Tfloat Real -> "real"
    | _ -> assert false
  else
    "real"

let rec type_why_for_term t = 
  match t.nterm_node with
    | NTconstant (IntConstant _) -> Info.Int     
    | NTconstant (RealConstant _)
    | NTunop ((Clogic.Usqrt_real | Clogic.Uabs_real 
	      |Clogic.Uround_error | Clogic.Utotal_error
	      |Clogic.Uexact | Clogic.Umodel), _) ->
	Info.Why_Logic "real"
    | NTvar v -> v.var_why_type
    | NTapp {napp_pred = f; napp_zones_assoc = assoc } -> 
	rename_zone assoc f.logic_why_type
    | NTunop (Clogic.Uminus,t) | NTunop (Clogic.Utilde,t) -> 
	type_why_for_term t
    | NTunop (Clogic.Ustar,_) | NTunop (Clogic.Uamp,_) -> assert false
    | NTunop ((Clogic.Ufloat_of_int | Clogic.Ufloat_conversion),_) -> 
	Info.Why_Logic (why_type_for_float t.nterm_type)
    | NTunop (Clogic.Uint_of_float,_) -> Info.Int
    | NTbinop (t1,Clogic.Bsub,t2) -> 
	begin
	  match type_why_for_term t1, type_why_for_term t2 with
	    | Pointer _, Pointer _ -> Info.Int
	    | Pointer _, _ -> assert false
	    | _, Pointer _ -> assert false
	    | ty,_ -> ty
	end
    | NTbinop (t1,_,_) -> type_why_for_term t1
    | NTarrow (_,z,f) ->
	begin
	  let z = repr z in
	  try
	    let t = Hashtbl.find type_why_table z  in
	    Hashtbl.find t f
	  with Not_found -> assert false
	end
    | NTif (_,_,t) -> type_why_for_term t
    | NTold t -> type_why_for_term t
    | NTat (t,_) -> type_why_for_term t
    | NTbase_addr t ->
	begin match type_why_for_term t with
	  | Pointer z -> Addr z
	  | _ -> assert false
	end  
    | NToffset t -> Info.Int
    | NTblock_length t -> Info.Int
    | NTcast (_,t) -> assert false (* type_why_for_term t *)
    | NTrange (t,_,_,_) -> type_why_for_term t
	
let find_zone_for_term e = 
  match type_why_for_term e with
    | Pointer z -> repr z
    | ty -> 
	let l,n = output_why_type ty in
	Format.eprintf "type of term %a : %s@." Cprint.nterm e n; 
	assert false 

let type_why_new_zone zone field_info =
  let t =
    try
      Hashtbl.find type_why_table zone 
    with Not_found ->
      let t = Hashtbl.create 5 in
      Hashtbl.add type_why_table zone t; t
  in
  try
    let _ = Hashtbl.find t field_info in
    ()
  with Not_found ->
    let tw =  
      match field_info.var_why_type with 
	| Pointer z -> 
	    Pointer (make_zone ~name:z.name zone.zone_is_var)
	| tw -> tw
    in
(*    let l,n = output_why_type tw in
    Format.eprintf "adding in type_why_table :(%s,%s) -> %s@." 
      zone.name field_info.var_name n;*)
    Hashtbl.add t field_info tw 

	

let ne_arrow loc valid ty e z f =
  let () = type_why_new_zone z f in 
  NEarrow (    {nexpr_node = e;
		nexpr_type = noattr (Tpointer (valid,ty));
		nexpr_loc = loc},z,f)

	
	  
let rec expr t =
  let ty = t.texpr_type in
  { nexpr_node = expr_node t.texpr_loc ty t.texpr_node;
    nexpr_type = ty ;
    nexpr_loc = t.texpr_loc;
  }

and expr_node loc ty t =
    match t with
      | TEnop -> NEnop
      | TEconstant constant -> NEconstant constant
      | TEstring_literal string -> NEstring_literal string
      | TEvar env_info ->
	  (match env_info with
	    | Var_info v ->
		let t' = NEvar env_info in
		if var_requires_indirection v then(
		   let info = make_field ty in
		   let info = declare_arrow_var info in
		   let zone = 
		     match v.var_why_type with
		       | Pointer z -> z
		       | _ -> assert false 
		   in
		   ne_arrow loc Valid ty t' zone info)
		else t'
	    | Fun_info _  -> NEvar env_info)
      | TEdot (lvalue,var_info) -> 
	  let t' =
	    match lvalue.texpr_node with
	      | TEunary (Ustar ,texpr) -> expr texpr
	      | _ -> expr lvalue
	  in
	  let zone = find_zone t' in
	  let () = type_why_new_zone zone var_info in 
	  let t' = NEarrow (t', zone, var_info) in
	  if var_requires_indirection var_info then
	    let info = make_field ty in
	    let info = declare_arrow_var info in
	    let zone = find_zone (noattr2 loc ty t') in
	    ne_arrow loc Valid ty t' zone info
	  else t'
      | TEarrow (lvalue,var_info) ->
	  let expr = expr lvalue in
	  let zone = find_zone expr in
	  let () = type_why_new_zone zone var_info in
	  let t' = NEarrow (expr, zone, var_info) in
	  if var_requires_indirection var_info then
	    let info = make_field ty in
	    let info = declare_arrow_var info in
	    let zone = find_zone (noattr2 loc ty t') in
	    ne_arrow loc Valid ty t' zone info
	  else t'
      | TEarrget (lvalue,texpr) -> 
	  (* t[e] -> *(t+e) *)
	  let is_valid =
	    match lvalue.texpr_type.Ctypes.ctype_node with
	      | Tarray(Valid,_,Some n) ->
		  begin
		    try
		      let i = Ctyping.eval_const_expr_noerror texpr in
		      if (Int64.zero <= i && i < n) then Valid else Tab n
		    with Invalid_argument _ -> Tab n
		  end
	      | Tarray(Tab n1, _, Some n2) ->  assert (n1=n2);
		  Tab n2
	      | _ -> Not_valid
	  in
	  let info = make_field ty in
	  let info = declare_arrow_var info in
	  let nexpr = expr lvalue in
	  let zone = find_zone nexpr in
	  let ty = { ty with Ctypes.ctype_node = Tpointer (is_valid,ty); 
		       ctype_ghost = lvalue.texpr_type.ctype_ghost } in
	  let () = type_why_new_zone zone info in
	  NEarrow ( 
	    {
	      nexpr_node = NEbinary(nexpr, Badd_pointer_int, expr texpr);
	      nexpr_type = ty ;
	      nexpr_loc = loc;
	    },
	    zone, info)
      | TEseq (texpr1,texpr2) -> NEseq ((expr texpr1) , (expr texpr2))
      | TEassign (lvalue ,texpr) -> 
	  NEassign ((expr lvalue) , (expr texpr))
      | TEassign_op (lvalue ,binary_operator, texpr) ->
	  NEassign_op ((expr lvalue),binary_operator , (expr texpr))
      | TEunary (Ustar ,texpr) ->
	  let info = make_field ty in
	  let info = declare_arrow_var info in
	  let expr = expr texpr in
	  let zone = find_zone expr in
	  let () = type_why_new_zone zone info in
	  NEarrow (expr, zone, info)
      | TEunary (Uamp ,texpr) ->
	  (match texpr.texpr_node with
	     | TEvar v -> NEvar v
	     | TEunary (Ustar, texpr)-> expr_node loc ty texpr.texpr_node
	     | TEdot(lvalue,var_info)->
		  let t' =
		    match lvalue.texpr_node with
		      | TEunary (Ustar ,texpr) -> expr texpr
		      | _ -> expr lvalue
		  in
		  let zone = find_zone t' in
		  let () = type_why_new_zone zone var_info in
		  NEarrow (t', zone, var_info)
	     | TEarrow(lvalue,var_info) ->
		 let t' = expr lvalue in
		 let zone = find_zone t' in 
		 let () = type_why_new_zone zone var_info in
		 NEarrow (t', zone, var_info)
	     | TEarrget (lvalue,t) ->
		 NEbinary(expr lvalue, Badd_pointer_int, expr t)
	     | _ -> 
		 warning loc "this & cannot be normalized";
		 NEunary (Uamp,expr texpr))
      | TEunary (unary_operator ,texpr) ->
	  NEunary(unary_operator, expr texpr)
      | TEincr (incr_operator,texpr) -> NEincr(incr_operator, expr texpr)
      | TEbinary (texpr1 , binary_operator , texpr2) ->
	  NEbinary ((expr texpr1), binary_operator , (expr texpr2))
      | TEcall (texpr ,list) -> 
	  NEcall { ncall_fun = expr texpr ;
		   ncall_args = List.map expr list;
		   ncall_zones_assoc = [] }
      | TEcond (texpr1, texpr2, texpr3) -> NEcond ((expr texpr1),
						   (expr texpr2),
						   (expr texpr3))
      | TEsizeof (tctype,n) ->
	  NEconstant (IntConstant (Int64.to_string n))
      | TEcast({Ctypes.ctype_node = Tpointer _}as ty, 
	       {texpr_node = TEconstant (IntConstant "0")}) ->
	  let info = default_var_info "null" in 
	  Cenv.set_var_type (Var_info info) ty false;
	  NEvar (Var_info info)    
      | TEcast (tctype ,texpr) -> 
	  NEcast (tctype, expr texpr)
      | TEmalloc (tctype, texpr) ->
	  NEmalloc (tctype, expr texpr)

let nt_arrow loc valid ty e z f =
  let () = type_why_new_zone z f in
  NTarrow ({nterm_node = e;
	    nterm_type = ty;
	    nterm_loc = loc},z,f)
      

let rec term_node loc t ty =
  match t with
  | Tconstant constant -> NTconstant constant
  | Tvar var_info -> 
      let t' = NTvar var_info in
      if var_requires_indirection var_info then
	let info = make_field ty in
	let info = declare_arrow_var info in
	let zone = 
	  match var_info.var_why_type with
	    | Pointer z -> z
	    | _ -> assert false 
	in
	nt_arrow loc true var_info.var_type t' zone info
      else
	t'
  | Tapp (logic_info ,l) -> NTapp  {napp_pred = logic_info; 
				    napp_args = List.map term l;
				    napp_zones_assoc = []}
  | Tunop (Clogic.Uamp,t) -> 
      begin match t.term_node with
	| Tvar v-> NTvar v
	| Tunop(Clogic.Ustar, t) -> term_node loc t.term_node ty
	| Tarrow(t,f) -> 
	    let t = term t in
	    let zone = find_zone_for_term t in
	    let () = type_why_new_zone zone f in
	    NTarrow (t, zone,  f) 
	| Tdot(t,f) ->  
	    let t =
	      match t.term_node with
		| Tunop (Clogic.Ustar ,t) -> term t
		| _ -> term t
	    in
	    let zone = find_zone_for_term t in
	    let () = type_why_new_zone zone f in
	    NTarrow (t, zone, f)
	| _ -> 
	    unsupported loc "cannot handle this & operator"
	    (* NTunop(Clogic.Uamp,term t)    *)
      end
  | Tunop (Clogic.Ustar,t) ->  
      let info = make_field ty in
      let info = declare_arrow_var info in
      let t = term t in
      let zone = find_zone_for_term t in
      let () = type_why_new_zone zone info in
      NTarrow (t, zone, info)
  | Tunop (unop,t) -> NTunop(unop,term t)
  | Tbinop (t1, binop, t2) -> NTbinop (term t1, binop, term t2)
  | Tdot (t', var_info) ->
      let t' =
	match t'.term_node with
	  | Tunop (Clogic.Ustar ,t') -> term t'
	  | _ -> term t'
      in
      let zone = find_zone_for_term t' in
      let () = type_why_new_zone zone var_info in
      let t' = NTarrow (t', zone, var_info) in
      if var_requires_indirection var_info then
	let info = make_field ty in
	let info = declare_arrow_var info in
	let zone = find_zone_for_term {nterm_node = t';
				       nterm_loc = loc;
				       nterm_type =  var_info.var_type}  
	in
	nt_arrow loc true var_info.var_type t' zone info
      else
	t'
  | Tarrow (t', var_info) ->
	  let t' = term t' in
	  let zone = find_zone_for_term t' in
	  let () = type_why_new_zone zone var_info in
	  let t' = NTarrow (t', zone, var_info) in
	  if var_requires_indirection var_info then
	    let info = make_field ty in
	    let info = declare_arrow_var info in
	    let zone = find_zone_for_term {nterm_type = ty;
					   nterm_loc = loc;
					   nterm_node= t'}
	    in
	    nt_arrow loc true ty t' zone info
	  else t'
  | Tarrget (t1, t2) ->
	  let info = make_field ty in
	  let info = declare_arrow_var info in
	  let t1' = term t1 in
	  let zone = find_zone_for_term t1' in
	  let ty = { ty with Ctypes.ctype_node = Tpointer (Valid,ty); 
		       ctype_ghost = t1.term_type.ctype_ghost } in
	  let () = type_why_new_zone zone info in
	  NTarrow ( 
	    {
	      nterm_node = NTbinop(t1', Clogic.Badd, term t2);
	      nterm_type = ty ;
	      nterm_loc = loc;
	    },
	    zone, info)
  | Tif (t1, t2, t3) -> NTif (term t1, term t2 , term t3)
  | Told t1 -> NTold (term t1)
  | Tat (t1, s) -> NTat (term t1, s)
  | Tbase_addr t -> NTbase_addr (term t)
  | Toffset t -> NToffset (term t)
  | Tblock_length t -> NTblock_length (term t)
  | Tcast ({Ctypes.ctype_node = Tpointer _}as ty, 
	    {term_node = Tconstant (IntConstant "0")}) ->      
      let info = default_var_info "null" in 
      Cenv.set_var_type (Var_info info) ty false;
      NTvar info
  | Tcast (ty, t) -> NTcast (ty, term t)
  | Trange (t1, t2, t3) -> 
      let t1 = term t1 in
      let info = make_field ty in
      let info = declare_arrow_var info in
      let zone = find_zone_for_term t1 in 
      let () = type_why_new_zone zone info in
      NTrange (t1, term_option t2, term_option t3, info)

and term t = 
{ 
  nterm_node = term_node t.term_loc t.term_node t.term_type;
  nterm_loc = t.term_loc;
  nterm_type = t.term_type
}

and term_option = function None -> None | Some t -> Some (term t)

let nlocation = term
(***
let nlocation l =
  match l with
    | Lterm(t) -> Lterm(term t)
    | Lstar(t) -> Lstar(term t)
    | Lrange(t1,t2,t3) -> Lrange(term t1,term t2,term t3)
***)
	
let nvariant v =
  match v with (t, sopt) -> (term t,sopt)

	
let rec predicate p =
  { npred_node = predicate_node p.pred_node;
    npred_loc = p.pred_loc }

and predicate_node = function
    | Pfalse -> NPfalse
    | Ptrue -> NPtrue 
    | Papp (info,l) -> NPapp {napp_pred = info; napp_args = List.map term l;
			      napp_zones_assoc = []}
    | Prel (t1 , relation , t2) -> NPrel (term t1,relation,term t2)
    | Pand (p1, p2) -> NPand (predicate p1, predicate p2)
    | Por (p1, p2) -> NPor (predicate p1, predicate p2)
    | Pimplies (p1, p2) -> NPimplies (predicate p1, predicate p2)
    | Piff (p1, p2) -> NPiff (predicate p1, predicate p2)
    | Pnot p1 -> NPnot (predicate p1)
    | Pif (t,p1,p2) -> NPif (term t,predicate p1 ,predicate p2)
    | Pforall (typed_quantifiers, p) -> NPforall (
	(List.map (fun (x,y) -> (x,y)) typed_quantifiers),
	(predicate p))
    | Pexists (typed_quantifiers, p) -> NPexists (
	(List.map (fun (x,y) -> (x,y)) typed_quantifiers),
	(predicate p)) 
    | Pold p -> NPold (predicate p)
    | Pat (p, s) -> NPat ((predicate p),s)
    | Pseparated (t1,t2) ->
(*
	let loc = t1.term_loc in
	let t1 =
	  match t1.term_node with
	    | Tvar t -> 	  
		set_var_type (Var_info t) (c_array_size t.var_type Int64.one);
		t
	    | _ -> assert false 
	in
	let t2 =
	  match t2.term_node with
	    | Tvar t -> 	  
		set_var_type (Var_info t) (c_array_size t.var_type Int64.one);
		t 
	    | _ -> assert false
	in
	(separation loc t1 t2).npred_node
*)
	assert false (* TODO *)
    | Pfullseparated (t1,t2) ->
(*
	let loc = t1.term_loc in
	let t1 =
	  match t1.term_node with
	    | Tvar t -> 	  
		set_var_type (Var_info t) (c_array_size t.var_type Int64.one);
		t
	    | _ -> assert false 
	in
	let t2 =
	  match t2.term_node with
	    | Tvar t -> 	  
		set_var_type (Var_info t) (c_array_size t.var_type Int64.one);
		t 
	    | _ -> assert false
	in
	(fullseparation loc t1 t2).npred_node
	*)
	assert false (* TODO *)
    | Pvalid (t) -> NPvalid (term t) 
    | Pvalid_index (t1 , t2) -> NPvalid_index (term t1 , term t2) 
    | Pvalid_range (t1,t2,t3) -> NPvalid_range (term t1, term t2 , term t3)
    | Pfresh t -> NPfresh (term t)  
    | Pnamed (n, p) -> NPnamed (n, predicate p)

let loop_annot a =
  {
    invariant = noption predicate a.invariant;
    loop_assigns = 
     noption (List.map nlocation) a.loop_assigns;
    variant = noption nvariant a.variant;
  }

let logic_symbol l =
  match l with
    | Predicate_reads(param_list,loc_list) ->
	NPredicate_reads(List.map (fun (v,t) -> (v,t)) param_list,
			List.map nlocation loc_list)
    | Predicate_def  (param_list , p ) ->
	NPredicate_def(List.map (fun (v,t) -> (v,t)) param_list,
		      predicate p)
    | Function (l1 , c , l2) -> NFunction (
	List.map (fun (var,c) -> (var,c)) l1,
	c,
	List.map nlocation l2)
    | Function_def (param_list, t, e) ->
	NFunction_def (param_list, t, term e)

let rec c_initializer c = match c with
  | Iexpr e ->  Iexpr (expr e)
  | Ilist l -> Ilist (List.map (fun x -> (c_initializer x))l)

let c_initializer_option = function
  | None -> None
  | Some i -> Some (c_initializer i)

let ilist = function
  | None -> None
  | Some i -> Some (Ilist [i])

let variant v = let (x,y) = v in ((term x), y)


let make_and p1 p2 = match p1.npred_node, p2.npred_node with
  | NPtrue, _ -> p2
  | _, NPtrue -> p1
  | _ -> { p1 with npred_node = NPand (p1, p2) }


let make_implies p1 p2 = match p2.npred_node with
  | NPtrue -> { p1 with npred_node = NPtrue }
  | _ -> { p1 with npred_node = NPimplies (p1, p2) }

let make_forall q p = match p.npred_node with
  | NPtrue -> { p with npred_node = NPtrue }
  | _ -> { p with npred_node = NPforall (q, p) }


let dummy_pred p = { npred_node = p; npred_loc = Loc.dummy_position }
let nprel (t1, r, t2) = dummy_pred (NPrel (t1, r, t2))
let npand (p1, p2) = make_and p1 p2
let npvalid t = dummy_pred (NPvalid t)
let npvalid_range (t,i,j) = dummy_pred (NPvalid_range (t,i,j))
let npfresh t = dummy_pred (NPfresh t)
let nptrue = dummy_pred NPtrue
let npapp (f, l) = dummy_pred (NPapp {napp_pred = f;napp_args =  l; 
				      napp_zones_assoc = []})

let spec ?(add=nptrue) s = 
  let pred = match s.requires with 
    | None -> add
    | Some pred -> npand (add,(predicate pred))
  in
  let pred = if pred = nptrue then None else Some pred in
  { 
    requires = pred;
    assigns  = noption (List.map (fun x -> nlocation x)) s.assigns;
    ensures = noption predicate s.ensures;
    decreases = noption variant s.decreases;
  }


let noattr loc ty e =
  { texpr_node = e;
    texpr_type = ty;
    texpr_loc  = loc
  }

let in_struct2 v1 v = 
  let x = begin
    match v1.texpr_node with
    | TEunary (Ustar, x)-> TEarrow (x, v)
    | TEarrget (x,i) -> 
	TEarrow 
	  ((noattr v1.texpr_loc v1.texpr_type 
	     (TEbinary(x, Badd_pointer_int, i))),v)
    | _ -> TEarrow (v1, v)
  end in
  { texpr_node = x; 
    texpr_loc = v1.texpr_loc;
    texpr_type = v.var_type }





let noattr3 tyn = { Ctypes.ctype_node = tyn; 
		   Ctypes.ctype_storage = No_storage;
		   Ctypes.ctype_const = false;
		   Ctypes.ctype_volatile = false;
		  Ctypes.ctype_ghost = false}

let alloca loc n =
  {nexpr_node = NEcall 
      {ncall_fun = 
	  (noattr2  loc 
	     (noattr3(
		Tfun ([noattr3
			 (Tint(Signed,Ctypes.Int))], 
		      noattr3 (Tpointer (Valid,noattr3 Tvoid))))) 
	     (NEvar  (Fun_info (default_fun_info "alloca"))));
       ncall_args = [{ nexpr_node = NEconstant  (IntConstant n);
		       nexpr_type =  noattr3 (Tint (Signed,Ctypes.Int));
		       nexpr_loc  = loc }];
       ncall_zones_assoc = []};
   nexpr_type = noattr3 (Tpointer (Valid,noattr3 Tvoid));
   nexpr_loc  = loc
  }	  

let copyattr s s' = 
  { nst_node = s';
    nst_break = s.st_break;
    nst_continue = s.st_continue;
    nst_return = s.st_return;
    nst_term = s.st_term;
    nst_loc = s.st_loc;
  }

let rec pop_initializer loc t i =
  match i with 
    | [] ->None,[]
    | (Iexpr e)::l -> Some e,l
    | (Ilist [])::l -> pop_initializer loc t l
    | (Ilist l)::l' -> 
	let e,r = pop_initializer loc t l in e,r@l'

let rec init_expr loc t lvalue initializers =
  match t.Ctypes.ctype_node with
    | Tint _ | Tfloat _ | Tpointer _ | Tenum _ -> 
	let x,l = pop_initializer loc t initializers in
	(match x with 
	  | Some x ->
	      [{nst_node = 
		   NSexpr (noattr2 loc t (NEassign(expr lvalue, expr x)));
		nst_break = false;    
		nst_continue = false; 
		nst_return = false;   
		nst_term = true;
		nst_loc = loc     
	       }]
	  | None -> []), l
    | Tstruct n ->
	begin match tag_type_definition n with
	  | TTStructUnion (Tstruct (_), fl) ->
	      let l1,l2 = List.fold_left 
		(fun (acc,init) f -> 
		   let block, init' =
		     init_expr loc f.var_type 
		       (in_struct2 lvalue f) init
		   in (acc@block,init'))
		([],initializers)  fl
	      in
	      l1,l2
	  | _ ->
	      assert false
	end
    | Tunion n ->
	begin match tag_type_definition n with
	  | TTStructUnion (Tstruct (_), f::_) ->
	      let block, init' =
		init_expr loc f.var_type 
		  (noattr loc f.var_type (TEarrow(lvalue, f)))
		  initializers
	      in 
	      block,init'
	  | _ ->
	      assert false
	end
    | Tarray (_,ty, Some t) ->
	let rec init_cells i (block,init) =
	  if i >= t then (block,init)
	  else
	    let ts = Ctyping.int_teconstant (Int64.to_string i) in
	    let (b,init') = 
	      init_expr loc ty (noattr loc ty (TEarrget(lvalue,ts))) init 
	    in
	    init_cells (Int64.add i Int64.one) (block@b,init')
	in
	init_cells Int64.zero ([],initializers)
    | Tarray (_,ty,None) -> assert false
    | Tfun (_, _) -> assert false
    | Ctypes.Tvar _ -> assert false
    | Tvoid -> assert false

let rec expr_of_term (t : nterm) : nexpr = 
 {
  nexpr_node = 
    begin
      match t.nterm_node with 
	| NTconstant c ->  NEconstant c
	| NTvar v -> NEvar (Var_info v)
	| NTapp _ -> error t.nterm_loc 
	      "logic function can't be used with ghost variables"
	| NTunop (t , term) -> NEunary(
	    begin  match t with 
	      | Clogic.Uminus -> Uminus 
	      | Clogic.Utilde -> Utilde 
	      | Clogic.Ustar -> assert false
	      | Clogic.Uamp -> assert false
	      | Clogic.Ufloat_of_int -> Ufloat_of_int
	      | Clogic.Uint_of_float -> Uint_of_float
	      | Clogic.Ufloat_conversion -> Ufloat_conversion
	      | Clogic.Usqrt_real
	      | Clogic.Uabs_real
	      | Clogic.Uround_error
	      | Clogic.Utotal_error
	      | Clogic.Uexact
	      | Clogic.Umodel -> assert false
	    end,
	    (expr_of_term term))
	      
(*	| NTstar t ->  NEstar (expr_of_term t)*)
	| NTbinop (t1, b, t2) -> 
	    let t1 = (expr_of_term t1) in
	    let t2 = (expr_of_term t2) in
	    NEbinary 
	      (t1,
	       begin match b,t1.nexpr_type.Ctypes.ctype_node,
	       t2.nexpr_type.Ctypes.ctype_node with
		 | Clogic.Badd,Tint _ , Tint _ -> Badd_int
		 | Clogic.Badd,Tfloat fk , Tfloat _ -> Badd_float fk
		 | Clogic.Badd,Tpointer _ , Tint _ -> Badd_pointer_int
		 | Clogic.Bsub,Tint _ , Tint _ -> Bsub_int
		 | Clogic.Bsub,Tfloat fk , Tfloat _ -> Bsub_float fk
		 | Clogic.Bsub,Tpointer _ , Tint _ -> Bsub_pointer
		 | Clogic.Bmul,Tfloat fk , Tfloat _ -> Bmul_float fk
		 | Clogic.Bmul,Tint _ , Tint _ -> Bmul_int
		 | Clogic.Bdiv,Tfloat fk , Tfloat _ -> Bdiv_float fk
		 | Clogic.Bdiv,Tint _ , Tint _ -> Bdiv_int
		 | Clogic.Bmod,Tint _ ,Tint _ -> Bmod_int
		 | Clogic.Badd,Tarray _ , Tint _ -> Badd_pointer_int
		 | Clogic.Bsub,Tarray _ , Tint _ -> Bsub_pointer   
		 | _ -> error  t.nterm_loc 
		     "this operation can't be used with ghost variables"
	       end,
	       t2)
	| NTarrow (t,z,v) -> NEarrow (expr_of_term t,z,v)
	| NTif (t1,t2,t3)-> NEcond 
	      (expr_of_term t1,expr_of_term t2,expr_of_term t3)
	| NTold t -> error t.nterm_loc 
	      "old can't be used here"
	| NTat (t , s)-> error t.nterm_loc 
	      "@ can't be used here"
	| NTbase_addr t -> error t.nterm_loc 
	      "base_addr can't be used here"
	| NToffset t -> error t.nterm_loc 
	      "offset can't be used here"
	| NTblock_length t -> error t.nterm_loc 
	      "block_length can't be used here"
	| NTcast (ty,t) -> NEcast(ty,expr_of_term t)
	| NTrange _ -> 
	    error t.nterm_loc "range cannot by used here"
    end;
    nexpr_type = t.nterm_type;
    nexpr_loc  = t.nterm_loc
 }

let rec st_cases used_cases (i : tstatement) 
  : 'a IntMap.t * 'a IntMap.t * nstatement =
  match i.st_node with 
    | TScase ( e ,i') ->
	let n =  Ctyping.eval_const_expr e in
	let e = expr e in
	if IntMap.mem n used_cases 
	then
	  error i.st_loc ("duplicate case")
	else
	  let (used_cases' , l,i) = st_cases (IntMap.add n e used_cases) i' in
	  (used_cases', (IntMap.add n e l),i)
    | _ -> (used_cases , IntMap.empty , statement i)

and st_instr (l : tstatement list) : tstatement list * nstatement list =
  match l with
    | [] -> l,[]
    | i ::l' -> 
	match i .st_node with
	  | TSdefault _ -> l,[]
	  | TScase(_,_) -> l,[]
	  | _ -> let (l,instr) = st_instr l' in
	    (l,(statement i)::instr)

      
    

and st_case_list (used_cases : 'a IntMap.t) (l : tstatement list) :
  'a IntMap.t * ('a IntMap.t * nstatement list) list =
  match l with 
    | [] -> (used_cases, [] )
    | i::l ->
	match i.st_node with 
	  | TSdefault s ->
	      begin
		match s.st_node with
		  | TScase _ -> unsupported s.st_loc "case following default"
		  | _ ->		 
		      let (l,instr) = st_instr l in
		      let(used_cases'', l'') = (st_case_list used_cases l) in
		      (used_cases'',(IntMap.empty,(statement s)::instr)::l'')
	      end
	  | TScase(e,i) -> 
	      let n = Ctyping.eval_const_expr e in 
	      let e = expr e in
	      if IntMap.mem n used_cases 
	      then
		error i.st_loc ("duplicate case")
	      else
		let (used_cases', l', i') = st_cases (used_cases) i in 
		let (l,instr) = st_instr l in
		let (used_cases'', l'') = 
		  st_case_list (IntMap.add n e used_cases') l in
		(used_cases'',((IntMap.add n e l'),i'::instr)::l'')
	  | _ ->  
	      let (used_cases', l') = st_case_list used_cases l in
	      match l' with
		| [] -> 
		    error i.st_loc 
		      ("unreachable statement at beginning of switch")
		| (lc,i')::l -> (used_cases',(lc,i'@[statement i])::l)
		



and st_switch i =
  match i.st_node with 
    | TSblock (_,l) -> st_case_list IntMap.empty l
    | _ -> st_case_list IntMap.empty [i]

and statement s =
  let nst =
    match s.st_node with
  | TSnop -> NSnop
  | TSexpr texpr -> NSexpr (expr texpr)
  | TSif (texpr, tstatement1, tstatement2) -> NSif ((expr texpr),
						  (statement tstatement1),
						  (statement tstatement2))
  | TSwhile (loop, texpr, tstatement) -> NSwhile (loop_annot loop,
						  (expr texpr),
						  (statement tstatement))
  | TSdowhile (loop, tstatement, texpr) -> 
      NSdowhile (loop_annot loop,statement tstatement, expr texpr) 
  | TSfor (loop ,texpr1, texpr2, texpr3, tstatement) ->
      NSfor (loop_annot loop,
	     (expr texpr1),
	     (expr texpr2),
	     (expr texpr3),
	      (statement tstatement))
  | TSblock (l1,l2) -> 
      local_decl s l1 l2
  | TSreturn option -> NSreturn (noption expr option)
  | TSbreak -> NSbreak
  | TScontinue -> NScontinue
  | TSlabel (string, tstatement) -> NSlabel (string, (statement tstatement)) 
  | TSswitch (texpr, tstatement) -> 
      let (used_cases,s) = st_switch tstatement in
      NSswitch(expr texpr, used_cases, s) 
  | TScase (texpr, tstatement) -> assert false
  | TSdefault tstatement -> assert false
  | TSgoto  string -> assert false (*error "not supported"*)
  | TSassert p -> NSassert (predicate p)
  | TSlogic_label  string -> NSlogic_label string
  | TSspec (s, tstatement) -> NSspec (spec s, statement tstatement)
  | TSset (x, t) -> 
      NSexpr (noattr2 s.st_loc x.term_type 
		(NEassign 
		   (expr_of_term (term x),expr_of_term (term t))))
  in
  { nst_node = nst;
    nst_break = s.st_break;
    nst_continue = s.st_continue;
    nst_return =  s.st_return;
    nst_term = s.st_term;
    nst_loc = s.st_loc;
  }

and local_decl s l l2 = 
  match l with 
    | [] -> NSblock (List.map statement l2)
    | {node = Tdecl (t,v,init); loc = l}::decl -> 
	if var_is_referenced_or_struct_or_union v then
	  set_var_type (Var_info v) (c_array_size Valid v.var_type Int64.one) true;
	begin match init with
	  | None ->
	      let declar = local_decl s decl l2 in
	      NSdecl(v.var_type,v,None,copyattr s declar)
	  | Some c ->
	      match v.var_type.Ctypes.ctype_node with
		| Tenum _ | Tint _ | Tfloat _ | Tpointer _ -> 
		    let declar = local_decl s decl l2 in
		    begin match c with
		      | Iexpr e ->
			  NSdecl(v.var_type, v, Some (Iexpr (expr e)),
				 copyattr s declar)
		      | _ -> assert false
		    end
		| Tarray (_,_, Some length) -> 
		    let lvalue = noattr l v.var_type (TEvar (Var_info v)) in
		    let declar,_ = 
		      without_dereference v
			(init_expr l v.var_type lvalue) [c] 
		    in
		    NSdecl(v.var_type,v,
			   None,
			   let rest = copyattr s (local_decl s decl l2) in
			   copyattr s (NSblock (declar @ [rest])))
		| Tarray _ | Tstruct _ | Tunion _ -> 
		    let lvalue = (noattr l v.var_type (TEvar (Var_info v))) in
		    let declar,_ = init_expr l v.var_type lvalue [c] in
		    NSdecl(v.var_type,v,
			   Some (Iexpr (alloca l "1")),
			   let rest = copyattr s (local_decl s decl l2) in
			   copyattr s (NSblock (declar @ [rest])))
		| Tvoid | Ctypes.Tvar _ | Tfun _ -> assert false		      
	end
    | _  -> assert false


let global_decl e1 =
  match e1 with    
  | Tlogic(info, l) -> Nlogic (info , logic_symbol l)
  | Taxiom (s, p) -> Naxiom (s, predicate p)
  | Tinvariant(s, p) -> Ninvariant (s, predicate p)
  | Ttypedef (t, s) -> Ntypedef(t,s)
  | Ttypedecl t -> Ntypedecl (t)
  | Tdecl (t, v, c) -> 
      let t =
	if  (* not *) v.var_is_assigned && Coptions.closed_program then   
	  { t with Ctypes.ctype_const = true }
	else t 
      in
      set_var_type (Var_info v) t false;
      if var_is_referenced_or_struct_or_union v
      then
	begin
	  set_var_type (Var_info v) (c_array_size Valid v.var_type Int64.one) false;
	  Ndecl(v.var_type,v,ilist (c_initializer_option c))
	end
      else Ndecl(t,v,c_initializer_option c)
  | Tfunspec (s, t, f) -> 
      if not f.has_body then
	begin
	  set_var_type (Fun_info f) (f.fun_type) true;
	  List.iter (fun arg -> 
		       set_var_type (Var_info arg) (arg.var_type) true) f.args
	end;
      Nfunspec (spec s,t,f)

  | Tfundef (s, t, f, st) ->
      let validity_for_struct = 
	List.fold_left 
	  (fun acc y ->
	     let x = y.var_type in
	     match x.Ctypes.ctype_node with
	       | Tstruct _ | Tunion _ -> 
		   npand (npvalid 
			    {nterm_node = NTvar y;
			     nterm_type = x;
			     nterm_loc = Loc.dummy_position},acc)
	       | _ -> acc) 
	  nptrue f.args in
      set_var_type (Fun_info f) (f.fun_type) true;
      List.iter (fun arg -> 
		   set_var_type (Var_info arg) (arg.var_type) true) f.args;
      Nfundef (spec ~add:validity_for_struct s,t,f,statement st)
  | Tghost(x,cinit) ->
      let cinit = 
	match cinit with
	  | None -> None
	  | Some (Iexpr t) -> Some(Iexpr (expr_of_term (term t)))
	  | _ -> assert false
      in
      Info.set_assigned x;
      Ndecl(x.var_type,x,cinit)
  | Ttype s ->
      Ntype s
      
      
	
let file = List.map (fun d -> { node = global_decl d.node ; loc = d.loc})




