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

open Creport
open Cast
open Info
open Clogic
open Cnorm
open Cenv



(* Automatic invariants expressing validity of local/global variables *)

open Clogic
open Ctypes

let tpred t = match t.nterm_node with
  | NTconstant (IntConstant c) -> 
      let c = string_of_int (int_of_string c - 1) in
      { t with nterm_node = NTconstant (IntConstant c) }
  | _ ->
      { t with nterm_node = NTbinop (t, Bsub, int_nconstant "1") }

let make_valid_range_from_0 t ts=
  if ts = Int64.one
  then
    npvalid t
  else
    npvalid_range (t, nzero, int_nconstant (Int64.to_string (Int64.pred ts)))


let fresh_index = 
  let r = ref (-1) in fun () -> incr r; "index_" ^ string_of_int !r


let indirection loc ty t =
  let info = make_field ty in
  let info = declare_arrow_var info in
  let zone = find_zone_for_term t in
  { nterm_node =   NTarrow (t, info.var_why_type, zone, info);
    nterm_loc = loc; 	   
    nterm_type = ty;}
    
(*
  [make_forall_range loc t b f] builds the formula

   forall i, 0 <= i < b -> (f t i)

  unless b is 1, in which case it produces (f t 0)

*)
let make_forall_range loc t b f =
  if b = Int64.one
  then f t nzero
  else
    let i = default_var_info (fresh_index ()) in
    let vari = { nterm_node = NTvar i; 
		 nterm_loc = loc;
		 nterm_type = c_int;} in
    let ti = 
      { nterm_node = NTbinop (t, Badd, vari); 
	nterm_loc = loc;
	nterm_type = t.nterm_type}
    in
    let ineq = npand (nprel (nzero, Le, vari),
		      nprel (vari, Lt, int_nconstant (Int64.to_string b))) in
    make_forall [c_int, i] (make_implies ineq (f ti vari))

let valid_for_type ?(fresh=false) loc name (t : Cast.nterm) =
  let rec valid_fields valid_for_current n (t : Cast.nterm) = 
    begin match tag_type_definition n with
      | TTStructUnion (Tstruct (_), fl) ->
	  List.fold_right 
	    (fun f acc -> 
	       let zone = find_zone_for_term t in
	       let tf = 
		 { nterm_node = NTarrow (t, f.var_why_type, zone, f); 
		   nterm_loc = loc;
		   nterm_type = f.var_type} 
	       in
	       make_and acc (valid_for tf))
	    fl 
	    (if valid_for_current then 
	       if fresh then npand(npvalid t, npfresh t) else npvalid t 
	     else nptrue)
      | TTIncomplete ->
	  error loc ("`" ^ name ^ "' has incomplete type")
      | _ ->
	  assert false
    end
  and valid_for (t : Cast.nterm) = match t.nterm_type.Ctypes.ctype_node with
    | Tstruct (n) ->
 	valid_fields true n t
    | Tarray (_,ty, None) ->
	error loc ("array size missing in `" ^ name ^ "'")
    | Tarray (valid,ty, Some s) ->
	assert valid;
	let ts = Int64.to_string s in
	let vrange = make_valid_range_from_0 t s in
	let valid_form =
	  make_and
	    vrange
	    (if fresh then npfresh t else nptrue)
	in		   
	begin match ty.Ctypes.ctype_node with
	  | Tstruct n ->	      
	      let vti t i = valid_fields false n t in
	      make_and valid_form (make_forall_range loc t s vti)
	  | _ ->
	      make_and valid_form
		(make_forall_range loc t s 
		   (fun t i -> valid_for 
			(indirection loc ty t)))
	end
    | _ -> 
	nptrue
  in
  valid_for t

let not_alias loc x y = 
  if Info.same_why_type (type_why_for_term x) (type_why_for_term y)
  then
    let ba t = { nterm_node = NTbase_addr t; 
		 nterm_loc = loc;
		 nterm_type = c_addr} in 
    nprel (ba x, Neq, ba y)
  else
    {npred_node = NPtrue;  npred_loc = loc}

let var_to_term loc v =
  {
    nterm_node = NTvar v; 
    nterm_loc = loc;
    nterm_type = v.var_type}

let in_struct v1 v = 
  (*  match v1.nterm_node with
    | NTarrow(x,ty,_,_) ->
    | _ -> *)
  let zone = find_zone_for_term v1 in
  { nterm_node = NTarrow (v1,v.var_why_type, zone, v); 
    nterm_loc = v1.nterm_loc;
    nterm_type = v.var_type}

	
let compatible_type ty1 ty2 = 
  match ty1.Ctypes.ctype_node,ty2.Ctypes.ctype_node with
    | Tfun _ , _  | Tenum _, _ | Tpointer _ , _ 
    | Ctypes.Tvar _ , _ | Tvoid, _ | Tint _, _ | Tfloat _, _ -> false
    | _, Tfun _ | _, Tenum _| _, Tpointer _  
    | _, Ctypes.Tvar _ | _, Tvoid | _, Tint _ | _, Tfloat _ -> false
    | _, _ -> true 

let full_compatible_type ty1 ty2 = 
  match ty1.Ctypes.ctype_node,ty2.Ctypes.ctype_node with
    | Tfun _ , _  | Tenum _, _  
    | Ctypes.Tvar _ , _ | Tvoid, _ | Tint _, _ | Tfloat _, _ -> false
    | _, Tfun _ | _, Tenum _  
    | _, Ctypes.Tvar _ | _, Tvoid | _, Tint _ | _, Tfloat _ -> false
    | _, _ -> true

(* assumes v2 is an array of objects of type ty *)
let rec tab_struct mark loc v1 v2 s ty n n1 n2=
  let l = begin
    match  tag_type_definition n with
      | TTStructUnion ((Tstruct _),fl) ->
	  fl
      | _ -> assert false
  end in
  if mark then
    List.fold_left 
      (fun p t -> 
	 if  compatible_type t.var_type v2.nterm_type 
	 then make_and p (not_alias loc v2 (in_struct v1 t))
	 else p)
      nptrue l
  else
  make_and (List.fold_left 
	      (fun p t -> 
		 if  compatible_type t.var_type v2.nterm_type 
		 then make_and p (not_alias loc v2 (in_struct v1 t))
		 else p)
	      nptrue l)
    (make_forall_range loc v2 s 
       (fun t i -> 
	  local_separation mark loc n1 v1 (n2^"[i]") (indirection loc ty t)))

and local_separation  mark loc n1 v1 n2 v2 =
  match (v1.nterm_type.Ctypes.ctype_node,v2.nterm_type.Ctypes.ctype_node) 
  with
    | Tarray (_,ty, None), _ ->
	error loc ("array size missing in `" ^ n1 ^ "'")
    | _, Tarray (_,ty, None) ->
	error loc ("array size missing in `" ^ n2 ^ "'")
    | Tstruct n , Tarray (_,ty,Some s) -> 
	tab_struct  mark loc v1 v2 s ty n n1 n2
    | Tarray (_,ty,Some s) , Tstruct n -> 
	tab_struct mark loc v2 v1 s ty n n1 n2
    | Tarray (_,ty1,Some s1), Tarray(_,ty2,Some s2) ->
	make_and
	  (if compatible_type v1.nterm_type v2.nterm_type
	   then
	     (not_alias loc v1 v2)
	   else
	     nptrue)
	  (make_and 
	     (make_forall_range loc v1 s1 
		(fun t i -> local_separation mark loc (n1^"[i]") 
		     (indirection loc ty1 t) n2 v2))
	     (make_forall_range loc v2 s2  
		(fun t i -> local_separation true loc n1 v1 (n2^"[j]")
		     (indirection loc ty2 t))))
     | _, _ -> nptrue

    
let separation loc v1 v2 =
  local_separation false loc v1.var_name (var_to_term loc v1) 
    v2.var_name (var_to_term loc v2)

let rec full_tab_struct mark loc v1 v2 s ty n n1 n2=
  let l = begin
    match  tag_type_definition n with
      | TTStructUnion ((Tstruct _),fl) ->
	  fl
      | _ -> assert false
  end in
  if mark then
    List.fold_left 
      (fun p t -> 
	 if  full_compatible_type t.var_type v2.nterm_type 
	 then make_and p (not_alias loc v2 (in_struct v1 t))
	 else p)
      nptrue l
  else
  make_and (List.fold_left 
	      (fun p t -> 
		 if  full_compatible_type t.var_type v2.nterm_type 
		 then make_and p (not_alias loc v2 (in_struct v1 t))
		 else p)
	      nptrue l)
    (make_forall_range loc v2 s 
       (fun t i -> 
	  full_local_separation mark loc n1 v1 (n2^"[i]") (indirection loc ty t)))

and full_local_separation  mark loc n1 v1 n2 v2 =
  match (v1.nterm_type.Ctypes.ctype_node,v2.nterm_type.Ctypes.ctype_node) 
  with
    | Tarray (_,ty, None), _ ->
	error loc ("array size missing in `" ^ n1 ^ "'")
    | _, Tarray (_,ty, None) ->
	error loc ("array size missing in `" ^ n2 ^ "'")
    | Tstruct n , Tarray (_,ty,Some s) -> 
	full_tab_struct  mark loc v1 v2 s ty n n1 n2
    | Tarray (_,ty,Some s) , Tstruct n -> 
	full_tab_struct mark loc v2 v1 s ty n n1 n2
    | Tarray (_,ty1,Some s1), Tarray(_,ty2,Some s2) ->
	make_and
	  (if full_compatible_type v1.nterm_type v2.nterm_type
	   then
	     (not_alias loc v1 v2)
	   else
	     nptrue)
	  (make_and 
	     (make_forall_range loc v1 s1 
		(fun t i -> full_local_separation mark loc (n1^"[i]") 
		     (indirection loc ty1 t) n2 v2))
	     (make_forall_range loc v2 s2  
		(fun t i -> full_local_separation true loc n1 v1 (n2^"[j]")
		     (indirection loc ty2 t))))
    | Tpointer (_,ty1) , Tpointer (_,ty2) ->
	if full_compatible_type v1.nterm_type v2.nterm_type
	then
	  (not_alias loc v1 v2)
	else
	  nptrue
    | Tarray (_,ty2,Some s2) ,  Tpointer (_,ty1)
    | Tpointer (_,ty1), Tarray (_,ty2,Some s2) ->
	make_and
	  (if full_compatible_type v1.nterm_type v2.nterm_type
	   then
	     (not_alias loc v1 v2)
	   else
	     nptrue)
	  (make_forall_range loc v2 s2  
	     (fun t i -> full_local_separation true loc n1 v1 (n2^"[j]")
		(indirection loc ty2 t)))
    | Tstruct n, Tpointer (_,ty)  ->
	 let l = begin
	   match  tag_type_definition n with
	     | TTStructUnion ((Tstruct _),fl) ->
		 fl
	     | _ -> assert false
	 end in 
	 (List.fold_left 
	    (fun p t -> 
	       make_and p (full_local_separation mark loc n2 v2 n1 
			     (in_struct v1 t)))
	    nptrue l)
    |  Tpointer (_,ty), Tstruct n ->
	 let l = begin
	   match  tag_type_definition n with
	     | TTStructUnion ((Tstruct _),fl) ->
		 fl
	     | _ -> assert false
	 end in 
	 (List.fold_left 
	    (fun p t -> 
	       make_and p (full_local_separation mark loc n1 v1 n2 
			     (in_struct v2 t)))
	    nptrue l)
    | Tstruct n1, Tstruct n2 ->
	let l2 = begin
	   match  tag_type_definition n2 with
	     | TTStructUnion ((Tstruct _),fl) ->
		 fl
	     | _ -> assert false
	 end in	
	let l1 = begin
	   match  tag_type_definition n1 with
	     | TTStructUnion ((Tstruct _),fl) ->
		 fl
	     | _ -> assert false
	end in
	(List.fold_left 
	    (fun p1 t1 ->
	       (List.fold_left 
		  (fun p2 t2 ->
		     make_and p2 (full_local_separation mark loc n1 
				    (in_struct v1 t1) 
				    n2  (in_struct v2 t2)))
		  p1 l2))
		 nptrue l1)
    | _, _ -> nptrue

let fullseparation loc v1 v2 =
  full_local_separation false loc v1.var_name (var_to_term loc v1) 
    v2.var_name (var_to_term loc v2)




let rec unifier_type_why tw1 tw2 =
  match tw1,tw2 with
    | Pointer z1 , Pointer z2 ->
	unifier_zone z1 z2     
    | Addr z1 , Addr z2 ->
	unifier_zone z1 z2
    | Info.Int, Info.Int -> ()
    | Info.Float, Info.Float -> ()
    | Unit, Unit -> ()
    | Why_Logic s1, Why_Logic s2 when s1=s2 -> ()
    | Memory _, _ | _, Memory _ -> assert false
    | _ ->
	assert false
	  

and unifier_zone z1 z2 =
  let z1' = Info.repr z1
  and z2' = Info.repr z2
  in
  if z1' == z2' then ()
  else
    begin
(*      unifier_type_why z1'.type_why_zone z2'.type_why_zone;*)
      match z1'.repr, z2'.repr with
	| None, None -> 
	    if z1'.zone_is_var then z1'.repr <- Some z2' else 
	      if z2'.zone_is_var then z2'.repr <- Some z1' else
	      if z1'.number < z2'.number then z2'.repr <- Some z1'
	  else z1'.repr <- Some z2' 
	| _ -> assert false
    end


let rec term tyf t =
  match t.nterm_node with
    | NTconstant _ -> () 
    | NTvar v -> 
	if v.var_name = "result" then
	  (Format.eprintf "dans term@\n"; 
	  unifier_type_why v.var_why_type tyf)
    | NTapp ({napp_pred = f;napp_args = l} as call) -> 
      List.iter (term tyf) l;
      let assoc = List.map (fun z -> (z,make_zone true)) f.logic_args_zones in
      call.napp_zones_assoc <- assoc;
      let li =  
	List.map 
	  (fun v ->
	     match v.var_why_type with
	       | Pointer z as ty -> 
		   begin
		     try
		       Pointer (List.assoc z assoc)
		     with
			 Not_found -> ty
		   end
	       | ty -> ty)
	    f.logic_args in

      assert (List.length li = List.length l || 
	  (Format.eprintf " wrong arguments for %s : expected %d, got %d\n" 
	     f.logic_name (List.length li) (List.length l); false));
      List.iter2 
	(fun ty e ->
	   Format.eprintf "dans term2@\n";
	   unifier_type_why ty (type_why_for_term e)) li l
  | NTunop (_,t) 
(*  | NTstar t *)-> term tyf t 
  | NTbinop (t1,_,t2) -> term tyf t1; term tyf t2 
  | NTarrow (t,_,_,v) -> term tyf t
  | NTif (t1,t2,t3) -> term tyf t1; term tyf t2; term tyf t3
  | NTold t 
  | NTat (t,_) 
  | NTbase_addr t
  | NTblock_length t 
  | NTcast (_,t) 
  | NTrange (t,None,None,_) -> term tyf t
  | NTrange (t1,Some t2,None,_) | NTrange (t1,None,Some t2,_) -> 
      term tyf t1; term tyf t2
  | NTrange (t1,Some t2,Some t3,_) -> term tyf t1; term tyf t2; term tyf t3

let rec predicate tyf p =
  match p.npred_node with
  | NPfalse
  | NPtrue -> ()
  | NPapp ({napp_pred = f;napp_args = l} as call) -> 
      List.iter (term tyf) l;
      let assoc = List.map (fun z -> (z,make_zone true)) f.logic_args_zones in
      call.napp_zones_assoc <- assoc;
      let li =  
	List.map 
	  (fun v ->
	     match v.var_why_type with
	       | Pointer z as ty -> 
		   begin
		     try
		       Pointer (List.assoc z assoc)
		     with
			 Not_found -> ty
		   end
	       | ty -> ty)
	    f.logic_args in

      assert (List.length li = List.length l || 
	  (Format.eprintf " wrong arguments for %s : expected %d, got %d\n" 
	     f.logic_name (List.length li) (List.length l); false));
      List.iter2 
	(fun ty e ->
	   Format.eprintf "dans predicate@\n";
	   unifier_type_why ty (type_why_for_term e)) li l
  | NPrel (t1,_,t2) ->
      term tyf t1; term tyf t2;
      Format.eprintf "dans predicate2@\n";
      unifier_type_why (type_why_for_term t1) (type_why_for_term t2)
  | NPand (p1,p2) 
  | NPor (p1,p2) 
  | NPimplies (p1,p2) 
  | NPiff (p1,p2) -> predicate tyf p1; predicate tyf p2
  | NPnot p -> predicate tyf p
  | NPif (t,p1,p2) -> term tyf t; predicate tyf p1; predicate tyf p2
  | NPforall (_,p) 
  | NPexists (_,p) 
  | NPold p 
  | NPat (p,_) -> predicate tyf p
  | NPvalid t -> term tyf t
  | NPvalid_index (t1,t2) -> term tyf t1; term tyf t2
  | NPvalid_range (t1,t2,t3) -> term tyf t1; term tyf t2; term tyf t3
  | NPfresh  t -> term tyf t
  | NPnamed (_,p) -> predicate tyf p


    
		    
let rec calcul_zones expr =
  match expr.nexpr_node with 
    | NEnop -> ()
    | NEconstant _ 
    | NEstring_literal _ 
    | NEvar _ -> ()
    | NEarrow (e,_,_,_) 
(*    | NEstar e*) -> calcul_zones e
    | NEseq (e1,e2) -> calcul_zones e1; calcul_zones e2
    | NEassign_op (lv,_,e) 
    | NEassign (lv,e) -> calcul_zones lv; calcul_zones e;
	let tw1 = type_why lv in
	let tw2 = type_why e in
	Format.eprintf "dans calcul_zone@\n";
	unifier_type_why tw1 tw2
    | NEunary (_,e) -> calcul_zones e
    | NEincr (_,e) -> calcul_zones e
    | NEbinary (e1,Bsub_pointer,e2) | NEbinary (e1,Blt_pointer,e2) 
    | NEbinary (e1,Bgt_pointer,e2) | NEbinary (e1,Ble_pointer,e2) 
    | NEbinary (e1,Bge_pointer,e2) | NEbinary (e1,Beq_pointer,e2) 
    | NEbinary (e1,Bneq_pointer,e2)   -> calcul_zones e1; calcul_zones e2;
	let tw1 = type_why e1 in
	let tw2 = type_why e2 in
	Format.eprintf "dans calcul_zone2@\n";
	unifier_type_why tw1 tw2
    | NEbinary (e1,_,e2) -> calcul_zones e1; calcul_zones e2
    | NEcall ({ncall_fun = e;ncall_args = l} as call) -> 
	List.iter calcul_zones l;
	let f = match e.nexpr_node with 
	  | NEvar (Fun_info f) -> f
	  | _  -> assert false 
	in
	let assoc = List.map (fun z -> (z,make_zone true)) f.args_zones in
	call.ncall_zones_assoc <- assoc;
	let arg_types =
	  List.map 
	    (fun v ->
	       match v.var_why_type with
		 | Pointer z as ty -> 
		     begin
		       try
			 Pointer (List.assoc z assoc)
		       with
			   Not_found -> ty
		     end
		 | ty -> ty)
	    f.args 
	in
	List.iter2 (fun ty e ->
		      Format.eprintf "calcul_zone3@\n";
		      unifier_type_why ty (type_why e))
	  arg_types l
    | NEcond (e1,e2,e3)->  calcul_zones e1; calcul_zones e2; calcul_zones e3
    | NEcast (_,e) -> calcul_zones e
 
let rec c_initializer ty tw init =
  match init with 
    | Iexpr e -> calcul_zones e; Format.eprintf "c_initializer@\n";unifier_type_why tw (type_why e)
    | Ilist l -> 
	match ty.ctype_node with  
	  | Tstruct tag  ->
	      begin
		match tag_type_definition tag with
		  | TTStructUnion(ty,fields) ->
		      List.iter2
			(fun f v ->
			    c_initializer f.var_type f.var_why_type v)
			fields l
		  | _ -> assert false
	      end
	  | Tarray (_,ty,_) ->	      
	      (*let z = match tw with
		| Pointer z -> z
		| _ -> 
		    let (a,t) = output_why_type tw in
		    Format.eprintf "anomaly : c_init type (";
		    List.iter (fun t -> Format.eprintf ",@ %s" t) a;
		    Format.eprintf ") %s not a pointer\n" t;
		    assert false (*mal typé*)
	      in*)
	      let tw = type_type_why ty false in
	      List.iter (fun init -> c_initializer ty tw init) l 
	  | _ -> assert false


let option_iter f x =
  match x with
    | None -> ()
    | Some x -> f x

let loop_annot tyf la =
  option_iter (predicate tyf) la.invariant;
  option_iter (List.iter (term tyf)) la.loop_assigns;
  option_iter (fun (t,_) -> term tyf t) la.variant

let spec tyf sp =
  begin
  match sp.requires with
    | None -> ()
    | Some p -> predicate tyf p
  end;
  begin
  match sp.assigns with
    | None -> ()
    | Some l -> List.iter (term tyf) l
  end;
  begin
    match sp.ensures with
      | None -> ()
      | Some p -> predicate tyf p
  end;
  begin
    match sp.decreases with
      | None -> ()
      | Some (t,_) -> term tyf t
  end

let rec statement twf st =
  match st.nst_node with 
    | NSnop | NSreturn None | NSbreak | NScontinue | NSassert _ 
    | NSlogic_label _ -> ()
    | NSexpr e -> calcul_zones e
    | NSif (e,st1,st2) -> calcul_zones e; statement twf st1; statement twf st2 
    | NSwhile (lannot,e,st) 
    | NSdowhile (lannot,st,e)-> 
	loop_annot twf lannot; calcul_zones e;statement twf st
    | NSfor (lannot, e1, e2, e3, st)-> 
	loop_annot twf lannot;
	calcul_zones e1; calcul_zones e2; 
	calcul_zones e3; statement twf st
    | NSblock ls -> List.iter (statement twf) ls
    | NSreturn (Some e) -> calcul_zones e ;
	Format.eprintf "statement@\n";
	unifier_type_why twf (type_why e)	
    | NSlabel (_,st) -> statement twf st
    | NSswitch (e1, e2, l) -> calcul_zones e1;
	List.iter (fun (x, y) -> List.iter (statement twf) y) l
    | NSspec (sp,st) -> spec twf sp; statement twf st
    | NSdecl (_, v, None, st) -> statement twf st
    | NSdecl (_, v, Some i, st) -> 
	c_initializer v.var_type v.var_why_type i;
	statement twf st 
	

let add_zone ty l =
  match ty with
    | Pointer z -> 
	begin match z.repr with 
	  | None -> z::l
	  | Some _ -> l
	end
    | _ -> l
      
let collect_zones args ret_type =	
  let l =
    List.fold_left  
      (fun l v ->
	 add_zone v.var_why_type l) [] args
  in
  add_zone ret_type l


let global_decl e =
  match e with 
    | Naxiom (_,sp) | Ninvariant (_,sp) | Ninvariant_strong (_,sp) ->
	predicate Unit sp
    | Nlogic (f, NPredicate_def (_,p)) -> predicate Unit p;
	f.logic_args_zones <- 
	  List.fold_left  
	  (fun l v ->
	     match v.var_why_type with 
	     | Pointer z -> 
		 begin match z.repr with 
		   | None -> z::l
		   | Some _ -> l
		 end
	     | _ -> l) [] f.logic_args
    | Nlogic (f, NFunction_def (_,_,t)) -> term Unit t;
	f.logic_args_zones <- 
	  List.fold_left  
	  (fun l v ->
	     match v.var_why_type with 
	     | Pointer z -> 
		 begin match z.repr with 
		   | None -> z::l
		   | Some _ -> l
		 end
	     | _ -> l) [] f.logic_args
    | Nlogic _ -> ()
    | Nfunspec (sp,_,f) -> 
	spec f.type_why_fun sp;
	f.args_zones <- collect_zones f.args f.type_why_fun
    | Ntypedef _ | Ntypedecl _ | Ndecl (_,_,None) | Ntype _ -> ()
    | Ndecl (_, v, Some i) -> c_initializer v.var_type v.var_why_type i
    | Nfundef (sp, _, f, st) -> 
	spec f.type_why_fun sp; 
	statement f.type_why_fun st; 
	f.args_zones <- collect_zones f.args f.type_why_fun

let file =  List.iter (fun d -> global_decl d.node)
