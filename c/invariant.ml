open Creport
open Info
open Ctypes
open Clogic
open Cenv
open Cnorm

let var_to_term loc v =
  {
    nterm_node = NTvar v; 
    nterm_loc = loc;
    nterm_type = v.var_type}

let indirection loc ty t =
  { nterm_node = NTstar t; 
    nterm_loc = loc; 	   
    nterm_type = ty}

let noattr_type ty =
  {ctype_node = ty;
   ctype_storage = No_storage;
   ctype_const = false;
   ctype_volatile = false;
  }

let noattr_term ty t= 
  { nterm_node = t; 
    nterm_loc = Loc.dummy;
    nterm_type = ty }

let find_pred x = snd (find_pred x)
  
let rec predicate_for name t =
  match t.nterm_type.ctype_node with
    | Tstruct (n) ->
	(*	NPand *)
	NPvalid t
	  (*,
 	    NPapp (find_pred ("valid_" ^ n), [t]))*)
    | Tarray (ty, None) ->
	error Loc.dummy ("array size missing in `" ^ name ^ "'")
    | Tarray (ty, Some s) ->
	  let i = default_var_info "counter" in
	  let vari = noattr_term c_int (NTvar i) in
	  let ineq = NPand 
		       (NPrel (nzero, Le, vari),
			NPrel (vari, Lt, 
			       int_nconstant (Int64.to_string s))) in
	  let pre = predicate_for name vari in
	  if pre = NPtrue 
	  then
	    NPand ((NPvalid t),(NPvalid_range (t,(int_nconstant "0"), 
			  (int_nconstant (Int64.to_string s)))))
	  else
	    NPand (NPvalid t, 
		   (NPand 
		      ((NPvalid_range (t,(int_nconstant "0"), 
			  (int_nconstant (Int64.to_string s)))),
		      (NPforall ([noattr_type (Tint (Signed, Ctypes.Int)), i], 
				NPimplies (ineq, pre))))))
     | _ -> NPtrue

let axiom_for s ty t v validity=
  Cast.Naxiom 
    ("valid_" ^ s ^ "_pointer", 
     NPforall ([ty,v], NPimplies (NPvalid t, validity)))
(***
		  NPapp (find_pred ("internal_separation_" ^ s), [t])))))
***)

let not_alias loc x y = 
  let ba t = { nterm_node = NTbase_addr t; 
	       nterm_loc = loc;
	       nterm_type = c_addr } in 
  NPrel (ba x, Neq, ba y)

let diff loc x y = 
  NPrel ( x, Neq,  y)

let make_implies p1 = function
  | NPtrue -> NPtrue
  | p2 -> NPimplies (p1, p2)

let make_forall q = function
  | NPtrue -> NPtrue
  | p -> NPforall (q, p)

let fresh_index = 
  let r = ref (-1) in fun () -> incr r; "index_" ^ string_of_int !r

let make_forall_range loc t b f =
  if b = Int64.one
  then f t nzero
  else
    let i = default_var_info (fresh_index ()) in
    let vari = { nterm_node = NTvar i; 
		 nterm_loc = loc;
		 nterm_type = c_int } in
    let ti = 
      { nterm_node = NTbinop (t, Badd, vari); 
	nterm_loc = loc;
	nterm_type = t.nterm_type }
    in
    let ineq = NPand (NPrel (nzero, Le, vari),
		      NPrel (vari, Lt, int_nconstant (Int64.to_string b))) in
    make_forall [c_int, i] (make_implies ineq (f ti vari))
     
(* assumes v2 is an array of objects of type ty *)
let rec tab_struct loc mark v1 v2 s ty n n1 n2=
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
      NPtrue l
  else
  make_and (List.fold_left 
	      (fun p t -> 
		 if  compatible_type t.var_type v2.nterm_type 
		 then make_and p (not_alias loc v2 (in_struct v1 t))
		 else p)
	      NPtrue l)
    (make_forall_range loc v2 s 
       (fun t i -> 
	  local_separation loc mark n1 v1 (n2^"[i]") (indirection loc ty t)))

and local_separation loc mark n1 v1 n2 v2 =
  match (v1.nterm_type.Ctypes.ctype_node,v2.nterm_type.Ctypes.ctype_node) 
  with
    | Tarray (ty, None), _ ->
	error loc ("array size missing in `" ^ n1 ^ "'")
    | _, Tarray (ty, None) ->
	error loc ("array size missing in `" ^ n2 ^ "'")
    | Tstruct n1, Tstruct n2 ->
	let l1 = begin
	  match  tag_type_definition n1 with
	    | TTStructUnion ((Tstruct _),fl) ->
		fl
	    | _ -> assert false
	end in
	let l2 = begin
	  match  tag_type_definition n2 with
	    | TTStructUnion ((Tstruct _),fl) ->
		fl
	    | _ -> assert false
	end in
	make_and
	  (if not (compatible_type v1.nterm_type v2.nterm_type)
	   then
	     (make_and 
		(List.fold_left
		   (fun p v ->
		      if compatible_type v1.nterm_type v.var_type
		      then
			make_and (not_alias loc v1 (in_struct v2 v)) p
		      else
			p)
		   NPtrue l2)
		(List.fold_left
		   (fun p v ->
		      if compatible_type v2.nterm_type v.var_type
		      then
			make_and (not_alias loc v2 (in_struct v1 v)) p
		      else
			p)
		   NPtrue l1))
	   else NPtrue)
	  (List.fold_left 
	     (fun p t1 -> 
		List.fold_left 
		  (fun p t2 -> 
		     make_and p 
		       (local_separation loc mark n1 (in_struct v1 t1) 
			  n2 (in_struct v2 t2)))
		  p l2)
	     NPtrue l1)
    | Tstruct n , Tarray (ty,Some s) -> tab_struct loc mark v1 v2 s ty n n1 n2
    | Tarray (ty,Some s) , Tstruct n -> tab_struct loc mark v2 v1 s ty n n1 n2
    | Tarray (ty1,Some s1), Tarray(ty2,Some s2) ->
	make_and
	  (if compatible_type v1.nterm_type v2.nterm_type
	   then
	     (not_alias loc v1 v2)
	   else
	     NPtrue)
	  (make_and 
	     (make_forall_range loc v1 s1 
		(fun t i -> local_separation loc mark (n1^"[i]") 
		     (indirection loc ty1 t) n2 v2))
	     (make_forall_range loc v2 s2  
		(fun t i -> local_separation loc true n1 v1 (n2^"[j]") 
		     (indirection loc ty2 t))))
    | _, _ -> NPtrue


let rec separation_intern ?(use_pred=false) loc n1 v1 =
  match v1.nterm_type.Ctypes.ctype_node with
    | Tarray (_,None) -> 
	error loc ("array size missing in `" ^ n1 ^ "'")
    | Tarray(ty,Some s) -> 
	begin
	  match ty.Ctypes.ctype_node with
	    | Tarray (_,None) -> 
		error loc ("array size missing in `" ^ n1 ^ "[i]'")
	    | Tarray (_,_)  
	    | Tstruct _ ->
		make_and
		  (make_forall_range loc v1 s 
		     (fun t1 i1 ->
			make_forall_range loc v1 s
			  (fun t2 i2 -> 
			     if i1 = nzero && i2 = nzero then NPtrue 
			     else
			       make_implies (NPrel (i1, Neq, i2)) 
				 (not_alias loc t1 t2))))
		  (make_forall_range loc v1 s 
		     (fun t i -> 
			separation_intern ~use_pred:true loc (n1^"[i]") 
			  (noattr_term ty t.nterm_node)))
		  
	    | _ -> NPtrue
	end
    | Tstruct n -> 
	let l =
	  begin
	    match  tag_type_definition n with
	      | TTStructUnion ((Tstruct _),fl) ->
		  fl
	      | _ -> assert false
	  end  
	in
	let rec f l =
	  match l with
	    | (v::l) -> 
		make_and
		  (make_and 
		     (separation_intern ~use_pred:true loc v.var_name 
			(in_struct v1 v))
		     (List.fold_left 
			(fun acc x -> 
			   make_and acc (local_separation loc false
					   v.var_name (in_struct v1 v) 
					   x.var_name (in_struct v1 x))) 
			NPtrue l))
		  (f l)
	    | [] -> NPtrue
	in
	if use_pred then
	  NPapp (find_pred ("internal_separation_" ^ n), [v1])
	else
	  f l
    | _ -> 
	NPtrue

    
let noattr_located n =  
  { Cast.node = n; Cast.loc = Loc.dummy }

(*

  [separation s1 ty1 s2 (ty2,fl) decls]

  [s1], [s2] are struct names

  [ty1] is the type of [s1]

  [ty2] is the type of [s2]

  [fl] is the list of fields of [s2]

  this function adds to [decls] an axiom which says that any pointer
  statically inside struct [s1] is different from any pointer inside
  struct [s2].

*)

let separation_done = Hashtbl.create 17

let separation s1 ty1 s2 (ty2,fl) decls =
  if not (Hashtbl.mem separation_done (s2, s1)) then begin
    Hashtbl.add separation_done (s1, s2) ();
    let ty2 = noattr_type ty2 in
    let t1_var = default_var_info s1 in
    let s2' = if s1 = s2 then s2 ^ "1" else s2 in
    let t2_var = default_var_info s2' in
    let t1 = { nterm_node = NTvar t1_var; 
	       nterm_loc = Loc.dummy;
	       nterm_type = ty1 } in
    let t2 = { nterm_node = NTvar t2_var; 
	       nterm_loc = Loc.dummy;
	       nterm_type = ty2 } in
    let pred = local_separation Loc.dummy false s1 t1 s2 t2 in
    let pred = NPimplies ((diff Loc.dummy t1 t2),pred) in
    noattr_located (Cast.Naxiom ( 
		      ("separation_" ^ s1 ^ "_" ^ s2),
		      NPforall ((ty1,t1_var)::[ty2,t2_var] , pred )))::decls
  end else
    decls

let make_var x ty =
  let info = default_var_info x in
  Info.set_var_type (Var_info info) ty;
  info, 
  { nterm_node = NTvar info; nterm_loc = Loc.dummy; nterm_type = ty } 
    
let add_predicates l =
  (* first we enter all names in environment *)
  Cenv.iter_all_struct 
    (fun s (ty,fl) ->
       let ty = noattr_type ty in
       (List.iter 
	 (fun f ->
	    let info = Info.default_logic_info 
			 ("valid_" ^ s ^ "_" ^ f.var_name) in 
	    Cenv.add_pred ("valid_" ^ s ^ "_" ^ f.var_name)  ([ty], info))) fl;
       let info = Info.default_logic_info ("internal_separation_" ^ s) in 
       Cenv.add_pred ("internal_separation_" ^ s) 
	 ([noattr_type (Tpointer ty)],info));
  (* then we define predicates for all structures *)
  let f s (ty,fl) l2 = 
    let ty = noattr_type ty in
    let st,t = make_var s ty in
    let l2 =
      List.fold_right 
	 (fun f acc -> 
	    let tf = 
	      { nterm_node = NTarrow (t, f); 
		nterm_loc = Loc.dummy;
		nterm_type = f.var_type } 
	    in
	    let infox,x = make_var f.var_name f.var_type in
	    let s_f = s ^ "_" ^ f.var_name in
	    let info = find_pred ("valid_" ^ s_f) in
	    let axiom_s_f =
	      noattr_located (axiom_for s_f ty t st (NPapp (info, [tf]))) 
	    in
	    let predicate_s_f =
	      noattr_located 
		(Cast.Nlogic 
		   (info, NPredicate_def ([infox,f.var_type], 
					  predicate_for s x))) 
	    in
	    predicate_s_f :: axiom_s_f :: acc)
	 fl l2
    in
    let info = find_pred ("internal_separation_" ^ s) in 	    
    let axiom_s_f =
      noattr_located (axiom_for s ty t st (NPapp (info, [t]))) 
    in
    let l2 = 
      axiom_s_f :: 
      noattr_located (
	Cast.Nlogic (info,
		     NPredicate_def 
		       ([st,ty],
			(separation_intern Loc.dummy s t))))::l2 in
    Cenv.fold_all_struct (separation s ty) l2
  in
  Cenv.fold_all_struct f l
