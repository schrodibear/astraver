open Creport
open Info
open Ctypes
open Clogic
open Cenv
open Cnorm
open Cprint
open Cseparation

let var_to_term loc v =
  {
    nterm_node = NTvar v; 
    nterm_loc = loc;
    nterm_type = v.var_type}

let indirection loc ty t =
  let info = make_field ty in
  let info = declare_arrow_var info  in
  let zone = find_zone_for_term t in
  let () = type_why_new_zone zone info in
  { nterm_node = NTarrow (t, zone, info); 
    nterm_loc = loc; 	   
    nterm_type = ty;}

let noattr_type ty =
  {ctype_node = ty;
   ctype_storage = No_storage;
   ctype_const = false;
   ctype_volatile = false;
   ctype_ghost = false;
  }

let noattr_term ty t= 
  { nterm_node = t; 
    nterm_loc = Loc.dummy_position;
    nterm_type = ty;}

let find_pred x = snd (find_pred x)
  
let rec predicate_for name t =
  match t.nterm_type.ctype_node with
    | Tstruct (n) ->
	(*	NPand *)
	npvalid t
	  (*,
 	    NPapp (find_pred ("valid_" ^ n), [t]))*)
    | Tarray (_,ty, None) ->
	error Loc.dummy_position ("array size missing in `" ^ name ^ "'")
    | Tarray (_,ty, Some s) ->
	  let i = default_var_info "counter" in
	  let vari = noattr_term c_int (NTvar i) in
	  let ineq = npand
		       (nprel (nzero, Le, vari),
			nprel (vari, Lt, 
			       int_nconstant (Int64.to_string s))) in
	  let pre = predicate_for name vari in
	  if pre = nptrue 
	  then
	    npand ((npvalid t),(npvalid_range (t,(int_nconstant "0"), 
			  (int_nconstant (Int64.to_string (Int64.pred s))))))
	  else
	    npand (npvalid t, 
		   (npand 
		      ((npvalid_range (t,(int_nconstant "0"), 
			  (int_nconstant (Int64.to_string (Int64.pred s))))),
		      (make_forall 
			 [noattr_type (Tint (Signed, Ctypes.Int)), i]
			 (make_implies ineq pre)))))
     | _ -> nptrue


let fresh_index = 
  let r = ref (-1) in fun () -> incr r; "index_" ^ string_of_int !r

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
	nterm_type = t.nterm_type;}
    in
    let pred = (f ti vari) in
    if pred = nptrue
    then 
      nptrue
    else
      let ineq = npand (nprel (nzero, Le, vari),
			nprel (vari, Lt, int_nconstant (Int64.to_string b))) in
      make_forall [c_int, i] (make_implies ineq pred)
     
let rec tab_struct loc v1 v2 s ty n n1 n2=
  (make_forall_range loc v2 s 
     (fun t i -> 
	local_separation loc n1 v1 (n2^"[i]") (indirection loc ty t)))

and local_separation loc n1 v1 n2 v2 =
  match (v1.nterm_type.Ctypes.ctype_node,v2.nterm_type.Ctypes.ctype_node) 
  with
    | Tarray (_,ty, None), _ ->
	error loc ("array size missing in `" ^ n1 ^ "'")
    | _, Tarray (_,ty, None) ->
	error loc ("array size missing in `" ^ n2 ^ "'")
    | Tstruct n , Tarray (_,ty,Some s) -> tab_struct loc v1 v2 s ty n n1 n2
    | Tarray (_,ty,Some s) , Tstruct n -> tab_struct loc v2 v1 s ty n n1 n2
    | Tarray (_,ty1,Some s1), Tarray(_,ty2,Some s2) ->
	make_and
	  (if compatible_type v1.nterm_type v2.nterm_type
	   then
	     (not_alias loc v1 v2)
	   else
	     nptrue)
	  (make_and 
	     (make_forall_range loc v1 s1 
		(fun t i -> local_separation loc (n1^"[i]") 
		     (indirection loc ty1 t) n2 v2))
	     (make_forall_range loc v2 s2  
		(fun t i -> local_separation loc n1 v1 (n2^"[j]") 
		     (indirection loc ty2 t))))
    | _, _ -> nptrue

    


let rec separation_intern2  n1 v1 =
  match v1.nterm_type.Ctypes.ctype_node with
    | Tarray (_,_,None) -> 
	error Loc.dummy_position ("array size missing in `" ^ n1 ^ "'")
    | Tarray(_,ty,Some s) ->
	  begin
	    match ty.Ctypes.ctype_node with
	      | Tarray (_,_,None) -> 
		error Loc.dummy_position ("array size missing in `" ^ n1 
				 ^ "[i]'")
	      | Tstruct _ ->
		  (make_forall_range Loc.dummy_position v1 s 
		     (fun t1 i1 ->
			make_forall_range Loc.dummy_position v1 s
			  (fun t2 i2 -> 
			     if i1 = nzero && i2 = nzero then nptrue 
			     else
			       make_implies (nprel (i1, Neq, i2)) 
				 (not_alias Loc.dummy_position t1 t2))))
	      | Tarray _ ->  
		  make_and
		    (make_forall_range Loc.dummy_position v1 s 
		       (fun t1 i1 ->
			  make_forall_range Loc.dummy_position v1 s
			    (fun t2 i2 -> 
			       if i1 = nzero && i2 = nzero then nptrue 
			       else
				 make_implies (nprel (i1, Neq, i2)) 
				   (not_alias Loc.dummy_position t1 t2))))
		    (make_forall_range Loc.dummy_position v1 s 
		       (fun t i -> 
			  separation_intern2 n1 
			    (noattr_term ty t.nterm_node)))    
	      | _ -> nptrue
	  end
    | _ -> 
	nptrue

(*let rec separation loc n1 v1 n2 v2 =
  match (v1.nterm_type.Ctypes.ctype_node,v2.nterm_type.Ctypes.ctype_node) 
  with
    | Tarray (ty, None), _ ->
	error loc ("array size missing in `" ^ n1 ^ "'")
    | _, Tarray (ty, None) ->
	error loc ("array size missing in `" ^ n2 ^ "'")
    | Tstruct n , Tarray (ty,Some s) -> 
	if compatible_type ty v1.nterm_type 
	then
	  (make_forall_range loc v2 s 
	     (fun t i -> not_alias loc 
		(indirection loc ty 
		   (noattr_term (noattr_type (Tpointer ty)) 
		      (NTbinop (t,Badd,i)))) v1))
	else
	  NPtrue
    | Tarray (ty,Some s) , Tstruct n ->
	if compatible_type ty v2.nterm_type 
	then
	  (make_forall_range loc v1 s 
	     (fun t i -> not_alias loc 
		(indirection loc ty 
		   (noattr_term (noattr_type (Tpointer ty)) 
		      (NTbinop (t,Badd,i)))) v2))
	else
	  NPtrue
    | Tarray (ty1,Some s1), Tarray(ty2,Some s2) ->
	make_and
	  (if compatible_type v1.nterm_type v2.nterm_type
	   then
	     (not_alias loc v1 v2)
	   else
	     NPtrue)
	  (make_and 
	     (make_forall_range loc v1 s1 
		(fun t i -> separation loc (n1^"[i]") 
		     (indirection loc ty1  
			(noattr_term (noattr_type (Tpointer ty1)) 
			   (NTbinop (t,Badd,i)))) n2 v2))
	     (make_forall_range loc v2 s2  
		(fun t i -> separation loc n1 v1 (n2^"[j]") 
		     (indirection loc ty2  
			(noattr_term (noattr_type (Tpointer ty2)) 
			   (NTbinop (t,Badd,i)))))))
    | _, _ -> NPtrue
*)
  
let rec fold_2 f l = 
  match l with 
    | v::l ->
	List.fold_left (fun acc x ->(f v x)@acc) (fold_2 f l) l
    | _ -> [] 

let noattr_located n =  
  { Cast.node = n; Cast.loc = Loc.dummy_position }


let separation_first mark diag v1 v2 =
  let sep = if mark then "%separation1" else "%separation2" in
  let n1 =  v1.var_unique_name in
  let n2 =  v2.var_unique_name in
  match v1.var_type.Ctypes.ctype_node,v2.var_type.Ctypes.ctype_node with
    | Tarray (_,_,None), _  ->
	error Loc.dummy_position ("array size missing in `" ^ n1 ^ "[i]'") 
    | _ , Tarray (_,_,None) ->
	error Loc.dummy_position ("array size missing in `" ^ n2 ^ "[i]'") 
    | Tstruct _ , Tstruct _ ->
	let pre = sep ^ n1 ^ "_" ^ n2 in
	let info = Info.default_logic_info (pre) in
	info.logic_heap_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	Cenv.add_pred (pre)  ([], info);
	[noattr_located (
	   Cast.Ninvariant_strong (
	     "separation" ^ n1 ^ "_" ^ n2 , 
	     npapp(find_pred (pre),[])))]
    | Tarray (_,ty,Some s) , Tstruct _ -> 
	if compatible_type ty v2.var_type then
	  let pre = sep ^ "_range1_" ^ n1 ^ "_" ^ n2 in 
	  let info = Info.default_logic_info (pre) in
	  info.logic_heap_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  [noattr_located 
	     (Cast.Ninvariant_strong (
		"separation_" ^ n1 ^ "_" ^ n2,
		npapp
		  (find_pred (pre ), 
		   [noattr_term 
		      (noattr_type (Tint (Signed,Int)))
		      (NTconstant (IntConstant 
				     (Int64.to_string s)))])))]
	else []
    | Tstruct _ ,Tarray (_,ty,Some s)  -> 
	if compatible_type ty v1.var_type then
	  let pre = sep ^ "_range1_" ^ n1 ^ "_" ^ n2 in 
	  let info = Info.default_logic_info (pre) in
	  info.logic_heap_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  [noattr_located
	     (Cast.Ninvariant_strong (
		"separation_" ^ n1 ^ "_" ^ n2,
		npapp(
		  find_pred (pre), 
		  (*(create_term n2)::(create_term n1)::*)
		    [noattr_term 
		       (noattr_type (Tint (Signed,Int)))
		       (NTconstant (IntConstant 
				      ((Int64.to_string s))))])))]
	else []
    | Tarray (_,ty1, Some s1),  Tarray(_,ty2, Some s2) ->
	let make_sub_term p ty v = 
	  let zone = find_zone_for_term p in
	  let () = type_why_new_zone zone v in
	  noattr_term ty (NTarrow (p, zone,v)) in
	if mark then
	  let pre = sep ^ n1 ^ "_" ^ n2 in
	  let info = Info.default_logic_info (pre) in
	  info.logic_heap_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  let ty = noattr_type (Tpointer (Not_valid,noattr_type (Tvoid))) in
	  let var = default_var_info (fresh_index()) in
	  set_var_type (Var_info var) ty false;
	  let term = noattr_term ty (NTvar var) in
	  noattr_located (
	    Cast.Ninvariant_strong (
	      "internal_separation" ^ n1 ^ "_" ^ n2 , 
	      npapp(find_pred (pre),[])))::
	    [noattr_located
	       (Cast.Ninvariant_strong (
		  "separation_" ^ n1 ^ "_" ^ n2,
		  make_forall 
		    [ty,var] 
		    (local_separation Loc.dummy_position n1 
		       (make_sub_term term ty1 v1) n2
		       (make_sub_term term ty2 v2))))]
	else
 	  let pre = sep ^ n1 ^ "_" ^ n2 in
	  let info = Info.default_logic_info (pre) in
	  info.logic_heap_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  let ty = noattr_type (Tpointer (Not_valid,noattr_type (Tvoid))) in
	  let var1 = default_var_info (fresh_index()) in
	  let var2 = default_var_info (fresh_index()) in
	  set_var_type (Var_info var1) ty false;
	  set_var_type (Var_info var2) ty false;
	  let term1 = noattr_term ty (NTvar var1) in
	  let term2 = noattr_term ty (NTvar var2) in
	  let pred = (local_separation Loc.dummy_position n1 
			(make_sub_term term1 ty1 v1)
			n2 
			(make_sub_term term2 ty2 v2)) in
	  if pred = nptrue then []
	  else
	    noattr_located (
	      Cast.Ninvariant_strong (
		"separation" ^ n1 ^ "_" ^ n2 , 
		npapp(find_pred (pre),[])))::
	      [noattr_located
		 (Cast.Ninvariant_strong 
		    ("separation_" ^ n1 ^ "_" ^ n2,
		     make_forall 
		       [ty,var1]
		       (make_forall 
			  [ty,var2]
			  (if diag 
			   then 
			     make_implies (nprel (term1,Neq,term2)) pred
			 else
			   pred))))]
    | _ , _ -> []
	  

let rec separation_intern n =
  let l =
    begin
      match  tag_type_definition n with
	| TTStructUnion ((Tstruct _),fl) ->
	    fl
	| _ -> assert false
    end  
  in
  let array_intern_separation v1  =
    let n1 = v1.var_unique_name in
    match v1.var_type.Ctypes.ctype_node with
      | Tarray (_,_,None) -> 
	  error Loc.dummy_position ("array size missing in `" 
			       ^ n1 ^ "[i]'")
      | Tarray (_,ty,Some s) ->
	  begin
	    match ty.Ctypes.ctype_node with
	      | Tstruct _ -> 
		  let pre = "%separation1_range_" ^ n1  in 
		  let info = Info.default_logic_info (pre) in
		  info.logic_heap_args <- HeapVarSet.singleton v1 ; 
		  Cenv.add_pred (pre)  ([], info);
		  [noattr_located (Cast.Ninvariant_strong (
				    "internal_separation_" ^ n1 ^ "_array1" , 
				   npapp(
				     find_pred (pre ),
				     (*(create_term n1)::*)
				     [noattr_term (noattr_type 
						     (Tint (Signed,Int))) 
					(NTconstant 
					    (IntConstant 
					       (Int64.to_string s)))])))]
	      |Tarray _ ->	
		 let pre = "%separation1_range_" ^ n1  in 
		 let info = Info.default_logic_info (pre) in
		 info.logic_heap_args <- HeapVarSet.singleton v1 ; 
		 Cenv.add_pred (pre)  ([], info);
		 noattr_located (Cast.Ninvariant_strong (
				   "internal_separation_" ^ n1 ^ "_array1" , 
				   npapp(
				     find_pred (pre ),
				     (*(create_term n1)::*)
				      [noattr_term (noattr_type 
						      (Tint (Signed,Int))) 
					 (NTconstant 
					    (IntConstant 
					       (Int64.to_string s)))])))::
		   noattr_located (Cast.Ninvariant_strong (
				     "internal_separation_" ^ n1 ^ "_array2",
				     (make_forall_range Loc.dummy_position 
					(var_to_term Loc.dummy_position v1) s 
					(fun t i -> 
					    separation_intern2 n1 
					      (noattr_term 
						 (noattr_type (Tpointer (Not_valid,ty))) 
						 (NTbinop (t,Badd,i)))))))::[]
	      | _ -> []
	  end
      | _ -> []
  in
  (List.fold_left (fun acc t ->
     array_intern_separation t@acc) [] l) @ 
    (fold_2 (separation_first true false ) l)  


let separation_2_struct s1 l1 s2 l2 acc=
  let l1 = snd l1 in
  let l2 = snd l2 in
  List.fold_left (fun acc1 t1 ->
		    (List.fold_left
		       (fun acc2 t2 ->
			  separation_first false (t1=t2) t1 t2@acc2) acc1 l2)) 
    acc l1

let add_predicates l =
  let f s (ty,fl) l2 = 
    let l2 = List.fold_right 
      (fun f acc -> 
	 begin
	   match f.var_type.Ctypes.ctype_node with
	     | Tstruct n ->
		 let pre = "%valid_acc_" ^ n  in 
		 let info = Info.default_logic_info (pre) in
		 info.logic_heap_args <- HeapVarSet.singleton f; 
		 Cenv.add_pred (pre)  ([], info);
		 [noattr_located (
		    Cast.Ninvariant_strong (
		      "valid" ^ n,npapp(find_pred (pre),[])))]
	     | Tarray(_,ty, Some s)->
		 let n1 = f.var_unique_name in
		 let pre = "%valid_acc_" ^ n1 in 
		 let info = Info.default_logic_info (pre) in
		 info.logic_heap_args <- HeapVarSet.singleton f; 
		 Cenv.add_pred (pre)  ([], info);
		 let pre2 = "%valid_acc_range_" ^ n1  in 
		 let info2 = Info.default_logic_info (pre2) in
		 info2.logic_heap_args <- HeapVarSet.singleton f; 
		 Cenv.add_pred (pre2)  ([], info2);
		 noattr_located (
		 Cast.Ninvariant_strong ("valid_array"^ n1,
					 npapp(find_pred (pre),[])))::
		   noattr_located (
		     Cast.Ninvariant_strong 
		       ("valid_range" ^ n1,
			npapp(find_pred (pre2),
			      [noattr_term (noattr_type (Tint (Signed,Int))) 
				(NTconstant 
				   (IntConstant (Int64.to_string s)))])))::
		   begin
		     match ty.ctype_node with
		       | Tarray (_,ty, None)->
			   error Loc.dummy_position 
			     ("array size missing in `" ^ f.var_name ^ "'")
		       | Tarray (_,ty, Some s1) ->
			 [noattr_located (
			    Cast.Ninvariant_strong 
			      ("valid_matrice" ^ n1,
			       make_forall_range 
				 Loc.dummy_position 
				 (var_to_term Loc.dummy_position f) s 
				 (fun t i -> predicate_for f.var_name 
				     (noattr_term (noattr_type (Tpointer (Not_valid,ty))) 
					(NTbinop (t,Badd,i))))))]
		       | _ -> []
		   end
		   
	     | _ -> []
	 end @ acc
      )		 
      fl l2
    in
    (separation_intern s) @ l2
  in
  let l = (fold_all_struct_pairs separation_2_struct l) in
  Cenv.fold_all_struct f l


(* Type predicates 
  
   For each structure "struct S" we introduce a predicate is_struct_S
   and its definition (as an axiom)
 *)

open Cast

let pand p1 p2 = match p1.pred_node, p2.pred_node with
  | Ptrue, _ -> p2
  | _, Ptrue -> p1
  | _ -> { p1 with pred_node = Pand (p1, p2) }

let pimp p1 p2 = match p1.pred_node, p2.pred_node with
  | Ptrue, _ -> p2
  | _, Ptrue -> p2
  | _ -> { p1 with pred_node = Pimplies (p1, p2) }

let pforall q p = match p.pred_node with
  | Ptrue -> { p with pred_node = Ptrue }
  | _ -> { p with pred_node = Pforall (q, p) }

let tterm d t = { term_node = d; term_type = t; term_loc = Loc.dummy_position }
let dummy_pred p = { pred_node = p; pred_loc = Loc.dummy_position }
let prel (t1, r, t2) = dummy_pred (Prel (t1, r, t2))
let piff (p1, p2) = dummy_pred (Piff (p1, p2))
let pvalid t = dummy_pred (Pvalid t)
let pvalid_range (t,i,j) = dummy_pred (Pvalid_range (t,i,j))
let pfresh t = dummy_pred (Pfresh t)
let ptrue = dummy_pred Ptrue
let papp (p, l) = dummy_pred (Papp (p, l))

let var_i = Info.default_var_info "i"
let tconstant n = tterm (Tconstant (IntConstant n)) c_int
let tzero = tconstant "0"

let rec pred_for_type ty t = match ty.Ctypes.ctype_node with
  | Ctypes.Tstruct n ->
      let _,info = Cenv.find_pred ("is_struct_" ^ n) in papp (info, [t])
  | Ctypes.Tint si when Coptions.int_overflow_check ->
      ptrue (*TODO*)
  | Ctypes.Tarray (_, ty', Some s) ->
      let tvar_i = tterm (Tvar var_i) c_int in
      let n = tconstant (Int64.to_string (Int64.pred s)) in
      let t_i = tterm (Tbinop (t, Clogic.Badd, tvar_i)) ty in
      let star_t_i = tterm (Tunop (Clogic.Ustar, t_i)) ty' in
      pand (pvalid_range (t, tzero, n))
	   (pforall [c_int,var_i] 
	      (pimp (pand (prel (tzero, Le, tvar_i)) (prel (tvar_i, Le, n)))
		 (pred_for_type ty' star_t_i)))
  | Ctypes.Tpointer (_, ty') | Ctypes.Tarray (_, ty', None) ->
      let t_i = tterm (Tbinop (t, Clogic.Badd, tterm (Tvar var_i) c_int)) ty in
      let star_t_i = tterm (Tunop (Clogic.Ustar, t_i)) ty' in
      pforall [c_int,var_i] (pimp (pvalid t_i) (pred_for_type ty' star_t_i))
  | Ctypes.Tunion n ->
      ptrue (*TODO*)
  | Ctypes.Tenum n ->
      ptrue (*TODO*)
  | Ctypes.Tvoid | Ctypes.Tfun _ | Ctypes.Tfloat _ | Ctypes.Tvar _ 
  | Ctypes.Tint _ -> 
      ptrue

let add_typing_predicates dl =
  let loc = Loc.dummy_position in
  let tdecl d = { node = d; loc = loc } in
  (* 1. declare all is_struct_S predicates *)
  let declare_is_struct s (tyn,fl) acc = 
    let ty = noattr tyn in
    let n = "is_struct_" ^ s in
    let is_struct_s = Info.default_logic_info n in
    Cenv.add_pred n ([ty], is_struct_s);
    let x = Info.default_var_info "x" in
    set_formal_param x;
    set_var_type (Var_info x) ty true;
    is_struct_s.logic_args <- [x];
    let varx = tterm (Tvar x) ty in
    let reads = (* reads = x.f1, ..., x.fn *)
      List.map (fun f -> tterm (Tdot (varx, f)) f.var_type) fl
    in
    let d = tdecl (Tlogic (is_struct_s, Predicate_reads ([x,ty], reads))) in
    d :: acc
  in
  (* 2. axiomatize all is_struct_S predicates *)
  let define_is_struct s (tyn,fl) acc =
    let _,is_struct_s = Cenv.find_pred ("is_struct_" ^ s) in
    let x = match is_struct_s.logic_args with [x] -> x | _ -> assert false in
    let ty = noattr tyn in
    let varx = tterm (Tvar x) ty in
    let ax = 
      let def = 
	List.fold_left
	  (fun acc f -> 
	     let t = tterm (Tdot (varx, f)) f.var_type in
	     pand acc (pred_for_type f.var_type t))
	  ptrue fl
      in
      let p = pforall [ty,x] (piff (papp (is_struct_s, [varx]), def)) in
      tdecl (Taxiom ("is_struct_" ^ s ^ "_def", p)) 
    in
    ax :: acc
  in
  (* 3. add typing predicates for global variables *)
  (**
  let add_invariant_for_global d acc = match d.node with
    | Tdecl (ty, x, _) ->
	let inv = 
	  tdecl (Tinvariant_strong ("typing_predicate_for_" ^ x.var_name,
				    pred_for_type ty (tterm (Tvar x) ty)))
	in
	d :: inv :: acc
    | _ -> 
	d :: acc
  in
  **)
  let dl = Cenv.fold_all_struct declare_is_struct dl in
  let dl = Cenv.fold_all_struct define_is_struct dl in
  (*let dl = List.fold_right add_invariant_for_global dl [] in*)
  dl
