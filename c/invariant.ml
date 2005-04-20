open Creport
open Info
open Ctypes
open Clogic
open Cenv
open Cnorm
open Cprint

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
     
let rec separation_intern2  n1 v1 =
  match v1.nterm_type.Ctypes.ctype_node with
    | Tarray (_,None) -> 
	error Loc.dummy ("array size missing in `" ^ n1 ^ "'")
    | Tarray(ty,Some s) ->
	  begin
	    match ty.Ctypes.ctype_node with
	      | Tarray (_,None) -> 
		error Loc.dummy ("array size missing in `" ^ n1 
				 ^ "[i]'")
	      | Tstruct _ ->
		  (make_forall_range Loc.dummy v1 s 
		     (fun t1 i1 ->
			make_forall_range Loc.dummy v1 s
			  (fun t2 i2 -> 
			     if i1 = nzero && i2 = nzero then NPtrue 
			     else
			       make_implies (NPrel (i1, Neq, i2)) 
				 (not_alias Loc.dummy t1 t2))))
	      | Tarray (_,_)->  
		  make_and
		    (make_forall_range Loc.dummy v1 s 
		       (fun t1 i1 ->
			  make_forall_range Loc.dummy v1 s
			    (fun t2 i2 -> 
			       if i1 = nzero && i2 = nzero then NPtrue 
			       else
				 make_implies (NPrel (i1, Neq, i2)) 
				   (not_alias Loc.dummy t1 t2))))
		    (make_forall_range Loc.dummy v1 s 
		       (fun t i -> 
			  separation_intern2 n1 
			    (noattr_term ty t.nterm_node)))    
	      | _ -> NPtrue
	  end
    | _ -> 
	NPtrue

let rec separation loc n1 v1 n2 v2 =
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

  
let rec fold_2 f l = 
  match l with 
    | v::l ->
	List.fold_left (fun acc x ->(f v x)@acc) (fold_2 f l) l
    | _ -> [] 
(*
let create_term n =
  let v = (default_var_info n) in
  set_var_type (Var_info v) (pointer memory);
  set_static v;
  (var_to_term Loc.dummy v)
*)
let noattr_located n =  
  { Cast.node = n; Cast.loc = Loc.dummy }


let separation_first mark v1 v2 =
  let sep = if mark then "%separation1" else "%separation2" in
  let n1 =  v1.var_unique_name in
  let n2 =  v2.var_unique_name in
  match v1.var_type.Ctypes.ctype_node,v2.var_type.Ctypes.ctype_node with
    | Tarray (_,None), _  ->
	error Loc.dummy ("array size missing in `" ^ n1 ^ "[i]'") 
    | _ , Tarray (_,None) ->
	error Loc.dummy ("array size missing in `" ^ n2 ^ "[i]'") 
    | Tstruct _ , Tstruct _ ->
	let pre = sep ^ n1 ^ "_" ^ n2 in
	let info = Info.default_logic_info (pre) in
	info.logic_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	Cenv.add_pred (pre)  ([], info);
	[noattr_located (
	   Cast.Ninvariant_strong (
	     "separation" ^ n1 ^ "_" ^ n2 , 
	     NPapp(find_pred (pre), 
		   (*(create_term n1)::[(create_term n2)]*) [])))]
    | Tarray (ty,Some s) , Tstruct _ -> 
	if compatible_type ty v2.var_type then
	  let pre = sep ^ "_range1_" ^ n1 ^ "_" ^ n2 in 
	  let info = Info.default_logic_info (pre) in
	  info.logic_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  [noattr_located 
	     (Cast.Ninvariant_strong (
		"separation_" ^ n1 ^ "_" ^ n2,
		NPapp
		  (find_pred (pre ), 
		   (*(create_term n1)::
		     (create_term n2)::*)
		     [noattr_term 
			(noattr_type (Tint (Signed,Int)))
			(NTconstant (IntConstant 
				       (Int64.to_string s)))])))]
	else []
    | Tstruct _ ,Tarray (ty,Some s)  -> 
	if compatible_type ty v1.var_type then
	  let pre = sep ^ "_range1_" ^ n1 ^ "_" ^ n2 in 
	  let info = Info.default_logic_info (pre) in
	  info.logic_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  [noattr_located
	     (Cast.Ninvariant_strong (
		"separation_" ^ n1 ^ "_" ^ n2,
		NPapp(
		  find_pred (pre), 
		  (*(create_term n2)::(create_term n1)::*)
		    [noattr_term 
		       (noattr_type (Tint (Signed,Int)))
		       (NTconstant (IntConstant 
				      ((Int64.to_string s))))])))]
	else []
    | Tarray (ty1, Some s1),  Tarray(ty2, Some s2) ->
	
	let make_sub_term p ty v = noattr_term ty (NTarrow (p,v)) in
	if mark then
	  let pre = sep ^ n1 ^ "_" ^ n2 in
	  let info = Info.default_logic_info (pre) in
	  info.logic_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  let ty = noattr_type (Tpointer (noattr_type (Tvoid))) in
	  let var = default_var_info (fresh_index()) in
	  let term = noattr_term ty (NTvar var) in
	  noattr_located (
	    Cast.Ninvariant_strong (
	      "separation" ^ n1 ^ "_" ^ n2 , 
	      NPapp(find_pred (pre),[])))::
	    [noattr_located
	       (Cast.Ninvariant_strong (
		  "separation_" ^ n1 ^ "_" ^ n2,
		  make_forall 
		    [ty,var] 
		    (separation Loc.dummy n1 
		       (make_sub_term term v1.var_type v1) n2
		       (make_sub_term term v2.var_type v2))))]
	else
 	  let pre = sep ^ n1 ^ "_" ^ n2 in
	  let info = Info.default_logic_info (pre) in
	  info.logic_args <- HeapVarSet.add v1 (HeapVarSet.singleton v2); 
	  Cenv.add_pred (pre)  ([], info);
	  let ty = noattr_type (Tpointer (noattr_type (Tvoid))) in
	  let var1 = default_var_info (fresh_index()) in
	  let var2 = default_var_info (fresh_index()) in
	  let term1 = noattr_term ty (NTvar var1) in
	  let term2 = noattr_term ty (NTvar var2) in
	  noattr_located (
	    Cast.Ninvariant_strong (
	      "separation" ^ n1 ^ "_" ^ n2 , 
	      NPapp(find_pred (pre),[])))::
	    [noattr_located
	       (Cast.Ninvariant_strong 
		  ("separation_" ^ n1 ^ "_" ^ n2,
		   make_forall 
		     [ty,var1]
		     (make_forall 
			[ty,var2]
			(separation Loc.dummy n1 
			   (make_sub_term term1 v1.var_type 
			      v1)
			   n2 
			   (make_sub_term term2 v2.var_type 
			      v2)))))]
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
      | Tarray (_,None) -> 
	  error Loc.dummy ("array size missing in `" 
			       ^ n1 ^ "[i]'")
      | Tarray (ty,Some s) ->
	  begin
	    match ty.Ctypes.ctype_node with
	      | Tstruct _ -> 
		  let pre = "%separation1_range_" ^ n1  in 
		  let info = Info.default_logic_info (pre) in
		  info.logic_args <- HeapVarSet.singleton v1 ; 
		  Cenv.add_pred (pre)  ([], info);
		  [noattr_located (Cast.Ninvariant_strong (
				    "internal_separation_" ^ n1 ^ "_array1" , 
				   NPapp(
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
		 info.logic_args <- HeapVarSet.singleton v1 ; 
		 Cenv.add_pred (pre)  ([], info);
		 noattr_located (Cast.Ninvariant_strong (
				   "internal_separation_" ^ n1 ^ "_array1" , 
				   NPapp(
				     find_pred (pre ),
				     (*(create_term n1)::*)
				      [noattr_term (noattr_type 
						      (Tint (Signed,Int))) 
					 (NTconstant 
					    (IntConstant 
					       (Int64.to_string s)))])))::
		   noattr_located (Cast.Ninvariant_strong (
				     "internal_separation_" ^ n1 ^ "_array2",
				     (make_forall_range Loc.dummy 
					(var_to_term Loc.dummy v1) s 
					(fun t i -> 
					    separation_intern2 n1 
					      (noattr_term 
						 (noattr_type (Tpointer ty)) 
						 (NTbinop (t,Badd,i)))))))::[]
	      | _ -> []
	  end
      | _ -> []
  in
  (List.fold_left (fun acc t ->
     array_intern_separation t@acc) [] l) @ 
    (fold_2 (separation_first true) l)  


let separation_2_struct s1 l1 s2 l2 acc=
  let l1 = snd l1 in
  let l2 = snd l2 in
  List.fold_left (fun acc1 t1 ->
		    (List.fold_left
		       (fun acc2 t2 ->
			  separation_first false t1 t2@acc2) acc1 l2)) 
    acc l1

let add_predicates l =
  let f s (ty,fl) l2 = 
    let l2 = List.fold_right 
      (fun f acc -> 
	 begin
	   match f.var_type.Ctypes.ctype_node with
	     | Tstruct n ->
		 let pre = "%valid1" ^ n  in 
		 let info = Info.default_logic_info (pre) in
		 info.logic_args <- HeapVarSet.singleton f; 
		 Cenv.add_pred (pre)  ([], info);
		 [noattr_located (
		    Cast.Ninvariant_strong (
		      "valid" ^ n,NPapp(find_pred (pre),[])))]
	     | Tarray(ty, Some s)->
		 let n1 = f.var_unique_name in
		 let pre = "%valid1_" ^ n1 in 
		 let info = Info.default_logic_info (pre) in
		 info.logic_args <- HeapVarSet.singleton f; 
		 Cenv.add_pred (pre)  ([], info);
		 let pre2 = "%valid1_range_" ^ n1  in 
		 let info2 = Info.default_logic_info (pre2) in
		 info2.logic_args <- HeapVarSet.singleton f; 
		 Cenv.add_pred (pre2)  ([], info2);
		 noattr_located (
		 Cast.Ninvariant_strong ("valid_array"^ n1,
					 NPapp(find_pred (pre),[])))::
		   noattr_located (
		     Cast.Ninvariant_strong 
		       ("valid_range" ^ n1,
			NPapp(find_pred (pre2),
			      [noattr_term (noattr_type (Tint (Signed,Int))) 
				(NTconstant 
				   (IntConstant (Int64.to_string s)))])))::
		   begin
		     match ty.ctype_node with
		       | Tarray (ty, None)->
			   error Loc.dummy 
			     ("array size missing in `" ^ f.var_name ^ "'")
		       | Tarray (ty, Some s1) ->
			 [noattr_located (
			    Cast.Ninvariant_strong 
			      ("valid_matrice" ^ n1,
			       make_forall_range 
				 Loc.dummy (var_to_term Loc.dummy f) s 
				 (fun t i -> predicate_for f.var_name 
				     (noattr_term (noattr_type (Tpointer ty)) 
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
(*
    try 
  let info2 = find_pred ("internal_separation_" ^ s) in 	    
      let info =Info.default_logic_info 
	("internal_separation_" ^ s ^ "_bis") in
      let l2 = noattr_located 
	(Cast.Nlogic 
	   (info, NPredicate_def 
	      ([],NPforall 
		 ([ty,st], 
		  NPimplies (NPvalid t, (NPapp (info2, [t]))))))) :: 
	noattr_located (Cast.Ninvariant ( 
			  ("internal_separation_" ^ s ^ "_invariant"),
			  (NPapp (info, []))))
	::l2 in 
      Cenv.fold_all_struct (separation s ty) l2
    with Not_found -> Cenv.fold_all_struct (separation s ty) l2

  in*)

  (fold_all_struct_pairs separation_2_struct l)@Cenv.fold_all_struct f l
