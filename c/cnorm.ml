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

(*i $Id: cnorm.ml,v 1.14 2005-01-06 16:10:31 hubert Exp $ i*)

open Creport
open Cconst
open Info
open Cenv
open Cltyping
open Ctypes
open Cast
open Clogic
open Int64



let noption f o =
  match o with
    | None -> None
    | Some x -> Some (f x)

let rec ctype (t : tctype) : nctype =
  let nctype =
    match t.Ctypes.ctype_node with
      | Tvoid -> Tvoid
      | Tint (sign ,i) -> Tint (sign , (*cinteger *)i) 
      | Tfloat cfloat -> Tfloat cfloat
      | Ctypes.Tvar string -> Ctypes.Tvar string
      | Tarray (t,op) -> Tarray(ctype t,op) 
      | Tpointer t -> Tpointer (ctype t)
      | Tstruct ( string ) ->Tstruct (string)
	  (*match l with 
	     | Tag -> Tstruct (string,Tag)
	     | Decl l ->
		 Tstruct ( 
		   string,
		   Decl (
		     (List.map (fun (t,s,op) -> (ctype t,s,noption eval_const_expr op))) 
		     l))*) 
      | Tunion (string)-> Tunion (string)
	  (*match l with 
	    | Tag -> Tunion (string,Tag)
	    | Decl l ->
		Tunion ( 
		  string,
		  Decl (
		    (List.map (fun (t,s,op) -> (ctype t,s,noption eval_const_expr op))) 
			  l))*)
      | Tfun (l ,c)-> Tfun (List.map (fun (t,s) -> (ctype t,s)) l, ctype c)
      | Tenum (string) ->Tenum string
	  (*match l with 
	    | Tag -> Tenum (string,Tag)
	    | Decl l -> 
		Tenum 
		  (string,
		   Decl (List.map 
			   (fun(s,op) -> 
			      (s,noption eval_const_expr op)) l))*)
(*
      let _ = 
	List.fold_left 
	  (fun n (f,op) -> 
	     let i = default_var_info f in
	     let n' = match op with
	       | None -> n
	       | Some e -> eval_const_expr e 
	     in
	     set_const_value i n'; 
	     ignore (add_sym loc f ty (Var_info i)); 
	     Int64.add n' Int64.one) 
	  Int64.zero fl
      in
*)

  in
  { 
    Ctypes.ctype_node = nctype;
    ctype_storage = t.Ctypes.ctype_storage;
    ctype_const = t.Ctypes.ctype_const;
    ctype_volatile = t.Ctypes.ctype_volatile;
  }

let var_requires_indirection v =
  v.var_is_referenced && 
  (match v.var_type.Ctypes.ctype_node with
     | Tstruct _ | Tunion _ -> false
     | _ -> true)

let var_is_referenced_or_struct_or_union v =
  v.var_is_referenced || 
  (match v.var_type.Ctypes.ctype_node with
     | Tstruct _ | Tunion _ -> true
     | _ -> false)

open Cast

let ne_arrow e f =
  match e.nexpr_node with
    | NEstar(x) -> NEarrow (x, f)
    | _ -> NEarrow (e, f)

let ne_star loc ty e =
  NEstar
    {nexpr_node = e;
     nexpr_type = noattr (Tpointer ty);
     nexpr_loc = loc}


let rec expr t =
  let ty = ctype t.texpr_type in
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
		if var_requires_indirection v then
		  ne_star loc ty t'
		else t'
	    | Fun_info _  -> NEvar env_info)
      | TEdot (lvalue,var_info) -> 
	  let t' = ne_arrow (expr lvalue) var_info in
	  if var_requires_indirection var_info then
	    ne_star loc ty t'
	  else t'
      | TEarrow (lvalue ,var_info) -> 
	  let t' = NEarrow ((expr lvalue), var_info) in
	  if var_requires_indirection var_info then
	    ne_star loc ty t'
	  else t'
      | TEarrget (lvalue,texpr) -> 
	  (* t[e] -> *(t+e) *)
	  NEstar(
	    {
	      nexpr_node =NEbinary(expr lvalue, Badd_pointer_int, expr texpr);
	      nexpr_type = noattr (Tpointer ty);
	      nexpr_loc = loc;
	    })
      | TEseq (texpr1,texpr2) -> NEseq ((expr texpr1) , (expr texpr2))
      | TEassign (lvalue ,texpr) -> 
	  NEassign ((expr lvalue) , (expr texpr))
      | TEassign_op (lvalue ,binary_operator, texpr) ->
	  NEassign_op ((expr lvalue),binary_operator , (expr texpr))
      | TEunary (Ustar ,texpr) ->  NEstar(expr texpr)
      | TEunary (Uamp ,texpr) ->
	  (match texpr.texpr_node with
	     | TEvar v -> NEvar v
	     | TEunary (Ustar, texpr)-> expr_node loc ty texpr.texpr_node
	     | TEdot(lvalue,var_info)->
		 ne_arrow (expr lvalue) var_info
	     | TEarrow(lvalue,var_info) -> 
		 NEarrow (expr lvalue, var_info)
	     | _ -> 
		 warning loc "this & cannot be normalized";
		 NEunary (Uamp,expr texpr))
      | TEunary (unary_operator ,texpr) ->
	  NEunary(unary_operator, expr texpr)
      | TEincr (incr_operator,texpr) -> NEincr(incr_operator, expr texpr)
      | TEbinary (texpr1 , binary_operator , texpr2) ->
	  NEbinary ((expr texpr1), binary_operator , (expr texpr2))
      | TEcall (texpr ,list) -> NEcall ((expr texpr),
				       (List.map (fun x -> (expr x)) list))
      | TEcond (texpr1, texpr2, texpr3) -> NEcond ((expr texpr1),
						   (expr texpr2),
						   (expr texpr3))
      | TEsizeof (tctype,n) ->
	  NEconstant (IntConstant (Int64.to_string n))
      | TEcast (tctype ,texpr) -> NEcast (ctype tctype, expr texpr)
  
let nt_arrow t f =
  match t.nterm_node with
    | NTstar(x) -> NTarrow (x, f)
    | _ -> NTarrow (t, f)

let nt_star loc ty t =
  NTstar { nterm_node = t;
	   nterm_loc = loc;
	   nterm_type = ty}
      
let rec term_node loc t =
  match t with
  | Tconstant constant -> NTconstant constant
  | Tvar var_info -> 
      let t' = NTvar var_info in
      if var_requires_indirection var_info then
	nt_star loc var_info.var_type t'
      else
	t'
  | Tapp (logic_info ,l) -> NTapp (
      logic_info, 
      List.map (fun x -> (term x)) l)
  | Tunop (Clogic.Uamp,t) -> 
      begin match t.term_node with
	| Tvar v-> NTvar v
	| Tunop(Clogic.Ustar, t) -> term_node loc t.term_node
	| Tarrow(t,f) -> NTarrow (term t, f) 
	| Tdot(t,f) -> nt_arrow (term t) f
	| _ -> 
	    unsupported loc "cannot handle this & operator"
	    (* NTunop(Clogic.Uamp,term t)    *)
      end
  | Tunop (Clogic.Ustar,t) -> NTstar (term t)
  | Tunop (unop,t) -> NTunop(unop,term t)
  | Tbinop (t1, binop, t2) -> NTbinop (term t1, binop, term t2)
  | Tdot (t, var_info) ->  
      let t' = nt_arrow (term t) var_info in
      if var_requires_indirection var_info then
	nt_star loc var_info.var_type t'
      else
	t'
  | Tarrow (t, var_info) -> 
      let t' = NTarrow (term t, var_info) in
      if var_requires_indirection var_info then
	nt_star loc var_info.var_type t'
      else
	t'
  | Tarrget (t1, t2) -> 
      let t1 = term t1 and t2 = term t2 in
      NTstar { nterm_node = NTbinop(t1, Clogic.Badd, t2);
	       nterm_loc = loc;
	       nterm_type = t1.nterm_type }
  | Tif (t1, t2, t3) -> NTif (term t1, term t2 , term t3)
  | Told t1 -> NTold (term t1)
  | Tat (t1, s) -> NTat (term t1, s)
  | Tbase_addr t -> NTbase_addr (term t)
  | Tblock_length t -> NTblock_length (term t)
  | Tresult -> NTresult
  | Tnull -> NTnull
  | Tcast (ty, t) -> NTcast (ctype ty, term t)


and term t = 
{ 
  nterm_node = term_node t.term_loc t.term_node;
  nterm_loc = t.term_loc;
  nterm_type = t.term_type;
}

let nlocation l =
  match l with
    | Lterm(t) -> Lterm(term t)
    | Lstar(t) -> Lstar(term t)
    | Lrange(t1,t2,t3) -> Lrange(term t1,term t2,term t3)
	
let nvariant v =
  match v with (t, sopt) -> (term t,sopt)

	
let rec predicate p = 
  match p with
    | Pfalse -> NPfalse
    | Ptrue -> NPtrue 
    | Papp (info,l) -> NPapp (info, List.map term l)
    | Prel (t1 , relation , t2) -> NPrel (term t1,relation,term t2)
    | Pand (p1, p2) -> NPand (predicate p1, predicate p2)
    | Por (p1, p2) -> NPor (predicate p1, predicate p2)
    | Pimplies (p1, p2) -> NPimplies (predicate p1, predicate p2)
    | Piff (p1, p2) -> NPiff (predicate p1, predicate p2)
    | Pnot p1 -> NPnot (predicate p1)
    | Pif (t,p1,p2) -> NPif (term t,predicate p1 ,predicate p2)
    | Pforall (typed_quantifiers, p) -> NPforall (
	(List.map (fun (x,y) -> ((ctype x),y)) typed_quantifiers),
	(predicate p))
    | Pexists (typed_quantifiers, p) -> NPexists (
	(List.map (fun (x,y) -> ((ctype x),y)) typed_quantifiers),
	(predicate p)) 
    | Pold p -> NPold (predicate p)
    | Pat (p, s) -> NPat ((predicate p),s)
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
	NPredicate_reads(List.map (fun (v,t) -> (v,ctype t)) param_list,
			List.map nlocation loc_list)
    | Predicate_def  (param_list , p ) ->
	NPredicate_def(List.map (fun (v,t) -> (v,ctype t)) param_list,
		      predicate p)
    | Function (l1 , c , l2) -> NFunction (
	List.map (fun (var,c) -> (var,ctype c)) l1,
	ctype c,
	List.map nlocation l2)

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

let spec s = 
{ 
  requires = noption predicate s.requires;
  assigns  = noption (List.map (fun x -> nlocation x)) s.assigns;
  ensures = noption predicate s.ensures;
  decreases = noption variant s.decreases;
}

let in_struct v1 v = 
  let x = begin
    match v1.texpr_node with
    | TEunary (Ustar, x)-> TEarrow (x, v)
    | _ -> TEarrow (v1, v)
  end in
  { texpr_node = x; 
    texpr_loc = v1.texpr_loc;
    texpr_type = v.var_type }

let noattr loc ty e =
  { texpr_node = e;
    texpr_type = ty;
    texpr_loc  = loc
  }

let noattr2 loc ty e =
  { nexpr_node = e;
    nexpr_type = ty;
    nexpr_loc  = loc
  }

let noattr3 tyn = { Ctypes.ctype_node = tyn; 
		   Ctypes.ctype_storage = No_storage;
		   Ctypes.ctype_const = false;
		   Ctypes.ctype_volatile = false }

let alloca loc n =
  {nexpr_node = NEcall ((noattr2  loc 
			   (noattr3(
			      Tfun ([(noattr3
					(Tint(Signed,Ctypes.Int)),"n")], 
				    noattr3 (Tpointer (noattr3 Tvoid))))) 
			   (NEvar  (Fun_info (default_fun_info "alloca")))), 
			[{ nexpr_node = NEconstant  (IntConstant n);
			   nexpr_type = { Ctypes.ctype_node =  
					    Tint (Signed,Ctypes.Int);
					  Ctypes.ctype_storage = No_storage;
					  Ctypes.ctype_const = false;
					  Ctypes.ctype_volatile = false;
					};
			   nexpr_loc  = loc }]);
   nexpr_type = noattr3 (Tpointer (noattr3 Tvoid));
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
	[{nst_node = NSexpr (noattr2 loc t (NEassign((expr lvalue),(expr x))));
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
		       (in_struct lvalue f) init
		   in (acc@block,init'))
		([],initializers)  fl
	      in
	      (
		(*{nst_node = NSexpr (noattr2 loc t (NEassign
						     ((expr lvalue),
						      (alloca loc "1"))));
		 nst_break = false;    
		 nst_continue = false; 
		 nst_return = false;   
		 nst_term = true;
		 nst_loc = loc     
		}::*)l1,l2)
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
	     (* {nst_node = NSexpr (noattr2 loc t 
				    (NEassign((expr lvalue),(alloca loc "1"))));
	       nst_break = false;    
	       nst_continue = false; 
	       nst_return = false;   
	       nst_term = true;
	       nst_loc = loc     
	      }::*)block,init'
	  | _ ->
	      assert false
	end
(*
    | Tarray (ty,None) -> 
	let i = ref 0 in
	let block = ref [] in
	while (initializers != []) do
	  let b,initializers =  
	    init_expr tyf (TEarrget(lvalue,i)) initializers in
	  i := !i + 1;
	  block := block@b
	done;
	(block,[])
*)
    | Tarray (ty,Some t) ->
	let rec init_cells i (block,init) =
	  if i >= t then (block,init)
	  else
	    let ts = Ctyping.int_teconstant (Int64.to_string i) in
	    let (b,init') = 
	      init_expr loc ty (noattr loc ty (TEarrget(lvalue,ts))) init 
	    in
	    init_cells (Int64.add i Int64.one) (block@b,init')
	in
	let l1 , l2 = init_cells Int64.zero ([],initializers) in
(*	{nst_node = NSexpr (noattr2 loc ty 
			      (NEassign((expr lvalue),
					(alloca loc (Int64.to_string t)))));
	 nst_break = false;    
	 nst_continue = false; 
	 nst_return = false;   
	 nst_term = true;
	 nst_loc = loc     
	}::*)l1,l2
    | Tarray (ty,None) -> assert false
    | Tfun (_, _) -> assert false
    | Ctypes.Tvar _ -> assert false
    | Tvoid -> assert false

and nlocated s l l2 = 
  match l with 
    | [] -> NSblock l2
    | {node = Tdecl (t,v,init); loc = l}::decl -> 
	if var_is_referenced_or_struct_or_union v
	then
	  set_var_type (Var_info v) (c_array_size v.var_type Int64.one);
	begin match init with
	  | None ->
	      let declar = nlocated s decl l2 in
	      NSdecl(v.var_type,v,None,copyattr s declar)
	  | Some c ->
	      match v.var_type.Ctypes.ctype_node with
		| Tenum _ | Tint _ | Tfloat _ | Tpointer _ -> 
		    let declar = nlocated s decl l2 in
		    begin match c with
		      | Iexpr e ->
			  NSdecl(v.var_type,v,Some (Iexpr (expr e)),
				 copyattr s declar)
		      | _ -> assert false
		    end
		| Tarray (_,Some length) -> 
		    let lvalue = (noattr l v.var_type (TEvar (Var_info v))) in
		    let declar,_ = 
		      init_expr l v.var_type 
			lvalue [c] 
		    in
		     NSdecl(v.var_type,v,
			    Some (Iexpr (alloca l (Int64.to_string length))),
			   copyattr s (nlocated s decl (declar@l2)))
(*		    NSdecl(v.var_type,v,None,
			   copyattr s (nlocated s decl (declar@l2)))*)
		| Tarray _ | Tstruct _ | Tunion _ -> 
		    let lvalue = (noattr l v.var_type (TEvar (Var_info v))) in
		    let declar,_ = 
		      init_expr l v.var_type 
			lvalue [c] 
		    in
		     NSdecl(v.var_type,v,
			    Some (Iexpr (alloca l "1")),
			   copyattr s (nlocated s decl (declar@l2)))
		| Tvoid | Ctypes.Tvar _ | Tfun _ -> assert false		      
	end
    | _  -> assert false

let rec expr_of_term (t : nterm) : nexpr = 
 {
  nexpr_node = 
    begin
      match t.nterm_node with 
	| NTconstant c ->  NEconstant c
	| NTvar v -> NEvar (Var_info v)
	| NTapp (i,l) -> error t.nterm_loc 
	      "logic function can't be used with ghost variables"
	| NTunop (t , term) -> NEunary(
	    begin  match t with 
	      | Clogic.Uminus -> Uminus 
	      | Clogic.Utilde -> Utilde 
	      | Clogic.Ustar -> assert false
	      | Clogic.Uamp -> assert false
	      | Clogic.Ufloat_of_int -> Ufloat_of_int
	      | Clogic.Uint_of_float -> Uint_of_float
	    end,
	    (expr_of_term term))
	      
	| NTstar t ->  NEstar (expr_of_term t)
	| NTbinop (t1, b, t2) -> NEbinary 
	      ((expr_of_term t1),
	       begin match b with
		 | Clogic.Badd -> Badd
		 | Clogic.Bsub -> Bsub
		 | Clogic.Bmul -> Bmul 
		 | Clogic.Bdiv -> Bdiv
		 | Clogic.Bmod -> Bmod
	       end,
	       (expr_of_term t2))
	      
	| NTarrow (t,v) -> NEarrow (expr_of_term t,v)
	| NTif (t1,t2,t3)-> NEcond 
	      (expr_of_term t1,expr_of_term t2,expr_of_term t3)
	| NTold t -> error t.nterm_loc 
	      "old can't be used with ghost variables"
	| NTat (t , s)-> error t.nterm_loc 
	      "@ can't be used with ghost variables"
	| NTbase_addr t -> error t.nterm_loc 
	      "base_addr can't be used with ghost variables"
	| NTblock_length t -> error t.nterm_loc 
	      "block_length can't be used with ghost variables"
	| NTresult -> error t.nterm_loc 
	      "result can't be used with ghost variables"
	| NTnull -> NEconstant (IntConstant "0")
	| NTcast (ty,t) -> NEcast(ty,expr_of_term t)
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
      nlocated s l1 (List.map statement l2)
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
  | TSset (x, t) -> NSexpr (noattr2 s.st_loc x.var_type 
			      (NEassign (noattr2 s.st_loc x.var_type 
					   (NEvar (Var_info x)),
			      (expr_of_term (term t)))))
  in
  { nst_node = nst;
    nst_break = s.st_break;
    nst_continue = s.st_continue;
    nst_return =  s.st_return;
    nst_term = s.st_term;
    nst_loc = s.st_loc;
  }
(*and decl e1=
  match e1 with    
  | Tlogic(info, l) -> Nlogic (info , logic_symbol l)
  | Taxiom (s, p) -> Naxiom (s, predicate p)
  | Tinvariant(s, p) -> Ninvariant (s, predicate p)
  | Ttypedef (t, s) -> Ntypedef((ctype t),s)
  | Ttypedecl t -> Ntypedecl (ctype t)
  | Tdecl (t, v, c) -> 
(* traitement des locales precedemment dans cinterp a rebrancher 
   if v.var_is_referenced then
   let t = { nterm_node = NTresult; 
   nterm_loc = d.loc;
   nterm_type = Ctypes.c_pointer ctype } in
   Let(v.var_unique_name, alloc_on_stack d.loc v t, acc)
   else
*)
      let decl =
	if var_is_referenced_or_struct_or_union v
	then
	  begin
	    set_var_type (Var_info v) (c_array_size v.var_type Int64.one);
	    Tdecl(v.var_type,v,ilist ((*c_initializer_option*) c))
	  end
	else Tdecl(t,v,(*c_initializer_option*) c)
      in 
      nlocated decl
  | Tfunspec (s, t, f, l) -> Nfunspec (spec s,ctype t,f,
				   (List.map (fun (x,y) -> (ctype x,y)) l))
  | Tfundef (s, t, f, l, st) -> Nfundef (spec s,ctype t,f,
				   (List.map (fun (x,y) -> (ctype x,y)) l),
				    statement st)
*)


let global_decl e1 =
  match e1 with    
  | Tlogic(info, l) -> Nlogic (info , logic_symbol l)
  | Taxiom (s, p) -> Naxiom (s, predicate p)
  | Tinvariant(s, p) -> Ninvariant (s, predicate p)
  | Ttypedef (t, s) -> Ntypedef((ctype t),s)
  | Ttypedecl t -> Ntypedecl (ctype t)
  | Tdecl (t, v, c) -> 
      let t =
	if (* not ??? *) v.var_is_assigned && Coptions.closed_program then   
	  { t with Ctypes.ctype_const = true }
	else t 
      in
      set_var_type (Var_info v) t;
      if var_is_referenced_or_struct_or_union v
      then
	begin
	  set_var_type (Var_info v) (c_array_size v.var_type Int64.one);
	  Ndecl(v.var_type,v,ilist (c_initializer_option c))
	end
      else Ndecl(t,v,c_initializer_option c)
  | Tfunspec (s, t, f, l) -> Nfunspec (spec s,ctype t,f,
				   (List.map (fun (x,y) -> (ctype x,y)) l))
  | Tfundef (s, t, f, l, st) -> Nfundef (spec s,ctype t,f,
				   (List.map (fun (x,y) -> (ctype x,y)) l),
				    statement st)
  | Tghost(x,cinit) ->
      let cinit = 
	match cinit with
	  | None -> None
	  | Some (Iexpr t) -> Some(Iexpr (expr_of_term (term t)))
	  | _ -> assert false
      in
      Ndecl(x.var_type,x,cinit)
      
      
	
let file = List.map (fun d -> { node = global_decl d.node ; loc = d.loc})


(* Automatic invariants expressing validity of local/global variables *)

let int_nconstant n = 
  { nterm_node = NTconstant (IntConstant n); 
    nterm_loc = Loc.dummy;
    nterm_type = c_int }

let nzero = int_nconstant "0"

(*
let eval_array_size e = 
  { nterm_node = NTconstant (IntConstant (Int64.to_string (eval_const_expr e))); 
    nterm_loc = e.nexpr_loc;
    nterm_type = c_int }
*)

open Clogic

let tpred t = match t.nterm_node with
  | NTconstant (IntConstant c) -> 
      let c = string_of_int (int_of_string c - 1) in
      { t with nterm_node = NTconstant (IntConstant c) }
  | _ ->
      { t with nterm_node = NTbinop (t, Bsub, int_nconstant "1") }

let make_and p1 p2 = match p1, p2 with
  | NPtrue, _ -> p2
  | _, NPtrue -> p1
  | _ -> NPand (p1, p2)

let make_implies p1 = function
  | NPtrue -> NPtrue
  | p2 -> NPimplies (p1, p2)

let make_forall q = function
  | NPtrue -> NPtrue
  | p -> NPforall (q, p)

let make_valid_range_from_0 t ts=
  if ts = Int64.one
  then
    NPvalid t
  else
    NPvalid_range (t, nzero, int_nconstant (Int64.to_string (Int64.pred ts)))


let fresh_index = 
  let r = ref (-1) in fun () -> incr r; "index_" ^ string_of_int !r


let indirection loc ty t =
  { nterm_node = NTstar t; 
    nterm_loc = loc; 	   
    nterm_type = ty}

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
		 nterm_type = c_int } in
    let ti = 
      { nterm_node = NTbinop (t, Badd, vari); 
	nterm_loc = loc;
	nterm_type = t.nterm_type }
    in
    let ineq = NPand (NPrel (nzero, Le, vari),
		      NPrel (vari, Lt, int_nconstant (Int64.to_string b))) in
    make_forall [c_int, i] (make_implies ineq (f ti vari))

let valid_for_type ?(fresh=false) loc v (t : Cast.nterm) =
  let rec valid_fields valid_for_current n (t : Cast.nterm) = 
    begin match tag_type_definition n with
      | TTStructUnion (Tstruct (_), fl) ->
	  List.fold_right 
	    (fun f acc -> 
	       let tf = 
		 { nterm_node = NTarrow (t, f); 
		   nterm_loc = loc;
		   nterm_type = ctype f.var_type } 
	       in
	       make_and acc (valid_for tf))
	    fl 
	    (if valid_for_current then 
	       if fresh then NPand(NPvalid t, NPfresh t) else NPvalid t 
	     else NPtrue)
      | TTIncomplete ->
	  error loc ("`" ^ v.var_name ^ "' has incomplete type")
      | _ ->
	  assert false
    end
  and valid_for (t : Cast.nterm) = match t.nterm_type.Ctypes.ctype_node with
    | Tstruct (n) ->
 	valid_fields true n t
    | Tarray (ty, None) ->
	error loc ("array size missing in `" ^ v.var_name ^ "'")
    | Tarray (ty, Some s) ->
	let ts = Int64.to_string s in
	let vrange = make_valid_range_from_0 t s in
	let valid_form =
	  make_and
	    vrange
	    (if fresh then NPfresh t else NPtrue)
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
	NPtrue
  in
  valid_for t

(*
open Format

let rec print_term_node fmt = function
  | Tconstant (IntConstant c | FloatConstant c) ->
      fprintf fmt "%s" c
  | Tvar v -> 
      fprintf fmt "%s" v.var_name
  | Tbinop (t1, Badd, t2) -> 
      fprintf fmt "(%a+%a)" print_term t1 print_term t2
  | Tarrow (t1, f) ->
      fprintf fmt "(%a->%s)" print_term t1 f.var_name
  | Tdot (t1, f) ->
      fprintf fmt "(%a.%s)" print_term t1 f.var_name
  | Tarrget (t1, t2) ->
      fprintf fmt "%a[%a]" print_term t1 print_term t2
  | Tresult ->
      fprintf fmt "result"
  | _ -> 
      fprintf fmt "<term>"

and print_term fmt t = print_term_node fmt t.term_node

let rec print_predicate fmt = function
  | Pforall ([_,x], p) -> 
      fprintf fmt "(forall %s, %a)" x.var_name print_predicate p
  | Pand (p1, p2) -> 
      fprintf fmt "(%a and %a)" print_predicate p1 print_predicate p2
  | Pimplies (p1, p2) ->
      fprintf fmt "(%a -> %a)" print_predicate p1 print_predicate p2
  | Prel (t1, Neq, t2) ->
      fprintf fmt "(%a <> %a)" print_term t1 print_term t2
  | Prel (t1, Le, t2) ->
      fprintf fmt "(%a <= %a)" print_term t1 print_term t2
  | Prel (t1, Lt, t2) ->
      fprintf fmt "(%a < %a)" print_term t1 print_term t2
  | Ptrue ->
      fprintf fmt "true"
  | _ -> 
      fprintf fmt "<predicate>"

let print_allocs =
  let x = default_var_info "x" in
  let varx = { term_node = Tvar x; 
	       term_loc = Loc.dummy;
	       term_type = c_pointer c_void } in
  fun fmt p -> fprintf fmt "fun x -> %a" print_predicate (p varx)
 
*)

let not_alias loc x y = 
  let ba t = { nterm_node = NTbase_addr t; 
	       nterm_loc = loc;
	       nterm_type = c_addr } in 
  NPrel (ba x, Neq, ba y)

(*
let forall_index s i ts vari pi =
    make_forall [c_int, i] 
      (make_implies 
	 (NPand (NPrel (nzero, Le, vari), NPrel (vari, Lt, ts)))
	 pi)
*)

let var_to_term loc v =
  {
    nterm_node = NTvar v; 
    nterm_loc = loc;
    nterm_type = v.var_type}

let in_struct v1 v = 
  match v1.nterm_node with
    | NTstar(x) ->
	{ nterm_node = NTarrow (x, v); 
	  nterm_loc = v1.nterm_loc;
	  nterm_type = v.var_type }
    | _ -> 
	{ nterm_node = NTarrow (v1, v); 
	  nterm_loc = v1.nterm_loc;
	  nterm_type = v.var_type }

	

(* assumes v2 is an array of objects of type ty *)
let rec tab_struct loc v1 v2 s ty n n1 n2=
  let l = begin
    match  tag_type_definition n with
      | TTStructUnion ((Tstruct _),fl) ->
	  fl
      | _ -> assert false
  end in
 (* make_and *)(List.fold_left 
	      (fun p t -> 
		 if  compatible_type t.var_type v2.nterm_type 
		 then make_and p (not_alias loc v2 (in_struct v1 t))
		 else p)
	      NPtrue l)
    (*make_forall_range loc v2 s 
       (fun t i -> 
	  local_separation loc n1 v1 (n2^"[i]") (indirection loc ty t))*)
and local_separation loc n1 v1 n2 v2 =
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
			make_and (not_alias loc v2 (in_struct v2 v)) p
		      else
			p)
		   NPtrue l1))
	   else NPtrue)
	  (List.fold_left 
	     (fun p t1 -> 
		List.fold_left 
		  (fun p t2 -> 
		     make_and p 
		       (local_separation loc n1 (in_struct v1 t1) 
			  n2 (in_struct v2 t2)))
		  p l2)
	     NPtrue l1)
    | Tstruct n , Tarray (ty,Some s) -> tab_struct loc v1 v2 s ty n n1 n2
    | Tarray (ty,Some s) , Tstruct n -> tab_struct loc v2 v1 s ty n n1 n2
    | Tarray (ty1,Some s1), Tarray(ty2,Some s2) ->
	make_and
	  (if compatible_type v1.nterm_type v2.nterm_type
	   then
	     (not_alias loc v1 v2)
	   else
	     NPtrue)
	  (make_and 
	     (make_forall_range loc v1 s1 
		(fun t i -> local_separation loc (n1^"[i]") 
		     (indirection loc ty1 t) n2 v2))
	     (make_forall_range loc v2 s2  
		(fun t i -> local_separation loc n1 v1 (n2^"[j]") 
		     (indirection loc ty2 t))))
    | _, _ -> NPtrue

    
let rec separation_intern loc v1 =
  let rec local_separation_intern loc n1 v1 =
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
			  local_separation_intern loc (n1^"[i]") 
			    (indirection loc ty t)))

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
	      | (v::l) -> make_and
		    (make_and 
		    (local_separation_intern loc v.var_name 
		       (var_to_term loc v))
		    (List.fold_left 
		       (fun acc x -> 
			  make_and acc (local_separation loc 
					  v.var_name (in_struct v1 v) 
					  x.var_name (in_struct v1 x))) 
		       NPtrue l))
		    (f l)
	      | [] -> NPtrue
	  in
	  f l
      | _ -> NPtrue
  in
  local_separation_intern loc v1.var_name (var_to_term loc v1) 
	  
	
let separation loc v1 v2 =
  local_separation loc v1.var_name (var_to_term loc v1) 
    v2.var_name (var_to_term loc v2)

(*
let separation loc v ?(allocs=(fun n x -> [])) (t : Cast.nterm) =
  let not_alias x y = 
    let ba t = { nterm_node = NTbase_addr t; 
		 nterm_loc = loc;
		 nterm_type = c_addr } in 
    NPrel (ba x, Neq, ba y)
  in
(*
[local_alloc_for t] returns a pair (allocs,f), f is a formula expressing that 
all allocations in [t] are not aliased and [allocs] is a function expressing
that a pointer is different from all allocated pointers in [t]
*)
  let rec local_alloc_fields allocs n t =	
    (* Format.eprintf "local_alloc_fields@.  allocs = %a@.  t = %a@." 
        print_allocs allocs print_term t; *)
    match tag_type_definition n with
    | TTStructUnion ((Tstruct _),fl) ->
	let allocs',form' as res = 
	  List.fold_right 
	  (fun (tyf, f) (allocs,form) -> 
	     let tf = 
	       { nterm_node = NTarrow (t, f); 
		 nterm_loc = t.nterm_loc;
		 nterm_type = ctype tyf }
	     in
	     let allocs',form' = local_alloc_for allocs tf f.var_name in
	     allocs',form@form')
	  fl 
	  (allocs, [])
	in
	(*
	Format.eprintf "  local_alloc_fields ---> %a@." print_predicate form'; 
	*)
	res 
    | TTIncomplete ->
	error loc ("`" ^ v.var_name ^ "' has incomplete type")
    |  _ ->
	assert false
  and local_alloc_for allocs (t : Cast.nterm) name = 
    (* Format.eprintf "local_alloc_for@.  allocs = %a@.  t = %a@." 
        print_allocs allocs print_term t; *)
    match t.nterm_type.Ctypes.ctype_node with
    | Tstruct n ->
	let allocs_t = allocs name t in
	let allocs n x = 
	  if compatible_type x.nterm_type t.nterm_type 
	  then (allocs n x)@[("separation_"^name^"_"^n, not_alias x t)] 
	  else allocs n x in
	let allocs',form = local_alloc_fields allocs n t in
	allocs', form@allocs_t 
    | Tarray (ty, None) ->
	error loc ("array size missing in `" ^ v.var_name ^ "'")
    | Tarray (ty, Some s) ->
	let ts = int_nconstant (Int64.to_string s) in
	let forall_index i vari pi =
	  make_forall [c_int, i] 
	    (make_implies 
	       (NPand (NPrel (nzero, Le, vari), NPrel (vari, Lt, ts)))
	       pi)
	in
	let allocs_t = allocs name t in
	begin match ty.Ctypes.ctype_node with
	  | Tstruct n ->
	      (* Format.eprintf "  cas d'un tableau de struct@."; *)
	      let i = default_var_info (fresh_index ()) in
	      let vari = { nterm_node = NTvar i; 
			   nterm_loc = t.nterm_loc;
			   nterm_type = c_int } in
	      let ti = 
		{ nterm_node = NTbinop (t, Badd, vari); 
		  nterm_loc = t.nterm_loc;
		  nterm_type = t.nterm_type }
	      in
	      let allocs_i,_ = local_alloc_fields (fun n x -> []) n ti in
	      let j = default_var_info (fresh_index ()) in
	      let varj ={ nterm_node = NTvar j; 
			  nterm_loc = t.nterm_loc;
			  nterm_type = c_int } in
	      let allocs' n x =
		(* allocs x and x<>t and 
		   forall i 0<=i<ts -> i<>j -> allocs_i x *)
		(allocs n x)@(if compatible_type x.nterm_type t.nterm_type 
			    then [("separation_"^name^"_"^n, not_alias x t)]file
			    else [])@
		[("separation_in_tableau_"^name^"_"^n,(forall_index i vari
		   (make_implies (NPrel (vari, Neq, varj)) 
		      (List.fold_left (fun x (_,y) -> make_and x y) 
			 NPtrue (allocs_i n x)))))]
	      in
	      let tj = 
		{ nterm_node = NTbinop (t, Badd, varj); 
		  nterm_loc = t.nterm_loc;
		  nterm_type = t.nterm_type }
	      in
	      let _,form_j = local_alloc_fields allocs' n tj in
	      (* x -> allocs x and x<>t and forall i 0<=i<ts -> allocs_i x *)
	      (fun n x -> 
		 (allocs n x)@(if compatible_type x.nterm_type t.nterm_type 
			     then [("separation_"^name^"_"^n,not_alias x t)]
			    else [])@
	      [("separation_in_structure_in_tableau_"^name^"_"^n,
		(forall_index i vari 
		   (List.fold_left (fun x (_,y) -> make_and x y) 
		      NPtrue (allocs_i n x))))]),
	      (* forall j 0<=j<ts -> form_j *)
	      ("separation_in_tableau_"^name^"_"^n,
	       (forall_index j varj (List.fold_left 
				       (fun x (_,y) -> make_and x y) 
				       NPtrue form_j)))::allocs_t 
	  | Tarray _ ->
	      (* Format.eprintf "  cas d'un tableau d'autre nature@."; *)
	      let i = default_var_info (fresh_index ()) in
	      let vari = { nterm_node = NTvar i; 
			   nterm_loc = t.nterm_loc;
			   nterm_type = c_int } in
	      let ti = { nterm_node = 
			   NTstar {
			     nterm_node = NTbinop (t, Badd, vari); 
			     nterm_type = t.nterm_type;
			     nterm_loc = t.nterm_loc ;
			   } ;
			 nterm_loc = t.nterm_loc;
			 nterm_type = ty } in
	      let allocs_i,_ = local_alloc_for (fun n x -> []) ti (name^"+i") 
	      in
	      let j = default_var_info (fresh_index ()) in
	      let varj ={ nterm_node = NTvar j; 
			  nterm_loc = t.nterm_loc;
			  nterm_type = c_int } in
	      let allocs' n x =
		(* allocs x and x<> t and
		   forall i 0<=i<ts -> i<>j -> allocs_i x *)
		(allocs n x)@(if compatible_type x.nterm_type t.nterm_type 
			    then [("separation_"^name^"_"^n,not_alias x t)]
			    else [])@
		  [("separation_in_tableau_"^name^"_"^n,(forall_index i vari
		     (make_implies (NPrel (vari, Neq, varj)) 
			(List.fold_left (fun x (_,y) -> make_and x y) 
			   NPtrue  (allocs_i n x)))))]
	      in
	      let tj = { nterm_node = 
			   NTstar {
			     nterm_node = NTbinop (t, Badd, varj); 
			     nterm_type = t.nterm_type;
			     nterm_loc = t.nterm_loc ;
			   } ;
			 nterm_loc = t.nterm_loc;
			 nterm_type = ty } in
	      let _,form_j = local_alloc_for allocs' tj (name^"+j") in
	      (* x -> allocs x and x<>t and forall i 0<=i<ts -> allocs_i x *)
	      (fun n x -> 
		 (allocs n x)@(if compatible_type x.nterm_type t.nterm_type 
			    then [("separation_"^name^"_"^n, not_alias x t)]
			     else [])@
		   [("separation_in_tableau_"^name^"_"^n,(forall_index i vari 
		      (List.fold_left (fun x (_,y) -> make_and x y) 
			 NPtrue (allocs_i n x))))]),
	      (* forall j 0<=j<ts -> form_j *)
	     ("separation_in_tableau"^name,(forall_index j varj 
		(List.fold_left (fun x (_,y) -> make_and x y) 
		   NPtrue form_j)))::allocs_t 
	  | _ ->
	      let allocs n x = (allocs n x)@
			     (if compatible_type x.nterm_type t.nterm_type 
			      then [("separation_"^name^"_"^n,not_alias x t)]
			      else []) in
	      allocs, allocs_t
	end
    | _ ->
	(* Format.eprintf "autre (%a)@." print_term t; *)
	allocs, []
  in
  local_alloc_for allocs t v.var_name
*)

