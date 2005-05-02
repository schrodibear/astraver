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

(*i $Id: ceffect.ml,v 1.94 2005-05-02 08:50:16 hubert Exp $ i*)

open Cast
open Coptions
open Clogic
open Creport
open Info
open Format
open Pp
open Output
open Ctypes
open Cenv

let interp_type ctype =
  match ctype.ctype_node with
  | Tvoid -> "unit"
  | Tenum _ | Tint _ -> "int"
  | Tfloat(cfloat) -> "real"
  | Tarray(t,None) -> "pointer"      
  | Tarray(t,Some e) -> "pointer"
  | Tpointer(t) -> "pointer"      
  | Tunion _
  | Tstruct _ -> "pointer"
  | Tvar x -> x (* must be a logic type *)
  | Tfun _ -> unsupported Loc.dummy "first-class functions"

let rec pointer_heap_var ty =
  match ty.ctype_node with
    | Tvar v -> assert false (* should have been expanded *)
    | Tvoid -> failwith "void * not supported"
    | Tint _ -> "int", "int"
    | Tenum _ -> "int", "int"
    | Tfloat _ -> "real", "real"
    | Tarray ({ctype_node = Tstruct _ | Tunion _}, _) 
    | Tpointer {ctype_node = Tstruct _ | Tunion _} ->
	"pointer", "pointer"
    | Tarray (ty,_)
    | Tpointer ty ->
	let v,_ = pointer_heap_var ty in
	(v ^ "P", "pointer")
    | Tstruct _ 
    | Tunion _ -> "pointer", "pointer" 
    | Tfun _ -> unsupported Loc.dummy "first-class functions"

let memory_type t = ([t],"memory")

let pointer_heap_array_var ty =
  match ty.ctype_node with
    | Tarray (ty,_)
    | Tpointer ty ->
	let v,ty = pointer_heap_var ty in
	let v = v^"P" in
	let info = 
	  match Cenv.add_sym Loc.dummy v 
	    Ctypes.c_void (Var_info (default_var_info v)) 
	  with
	    | Var_info v -> v
	    | Fun_info f -> assert false
	in
	(info, memory_type ty)
    | _ -> assert false (* location wrongly typed *)

let heap_vars = Hashtbl.create 97

let print_heap_vars fmt () =
  let base_type fmt = function
    | [], s -> fprintf fmt "%s" s
    | [x], s -> fprintf fmt "%s %s" x s
    | l, s -> fprintf fmt "(%a) %s" (print_list comma pp_print_string) l s
  in
  fprintf fmt "@[";
  Hashtbl.iter 
    (fun s t -> fprintf fmt "(%s:%a)" s base_type t) heap_vars;
  fprintf fmt "@]"

let alloc = 
  let x = "alloc" in
  match Cenv.add_sym Loc.dummy x Ctypes.c_void (Var_info (default_var_info x)) 
  with
    | Var_info v -> v
    | Fun_info _ -> assert false



let heap_var_type v = 
  if v == alloc
  then ([], "alloc_table")
  else 
    try
      Hashtbl.find heap_vars v.var_unique_name
    with Not_found -> 
      eprintf "variable %s not found@." v.var_unique_name;
      assert false

let is_memory_var v = 
  if v == alloc then false
  else
    try 
      let (_,t) = Hashtbl.find heap_vars v.var_unique_name in 
      t = "memory"
    with Not_found -> assert false

let declare_heap_var v ty =
  (*eprintf "declare_heap_var %s (%a)%s\n" v (print_list comma pp_print_string) (fst ty) (snd ty); flush stderr;*)
  if not (Hashtbl.mem heap_vars v) then Hashtbl.add heap_vars v ty
  else assert (Hashtbl.find heap_vars v = ty)

let empty = HeapVarSet.empty
let union = HeapVarSet.union

let add_var v ty s =
  let tyi=
    if v.var_is_referenced then Ctypes.c_pointer ty
    else ty
  in
  declare_heap_var v.var_unique_name ([], interp_type tyi);
  HeapVarSet.add v s

  
let add_alloc s = HeapVarSet.add alloc s

let add_field_var v ty s =
   let n = v.var_unique_name in
   let _,ty = pointer_heap_var ty in
   declare_heap_var n (memory_type ty);
   HeapVarSet.add v s

let add_pointer_var ty s =
  let v,ty = pointer_heap_array_var ty in
  declare_heap_var v.var_unique_name ty;
  HeapVarSet.add v s

type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

let ef_empty = { reads = empty; assigns = empty }
let ef_union e1 e2 = 
  { reads = union e1.reads e2.reads;
    assigns = union e1.assigns e2.assigns }

let reads_add_var v ty e = { e with reads = add_var v ty e.reads }
let reads_add_field_var v ty e = { e with reads = add_field_var v ty e.reads }
let reads_add_pointer_var ty e = { e with reads = add_pointer_var ty e.reads }
let reads_add_alloc e = { e with reads = add_alloc e.reads }

let assigns_add_var v ty e = { e with assigns = add_var v ty e.assigns }
let assigns_add_field_var v ty e = 
  { e with assigns = add_field_var v ty e.assigns }
let assigns_add_pointer_var ty e = 
  { e with assigns = add_pointer_var ty e.assigns }

let rec term t = match t.nterm_node with 
  | NTvar v -> 
      if v.var_is_static
      then add_var v t.nterm_type empty
      else empty
  | NTarrow (t1,f) -> 
      add_alloc (add_field_var f t.nterm_type (term t1))
  | NTstar t ->
      add_alloc (add_pointer_var t.nterm_type (term t))
  | NTunop (Ustar,_) -> assert false
  | NTunop (Uamp, t) -> term t
  | NTunop (Uminus, t) -> term t
  | NTunop (Utilde, t) -> term t
  | NTunop ((Ufloat_of_int | Uint_of_float), t) -> term t
  | NTbase_addr t -> term t
  | NTblock_length t -> add_alloc (term t)
  | NTat (t, _) -> 
      term t
  | NTold t -> 
      term t
  | NTif (t1, t2, t3) -> 
      union (term t1) (union (term t2) (term t3))
  | NTbinop (t1, _, t2) -> 
      union (term t1) (term t2) 
  | NTapp (id, l) -> 
      List.fold_left (fun acc t -> union acc (term t)) id.logic_args l
  | NTconstant _ -> empty
  | NTnull -> empty
  | NTresult -> empty
  | NTcast (_, t) -> term t
  | NTrange (t1, t2, t3) ->
      add_alloc 
	(add_pointer_var t1.nterm_type 
	   (union (term t1) (union (term_option t2) (term_option t3))))

and term_option = function None -> empty | Some t -> term t


(* used to interpret the reads clause *)
let locations ll =
  List.fold_left
    (fun acc l -> union acc (term l)) empty ll

(* used to interpret the assigns clause *)
let rec assign_location t = match t.nterm_node with 
  | NTvar v -> 
      if v.var_is_static
      then { reads = empty; assigns = add_var v t.nterm_type empty }
      else ef_empty
  | NTarrow (t1,f) -> 
      { reads = add_alloc (term t1);
	assigns = add_field_var f t.nterm_type empty }
  | NTstar t1 ->
      { reads = add_alloc (term t1);
	assigns = add_pointer_var t1.nterm_type empty }
  | NTunop (Ustar,_) -> assert false
  | NTunop (Uamp, _) -> assert false
  | NTunop (Uminus, _)  
  | NTunop (Utilde, _)  
  | NTunop ((Ufloat_of_int | Uint_of_float), _)  
  | NTbase_addr _  
  | NTblock_length _  
  | NTat (_, _)  
  | NTold _  
  | NTif (_, _, _)  
  | NTbinop (_, _, _)  
  | NTapp (_, _)  
  | NTconstant _  
  | NTnull  
  | NTresult  
  | NTcast (_, _) -> 
      error t.nterm_loc "invalid location"
  | NTrange (t1, t2, t3) ->
      { reads = add_alloc 
	  (union (term t1) (union (term_option t2) (term_option t3)));
	assigns = add_pointer_var t1.nterm_type empty }

(***
let assign_location loc =
  match loc with
    | Lterm t ->
	 begin 
	   match t.nterm_node with
	     | NTarrow (t1,f) -> 
		 { reads = add_alloc (term t1);
		   assigns = add_field_var f t.nterm_type empty }
	     | NTstar t1 ->
		 { reads = add_alloc (term t1);
		   assigns = add_pointer_var t1.nterm_type empty }
	     | NTunop (Ustar,_) -> assert false
	     | NTvar v ->
		 { reads = empty;
		   assigns = 
		     if v.var_is_static
		     then add_var v t.nterm_type empty
		     else empty }
	     | _ -> assert false
	 end
    | Lstar t ->
	{ reads = add_alloc (term t);
	  assigns = add_pointer_var t.nterm_type empty }
    | Lrange(t1,t2,t3) -> 
	{ reads = add_alloc (union (term t1) (union (term t2) (term t3)));
	  assigns = add_pointer_var t1.nterm_type empty }
***)	  

let rec predicate p = 
  match p with
    | NPtrue -> empty
    | NPfalse -> empty
    | NPapp (id, tl) -> 
	List.fold_left 
	  (fun acc t -> union acc (term t)) 
	  id.logic_args
	  tl 
    | NPrel (t1, _, t2) -> union (term t1) (term t2)
    | NPand (p1, p2)
    | NPor (p1, p2) 
    | NPiff (p1, p2) 
    | NPimplies (p1, p2) -> union (predicate p1) (predicate p2)
    | NPnot p -> predicate p
    | NPif (t, p1, p2) -> union (term t) (union (predicate p1) (predicate p2))
    | NPforall (_, p) -> predicate p	
    | NPexists (_, p) -> predicate p
    | NPfresh t -> add_alloc (term t)
    | NPvalid t -> add_alloc (term t)
    | NPvalid_index (t1,t2) -> add_alloc (union (term t1) (term t2))
    | NPvalid_range (t1,t2, t3) -> 
	add_alloc (union (term t1) (union (term t2) (term t3)))
    | NPold p -> predicate p
    | NPat (p,_) -> predicate p
    | NPnamed (_, p) -> predicate p

let logic_type ls =
  match ls with
    | Clogic.NPredicate_reads(args,locs) -> locations locs
    | Clogic.NPredicate_def(args,pred) -> predicate pred
    | Clogic.NFunction(args,ret,locs) -> locations locs


let option f = function None -> empty | Some x -> f x
let ef_option f = function None -> ef_empty | Some x -> f x

let variant (t,_) = term t

let loop_annot a = 
  let r = union (option predicate a.invariant) (option variant a.variant) in
  { reads = r; assigns = empty (* TODO *) }

(* table for weak invariants *)
let weak_invariants = Hashtbl.create 97

let print_effects fmt l =
  fprintf fmt "@[%a@]"
    (print_list space (fun fmt v -> pp_print_string fmt v.var_unique_name)) 
    (HeapVarSet.elements l)

let add_weak_invariant id p =
  Hashtbl.add weak_invariants id (p, predicate p)

(* table for strong invariants *)
let strong_invariants = Hashtbl.create 97

let add_strong_invariant id p vars =
  if p <> NPtrue then
  let ef = predicate p in
  Hashtbl.add strong_invariants id (p,ef,vars)

let strong_invariants_2 = Hashtbl.create 97

let mem_strong_invariant_2 id =
  Hashtbl.mem strong_invariants_2 id

let add_strong_invariant_2 id p args =
  if not (mem_strong_invariant_2 id) 
  then
    if p <> NPtrue then
      let ef = predicate p in
      Hashtbl.add strong_invariants_2 id (p,ef,args)      

let intersect_only_alloc e1 e2 =
  HeapVarSet.is_empty (HeapVarSet.remove alloc (HeapVarSet.inter e1 e2))

let weak_invariants_for hvs =
  Hashtbl.fold
    (fun name (_,e) acc ->
        if intersect_only_alloc e hvs then acc
       else union e acc) 
    weak_invariants empty

let strong_invariants_for hvs =
  Hashtbl.fold
    (fun s (_,_,e) acc -> 
       if HeapVarSet.subset e hvs then union e acc
       else acc) 
    strong_invariants empty

let spec sp = 
  ef_union
    { reads = 
	union 
	  (union (option predicate sp.requires) (option predicate sp.ensures))
	  (option variant sp.decreases);
      assigns = empty }
    (ef_option 
       (List.fold_left
	  (fun acc l -> ef_union acc (assign_location l)) ef_empty)
       sp.Clogic.assigns)

open Cast

let rec expr e = match e.nexpr_node with
  | NEnop
  | NEconstant _
  | NEstring_literal _ -> ef_empty
  | NEvar (Var_info v) ->
      if v.var_is_static 
      then reads_add_var v e.nexpr_type ef_empty
      else ef_empty
  | NEvar (Fun_info v) ->
      ef_empty
  | NEarrow (e1, f) ->	
      reads_add_alloc (reads_add_field_var f e.nexpr_type (expr e1))
  | NEbinary (e1, _, e2) | NEseq (e1, e2) ->
      ef_union (expr e1) (expr e2)
  | NEassign (lv, e) | NEassign_op (lv, _, e) ->
      ef_union (assign_expr lv) (expr e)
  | NEstar e ->
      reads_add_alloc (reads_add_pointer_var e.nexpr_type (expr e))
  | NEunary (Ustar , _ ) -> assert false
  | NEunary (Uamp, e) ->
      address_expr e
  | NEunary 
      ((Uplus | Uminus | Unot | Utilde | Ufloat_of_int | Uint_of_float), e) ->
      expr e
  | NEincr (_, e) ->
      assign_expr e
  | NEcall (e, el) ->
      let ef = match e.nexpr_node with
	| NEvar (Fun_info f) -> 
	    { reads = f.function_reads; assigns = f.function_writes } 
	| _ -> expr e
      in
      List.fold_left (fun ef arg -> ef_union (expr arg) ef) ef el
  | NEcond (e1, e2, e3) ->
      ef_union (ef_union (expr e1) (expr e2)) (expr e3)
  | NEcast (_, e) ->
      expr e

(* effects for [e = ...] *)
and assign_expr e = match e.nexpr_node with
  | NEvar (Var_info v) -> 
      if v.var_is_static
      then assigns_add_var v e.nexpr_type ef_empty
      else ef_empty
  | NEvar (Fun_info _) ->
      ef_empty
  | NEstar e ->
      reads_add_alloc (assigns_add_pointer_var e.nexpr_type (expr e))
  | NEunary (Ustar,_) -> assert false
  | NEarrow (e1, f) ->
      reads_add_alloc (assigns_add_field_var f e.nexpr_type (expr e1))
  | NEcast (_, e1) ->
      assign_expr e1
  | _ -> 
      assert false (* not a left value *)

(* effects for [&e] *)
and address_expr e = match e.nexpr_node with
  | NEvar v -> 
      begin match e.nexpr_type.Ctypes.ctype_node with
	| Tstruct _ | Tunion _ -> assert false (* ef_empty *)
	| _ -> ef_empty (* unsupported "& operator" *)
      end
  | NEstar  e1 ->
      expr e1
  | NEarrow (e1, f) ->
      begin match e1.nexpr_type.Ctypes.ctype_node with
	| Tenum _ | Tint _ | Tfloat _ -> expr e1
	| _ -> reads_add_field_var f e.nexpr_type (expr e1)
      end
 (* | NEcast (_, e1) ->
      address_expr e1*)
  | _ -> 
      assert false (* not a left value *)

let rec statement s = match s.nst_node with
  | NSnop
  | NSbreak
  | NScontinue
  | NSlogic_label _
  | NSreturn None ->
      ef_empty
  | NSexpr e -> 
      expr e
  | NSif (e, s1, s2) -> 
      ef_union (expr e) (ef_union (statement s1) (statement s2))
  | NSwhile (annot, e, s)
  | NSdowhile (annot, s, e) ->
      ef_union (loop_annot annot) (ef_union (statement s) (expr e))
  | NSfor (annot, e1, e2, e3, s) ->
      ef_union (loop_annot annot) (ef_union (ef_union (expr e1) (expr e2))
				     (ef_union (expr e3) (statement s)))
  | NSblock bl ->
      block bl
  | NSreturn (Some e) ->
      expr e
  | NSlabel (_, s) ->
      statement s
  | NSswitch (e, used_cases, case_list) -> 
      List.fold_left
	(fun ef (cases,bl) ->
	   List.fold_left 
	     (fun ef i -> ef_union ef (statement i))
	     ef bl)
	(expr e)
	case_list
  | NSassert p ->
      { reads = predicate p; assigns = empty }
  | NSspec (sp, s) ->
      ef_union (spec sp) (statement s)
  | NSdecl (_, _, i,rem) -> ef_union (initializer_option i) (statement rem)

and block sl =
(*  let local_decl d = match d.node with
    | Ndecl (_, _, i) -> initializer_option i
    | Ntypedecl _ -> ef_empty
    | _ -> ef_empty (* unsupported local declaration *)
  in*)
  List.fold_left
    (fun ef s -> ef_union (statement s) ef)
(*    (List.fold_left (fun ef d -> ef_union (local_decl d) ef) ef_empty dl)*)
    ef_empty
    sl

and initializer_ = function
  | Iexpr e -> 
      expr e
  | Ilist il -> 
      List.fold_left (fun ef i -> ef_union (initializer_ i) ef) ef_empty il

and initializer_option = function
  | None -> ef_empty
  | Some i -> initializer_ i

let print_effects fmt l =
  fprintf fmt "@[%a@]"
    (print_list space (fun fmt v -> pp_print_string fmt v.var_unique_name)) 
    (HeapVarSet.elements l)

(* first pass: declare invariants and computes effects for logics *)


let rec ctype ty =
  ctype_node ty.Ctypes.ctype_node

and ctype_node = function
  | Tvoid -> sprintf "void"
  | Tint _ -> sprintf "int"
  | Tfloat _ -> sprintf "float"
  | Ctypes.Tvar s -> sprintf "%s" s
  | Tarray (ty, _) -> sprintf "%s" (ctype ty)
  | Tpointer ty -> sprintf "%s*" (ctype ty)
  | Tstruct s -> sprintf "%s" s;
  | Tunion s -> sprintf "%s" s
  | Tenum s -> sprintf "%s" s
  | Tfun _ -> assert false
		   
let global_var = ref [] 

let invariant_for_global loc v =
  assert (not (List.mem v !global_var));
  let form =
    List.fold_left 
      (fun p x ->
	 ("separation_" ^ (ctype v.var_type) ^ "_" ^ (ctype x.var_type),
	   "separation_"^v.var_name^"_"^x.var_name,
	  Cnorm.separation loc v x,
	  HeapVarSet.add v (HeapVarSet.singleton x)) :: p) 
      [] !global_var 
  in 
  global_var := v::!global_var;
  form
    
let not_a_constant_value loc = error loc "is not a constant value"

(*let binop loc e1 e2 op = 
  match e1.nexpr_node, e2.nexpr_node, op with
  | _, _, Badd | _, _, Badd_int | _, _, Badd_float | _, _, Badd_pointer_int ->
      NTbinop(term_of_expr e1, Clogic.Badd, term_of_expr e2)
  | _, _, Bsub | _, _, Bsub_int | _, _, Bsub_float | _, _, Bsub_pointer -> 
      NTbinop(term_of_expr e1, Clogic.Bsub, term_of_expr e2)
  | _, _, Bmul | _, _, Bmul_int | _, _, Bmul_float -> 
      NTbinop(term_of_expr e1, Clogic.Bmul, term_of_expr e2)
  | _, _, Bdiv | _, _, Bdiv_int | _, _, Bdiv_float -> 
      NTbinop(term_of_expr e1, Clogic.Bdiv, term_of_expr e2)
  | _, _, Bmod | _, _, Bmod_int ->  
      NTbinop(term_of_expr e1, Clogic.Bmod, term_of_expr e2)
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Beq_int 
  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), Beq_float 
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Beq_pointer  ->
      if e1 = e2 then NEconstant (Intconstant "0")
      else NEconstant (IntConstant "1")
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bneq_int 
  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), Bneq_float 
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bneq_pointer  ->
      if e1 = e2 then NEconstant (IntConstant "1")
      else NEconstant (IntConstant "0")
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Blt_int 
  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), Blt_float 
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Blt_pointer  ->
      if e1 < e2 then NEconstant (IntConstant "0")
      else NEconstant (IntConstant "1")
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bgt_int 
  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), Bgt_float 
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bgt_pointer  ->
      if e1 > e2 then NEconstant (IntConstant "0")
      else NEconstant (IntConstant "1")
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Ble_int 
  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), Ble_float 
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Ble_pointer  ->
      if e1 <= e2 then NEconstant (IntConstant "0")
      else NEconstant (IntConstant "1")
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bge_int 
  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), Bge_float 
  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bge_pointer  ->
      if e1 >= e2 then NEconstant (IntConstant "0")
      else NEconstant (IntConstant "1")
  | _, _, Beq | _, _, Beq_int | _, _, Beq_float | _, _, Beq_pointer      
  |  _, _, Blt |  _, _, Blt_int |  _, _, Blt_float |  _, _, Blt_pointer
  |  _, _, Bgt |  _, _, Bgt_int |  _, _, Bgt_float |  _, _, Bgt_pointer
  |  _, _, Ble |  _, _, Ble_int |  _, _, Ble_float |  _, _, Ble_pointer
  |  _, _, Bge |  _, _, Bge_int |  _, _, Bge_float |  _, _, Bge_pointer
  |  _, _, Bneq |  _, _, Bneq_int |  _, _, Bneq_float |  _, _, Bneq_pointer
  |  _, _, Bbw_and
  |  _, _, Bbw_xor
  |  _, _, Bbw_or
  |  _, _, Band
  |  _, _, Bor
  |  _, _, Bshift_left
  |  _, _, Bshift_right -> error loc "not a constant value"
*)

let unop = function
  | Ustar -> Clogic.Ustar
  | Uamp -> Clogic.Uamp
  | Utilde -> Clogic.Utilde
  | Ufloat_of_int -> Clogic.Ufloat_of_int
  | Uint_of_float -> Clogic.Uint_of_float
  | Uminus -> Clogic.Uminus
  | Uplus | Unot -> assert false

let rec term_of_expr e =
  let make n = 
    { nterm_node = n; nterm_type = e.nexpr_type; nterm_loc = e.nexpr_loc }
  in
  match e.nexpr_node with 
  | NEconstant e -> make (NTconstant e)
  | NEvar (Var_info info) -> make (NTvar info)
  | NEarrow (nlvalue,var_info) -> 
      make (NTarrow (term_of_expr nlvalue, var_info))
  | NEstar (nlvalue) -> 
      make (NTstar (term_of_expr nlvalue))
  | NEunary (Uplus, nexpr) -> 
      term_of_expr nexpr
  | NEunary (Unot, nexpr) -> 
      make (NTif ((term_of_expr nexpr), 
		  make (NTconstant (IntConstant "0")), 
		  make (NTconstant (IntConstant "1"))))
  | NEunary (op, nexpr) ->  
      make (NTunop (unop op, term_of_expr nexpr))  
  | NEbinary (e1, op, e2) ->
      begin
	match e1.nexpr_node, e2.nexpr_node, op with
	  | _, _, Badd | _, _, Badd_int | _, _, Badd_float 
	  | _, _, Badd_pointer_int ->
	      make (NTbinop(term_of_expr e1, Clogic.Badd, term_of_expr e2))
	  | _, _, Bsub | _, _, Bsub_int | _, _, Bsub_float 
	  | _, _, Bsub_pointer -> 
	      make (NTbinop(term_of_expr e1, Clogic.Bsub, term_of_expr e2))
	  | _, _, Bmul | _, _, Bmul_int | _, _, Bmul_float -> 
	      make (NTbinop(term_of_expr e1, Clogic.Bmul, term_of_expr e2))
	  | _, _, Bdiv | _, _, Bdiv_int | _, _, Bdiv_float -> 
	      make (NTbinop(term_of_expr e1, Clogic.Bdiv, term_of_expr e2))
	  | _, _, Bmod | _, _, Bmod_int ->  
	      make (NTbinop(term_of_expr e1, Clogic.Bmod, term_of_expr e2))
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Beq_int 
	  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), 
	    Beq_float 
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), 
	    Beq_pointer  ->
	      if e1 = e2 then make (NTconstant (IntConstant "0"))
	      else make (NTconstant (IntConstant "1"))
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bneq_int 
	  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), 
	    Bneq_float 
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), 
	    Bneq_pointer  ->
	      if e1 = e2 then make (NTconstant (IntConstant "1"))
	      else make (NTconstant (IntConstant "0"))
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Blt_int 
	  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), 
	    Blt_float 
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), 
	    Blt_pointer  ->
	      if e1 < e2 then make (NTconstant (IntConstant "0"))
	      else make (NTconstant (IntConstant "1"))
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bgt_int 
	  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), 
	    Bgt_float 
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), 
	    Bgt_pointer  ->
	      if e1 > e2 then make (NTconstant (IntConstant "0"))
	      else make (NTconstant (IntConstant "1"))
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Ble_int 
	  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), 
	    Ble_float 
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), 
	    Ble_pointer  ->
	      if e1 <= e2 then make (NTconstant (IntConstant "0"))
	      else make (NTconstant (IntConstant "1"))
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), Bge_int 
	  | NEconstant (FloatConstant e1), NEconstant (FloatConstant e2), 
	    Bge_float 
	  | NEconstant (IntConstant e1), NEconstant (IntConstant e2), 
	    Bge_pointer  ->
	      if e1 >= e2 then make (NTconstant (IntConstant "0"))
	      else make (NTconstant (IntConstant "1"))
	  | _, _, Beq | _, _, Beq_int | _, _, Beq_float | _, _, Beq_pointer 
	  |  _, _, Blt |  _, _, Blt_int |  _, _, Blt_float |  _, _, Blt_pointer
	  |  _, _, Bgt |  _, _, Bgt_int |  _, _, Bgt_float |  _, _, Bgt_pointer
	  |  _, _, Ble |  _, _, Ble_int |  _, _, Ble_float |  _, _, Ble_pointer
	  |  _, _, Bge |  _, _, Bge_int |  _, _, Bge_float |  _, _, Bge_pointer
	  |  _, _, Bneq |  _, _, Bneq_int |  _, _, Bneq_float 
	  |  _, _, Bneq_pointer
	  |  _, _, Bbw_and
	  |  _, _, Bbw_xor
	  |  _, _, Bbw_or
	  |  _, _, Band
	  |  _, _, Bor
	  |  _, _, Bshift_left
	  |  _, _, Bshift_right -> error e.nexpr_loc "not a constant value"
      end
  | NEcond (e1, e2, e3) ->
      make (NTif (term_of_expr e1, term_of_expr e2, term_of_expr e3))
  | NEcast (ty, e) ->
      make (NTcast (ty, term_of_expr e))
  | NEvar (Fun_info _)
  | NEcall _ 
  | NEincr (_, _)
  | NEassign_op (_, _, _)
  | NEassign (_, _) 
  | NEseq (_, _)
  | NEstring_literal _
  | NEnop -> 
      not_a_constant_value e.nexpr_loc

let noattr loc ty e =
  { nterm_node = e;
    nterm_type = ty;
    nterm_loc  = loc
  }

let rec pop_initializer loc t i =
  match i with 
    | [] ->{ nterm_node = 
	       (match t.Ctypes.ctype_node with
		  | Tint _ | Tenum _ -> NTconstant(IntConstant "0")
		  | Tfloat _ -> NTconstant(FloatConstant "0.0")
		  | Tpointer _ -> 
		      NTcast (t,
			      {nterm_node = NTconstant (IntConstant "0");
			       nterm_type = c_int;
			       nterm_loc  = loc})
		  | _ -> assert false);
	     nterm_type = t;
	     nterm_loc  = loc
	    },[]
    | (Iexpr e)::l -> term_of_expr e,l
    | (Ilist [])::l -> pop_initializer loc t l
    | (Ilist l)::l' -> 
	let e,r = pop_initializer loc t l in e,r@l'

let rec invariant_for_constant loc t lvalue initializers =
 match t.Ctypes.ctype_node with
    | Tint _ | Tfloat _ | Tpointer _ | Tenum _ -> 
	let x,l = pop_initializer loc t initializers in
	NPrel ( lvalue,Eq,x), l
    | Tstruct n ->
	begin match tag_type_definition n with
	  | TTStructUnion (Tstruct (_), fl) ->
	      List.fold_left 
		(fun (acc,init) f -> 
		   let tyf = f.var_type in
		   let tyf =  { 
		     Ctypes.ctype_node = tyf.Ctypes.ctype_node;
		     Ctypes.ctype_storage = tyf.Ctypes.ctype_storage;
		     Ctypes.ctype_const = tyf.Ctypes.ctype_const 
					  || t.Ctypes.ctype_const;
		     Ctypes.ctype_volatile = tyf.Ctypes.ctype_volatile;
		   }  in 
		   let block, init' =
		     invariant_for_constant loc tyf 
		       (Cnorm.in_struct lvalue f) init
		   in 
		   if tyf.Ctypes.ctype_const then
		     (NPand (acc,block),init')
		   else
		     (acc,init'))
		(NPtrue,initializers)  fl
	  | _ ->
	      assert false
	end
    | Tunion n ->
	begin match tag_type_definition n with
	  | TTStructUnion (Tstruct (_), f::_) ->
	      let block, init' =
		 invariant_for_constant loc f.var_type 
		  (noattr loc f.var_type (NTarrow(lvalue, f)))
		  initializers
	      in (block,init')
	  | _ ->
	      assert false
	end
    | Tarray (ty,Some t) ->
	let rec init_cells i (block,init) =
	  if i >= t then (block,init)
	  else
	    let ts = (noattr loc c_int 
			(NTconstant (IntConstant (Int64.to_string i)))) in
	    let (b,init') = 
	       invariant_for_constant loc ty 
		(noattr loc ty 
		   (NTstar 
		      (noattr loc 
			 {Ctypes.ctype_node = (Tpointer ty);
			  Ctypes.ctype_storage = ty.Ctypes.ctype_storage;
			  Ctypes.ctype_const = ty.Ctypes.ctype_const;
			  Ctypes.ctype_volatile = ty.Ctypes.ctype_volatile;
			 }
			 (NTbinop (lvalue,Clogic.Badd, ts))))) init 
	    in
	    init_cells (Int64.add i Int64.one) (NPand (block,b),init')
	in
	init_cells Int64.zero (NPtrue,initializers)
    | Tarray (ty,None) -> assert false
    | Tfun (_, _) -> assert false
    | Tvar _ -> assert false
    | Tvoid -> assert false  

let rec has_constant_values ty = match ty.Ctypes.ctype_node with
  | Tvoid | Tint _ | Tfloat _ | Tenum _ | Tpointer _ ->
      ty.Ctypes.ctype_const
  | Tstruct n -> 
      ty.Ctypes.ctype_const ||
      (match tag_type_definition n with
	 | TTStructUnion (Tstruct _, fl) -> 
	     List.exists (fun f -> has_constant_values f.var_type) fl
	 | _ -> assert false)
  | Tarray (ty', _) -> has_constant_values ty'
  | Tunion _ | Tfun _ | Tvar _ -> false

	  
let rec validity x ty size =
  match ty.Ctypes.ctype_node with
    | Tarray (ty', Some size') ->
	let i = default_var_info "counter" in
	let vari = { nterm_node = NTvar i; 
		     nterm_loc = x.nterm_loc;
		     nterm_type = c_int } in
	let j = default_var_info "counter2" in
	let varj = { nterm_node = NTvar j; 
		     nterm_loc = x.nterm_loc;
		     nterm_type = c_int } in	  
	let term_sup = { nterm_node = NTconstant (IntConstant 
						    (Int64.to_string size)); 
			 nterm_loc = x.nterm_loc;
			 nterm_type = c_int } in
	let ineq = NPand 
		     (NPrel (Cnorm.nzero, Le, vari),
		      NPrel (vari, Lt, 
			       term_sup)) in	
	let jneq = NPand 
		     (NPrel (Cnorm.nzero, Le, varj),
		      NPrel (varj, Lt, 
			     term_sup)) in
	let (pre1,pre2) = validity 
			(noattr x.nterm_loc ty 
			   (NTbinop (x,Clogic.Badd,vari)))
					     ty' size' in
	(NPand (
	  NPvalid_range (x, Cnorm.nzero,term_sup),
	  NPforall (
	    [c_int,i],
	    NPimplies(ineq,pre1))),
	  NPforall (
	    (c_int,j)::[(c_int,i)],
	    NPimplies(NPand (NPand (ineq,jneq),
			     Invariant.diff x.nterm_loc vari varj),
		      NPand (Invariant.diff x.nterm_loc 
			       (noattr x.nterm_loc ty 
				  (NTbinop (x,Clogic.Badd,vari)))
			       (noattr x.nterm_loc ty 
				  (NTbinop (x,Clogic.Badd,varj))),
			       pre2))))
(*    | Tstruct (n) ->
	let term_sup = { nterm_node = NTconstant (IntConstant 
						    (Int64.to_string size)); 
			 nterm_loc = x.nterm_loc;
			 nterm_type = c_int } in
	let name = "internal_separation_" ^ n in
	NPvalid_range (x, Cnorm.nzero,term_sup), 
	NPapp (snd (find_pred name), [x])
*)			
    | _ ->  
	let term_sup = { nterm_node = NTconstant (IntConstant 
						    (Int64.to_string size)); 
			 nterm_loc = x.nterm_loc;
			 nterm_type = c_int } in
      NPvalid_range (x, Cnorm.nzero,term_sup), NPtrue

let decl d =
  match d.Cast.node with
    | Nlogic(id,ltype) -> 
	let l = logic_type ltype in
	lprintf 
	  "effects of logic declaration of %s: @[%a@]@." id.logic_name
	  print_effects l;
	id.logic_args <- l
    | Ninvariant(id,p) -> 
	add_weak_invariant id p
    | Ninvariant_strong(id,p) -> 
	let pre = (predicate p) in 
	add_strong_invariant id p pre	  
    | Ndecl(ty,v,init) when ty.Ctypes.ctype_storage <> Extern -> 
	begin
	  match ty.Ctypes.ctype_node with
	   | Tstruct _ | Tarray (_,None) -> assert false
	   | Tarray (typ, Some s) ->
	       lprintf "adding implicit invariant for validity of %s@." 
		 v.var_name;
	       let t = { nterm_node = NTvar v; 
			 nterm_loc = d.loc;
			 nterm_type = ty } in
	       let name1 = "valid_range_" ^ v.var_name in
	       let (pre1,pre2) = validity t typ s in
	       add_strong_invariant name1 pre1 (HeapVarSet.singleton v);   
	       List.iter (fun (x1,x2,p,y) -> add_strong_invariant x2 p y;
			    add_strong_invariant_2 x1 p [])
		 (invariant_for_global d.loc v);
	   | _ -> ()
	end;
	
	let init = (match init with | None -> [] | Some l -> [l]) in
	if has_constant_values ty then begin
	  lprintf "adding implicit invariant for constant %s@." v.var_name;
	  let id = "constant_" ^ v.var_name in
	  let t = {nterm_node = NTvar v; 
		   nterm_loc = Loc.dummy;
		   nterm_type = ty } in
	  let (pre,_) = invariant_for_constant d.loc ty t init in
	  let info = Info.default_logic_info id in 
	  add_strong_invariant_2 id pre [] ;
	  add_strong_invariant id pre (HeapVarSet.singleton v)
	end;
    | Ndecl(ty,v,init) -> () (* nothing to do for extern var *)	
    | Naxiom(id,p) -> () (* TODO *)
    | Ntypedef(ctype,id) -> () 
    | Ntypedecl(ctype) -> ()
    | Nfunspec(spec,ctype,id) -> () (* TODO *)
    | Nfundef(spec,ctype,id,block) -> () (* TODO *)

let file l = List.iter decl l

(* second pass: compute functions effects as a fixpoint *)

let warnings = Queue.create ()

let functions dl = 
  let fixpoint = ref true in
  let declare id ef =
    lprintf "effects for function %s before invariants: reads %a writes %a@." 
      id.fun_name print_effects ef.reads print_effects ef.assigns;
    let ef  = {
      reads = union 
		(union ef.reads 
		   (weak_invariants_for (union ef.reads ef.assigns)))
		(strong_invariants_for (union ef.reads ef.assigns)) ;
      assigns = ef.assigns }
    in
    lprintf "effects for function %s: reads %a writes %a@." id.fun_name 
      print_effects ef.reads print_effects ef.assigns;
    if not (HeapVarSet.subset ef.reads id.function_reads) then begin
      fixpoint := false;
      id.function_reads <- ef.reads
    end;
    if not (HeapVarSet.subset ef.assigns id.function_writes) then begin
      fixpoint := false;
      id.function_writes <- ef.assigns
    end
  in
  let decl d = match d.node with
    | Nfunspec (sp, _, id) ->
	declare id (spec sp)
    | Nfundef (sp, _, id, s) ->
	let ef_spec = spec sp in
	let ef = 
	  if verify id.fun_name then
	    let ef_body = statement s in
	    begin match sp.Clogic.assigns with
	      | None -> 
		  (* no assigns given by user:
		     emit a warning if some side-effects have been detected *)
		  if id <> Cinit.invariants_initially_established_info &&
		    not (HeapVarSet.is_empty ef_body.assigns) then
		      Queue.add 
			(d.loc,
			 "function " ^ id.fun_name ^ 
			   " has side-effects but no 'assigns' clause given")
			warnings
	      | Some _ -> 
		  (* some assigns given by user:
		     emit a warning if side-effects of spec differs from 
		     side-effects of body *) 
		  if not (HeapVarSet.equal ef_spec.assigns ef_body.assigns) 
		  then begin 
		    Queue.add 
		      (d.loc,
		       "'assigns' clause for function " ^ id.fun_name ^
			 " do not match side-effects of its body ")
		      warnings		    
		  end
	    end;
	    ef_union ef_spec ef_body
	  else
	    ef_spec
	in
	declare id ef
    | _ -> 
	()
  in
  List.iter decl dl;
  !fixpoint


