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

(*i $Id: ceffect.ml,v 1.62 2004-12-01 14:45:22 filliatr Exp $ i*)

open Cast
open Coptions
open Clogic
open Creport
open Info
open Format
open Pp
open Output

let interp_type ctype =
  match ctype.ctype_node with
  | CTvoid -> "unit"
  | CTenum _ | CTint _ -> "int"
  | CTfloat(cfloat) -> "real"
  | CTarray(t,None) -> "pointer"      
  | CTarray(t,Some e) -> "pointer"
  | CTpointer(t) -> "pointer"      
  | CTunion _
  | CTstruct _ -> "pointer"
  | CTvar x -> x (* must be a logic type *)
  | CTfun _ -> unsupported Loc.dummy "first-class functions"

let rec pointer_heap_var ty =
  match ty.ctype_node with
    | CTvar v -> assert false (* should have been expanded *)
    | CTvoid -> failwith "void * not supported"
    | CTint _ -> "int", "int"
    | CTenum _ -> "int", "int"
    | CTfloat _ -> "real", "real"
    | CTarray ({ctype_node = CTstruct _ | CTunion _}, _) 
    | CTpointer {ctype_node = CTstruct _ | CTunion _} ->
	"pointer", "pointer"
    | CTarray (ty,_)
    | CTpointer ty ->
	let v,_ = pointer_heap_var ty in
	(v ^ "P", "pointer")
    | CTstruct _ 
    | CTunion _ -> "pointer", "pointer" (* OK? *)
    | CTfun _ -> assert false (* bad typing ! *)

let memory_type t = ([t],"memory")

let pointer_heap_array_var ty =
  match ty.ctype_node with
    | CTarray (ty,_)
    | CTpointer ty ->
	let v,ty = pointer_heap_var ty in
	let v = v^"P" in
	let info = 
	  match Cenv.add_sym Loc.dummy v 
	    Cltyping.c_void (Var_info (default_var_info v)) 
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
  match Cenv.add_sym Loc.dummy x Cltyping.c_void (Var_info (default_var_info x)) 
  with
    | Var_info v -> v
    | Fun_info _ -> assert false



let heap_var_type v = 
  if v == alloc
  then ([], "alloc_table")
  else Hashtbl.find heap_vars v.var_unique_name

let is_memory_var v = 
  if v == alloc then false
  else
    try 
      let (_,t) = Hashtbl.find heap_vars v.var_unique_name in 
      t = "memory"
    with Not_found -> assert false

let declare_heap_var v ty =
(**
  eprintf "declare_heap_var %s (%a)%s\n" v (print_list comma pp_print_string) (fst ty) (snd ty); flush stderr;
**)
  if not (Hashtbl.mem heap_vars v) then Hashtbl.add heap_vars v ty
  else assert (Hashtbl.find heap_vars v = ty)

let empty = HeapVarSet.empty
let union = HeapVarSet.union

let add_var v ty s =
  let tyi =
    if v.var_is_referenced then Cltyping.c_pointer ty
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

let rec term t =
  match t.nterm_node with 
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
	List.fold_left 
	  (fun acc t -> union acc (term t)) 
	  id.logic_args
	  l
    | NTconstant _ -> empty
    | NTnull -> empty
    | NTresult -> empty
    | NTcast (_, t) -> term t

let location loc =
  match loc with
    | Lterm t -> term t 
    | Lstar t ->
	add_pointer_var t.nterm_type (term t)
    | Lrange(t1,t2,t3) -> 
	add_pointer_var t1.nterm_type
	  (union 
	     (term t1)
	     (union (term t2) (term t3)))

let locations ll =
  List.fold_left
    (fun acc l -> union acc (location l)) empty ll

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

let add_weak_invariant id p =
  Hashtbl.add weak_invariants id (p, predicate p)

let intersect_only_alloc e1 e2 =
  HeapVarSet.is_empty (HeapVarSet.remove alloc (HeapVarSet.inter e1 e2))

let weak_invariants_for hvs =
  Hashtbl.fold
    (fun _ (_,e) acc -> 
       if intersect_only_alloc e hvs then acc
       else union e acc) 
    weak_invariants empty

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
      begin match e.nexpr_type.ctype_node with
	| CTstruct _ | CTunion _ -> ef_empty
	| _ -> ef_empty (* unsupported "& operator" *)
      end
  | NEstar  e1 ->
      expr e1
  | NEarrow (e1, f) ->
      begin match e1.nexpr_type.ctype_node with
	| CTenum _ | CTint _ | CTfloat _ -> expr e1
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

and block (dl, sl) =
  let local_decl d = match d.node with
    | Ndecl (_, _, i) -> initializer_ i
    | Ntypedecl _ -> ef_empty
    | _ -> ef_empty (* unsupported local declaration *)
  in
  List.fold_left
    (fun ef s -> ef_union (statement s) ef)
    (List.fold_left (fun ef d -> ef_union (local_decl d) ef) ef_empty dl)
    sl

and initializer_ = function
  | Inothing -> 
      ef_empty
  | Iexpr e -> 
      expr e
  | Ilist il -> 
      List.fold_left (fun ef i -> ef_union (initializer_ i) ef) ef_empty il

let print_effects fmt l =
  fprintf fmt "@[%a@]"
    (print_list space 
       (fun fmt v -> pp_print_string fmt v.var_name)) (HeapVarSet.elements l)

(* first pass: declare invariants and computes effects for logics *)

let invariant_for_global =
  let allocs = ref (fun x -> NPtrue) in
  fun loc v t ->
    let allocs',form = Cnorm.separation ~allocs:!allocs loc v t in
    allocs := allocs';
    NPand (form, Cnorm.valid_for_type loc v t)

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
    | Ndecl({ctype_node = CTstruct _ | CTarray _} as ty, v, _) 
      when ty.ctype_storage <> Extern ->
	lprintf "adding implicit invariant for %s@." v.var_name;
	let id = "valid_" ^ v.var_name in
	let t = { nterm_node = NTvar v; 
		  nterm_loc = Loc.dummy;
		  nterm_type = ty } in
	add_weak_invariant id (invariant_for_global d.loc v t) 
    | Ndecl(ctype,v,init) -> () (* TODO *)
    | Naxiom(id,p) -> () (* TODO *)
    | Ntypedef(ctype,id) -> () 
    | Ntypedecl(ctype) -> ()
    | Nfunspec(spec,ctype,id,params) -> () (* TODO *)
    | Nfundef(spec,ctype,id,params,block) -> () (* TODO *)

let file l = List.iter decl l

(* second pass: compute functions effects as a fixpoint *)

let warnings = Queue.create ()

let functions dl = 
  let fixpoint = ref true in
  let declare id ef =
    lprintf "effects for function %s before invariants: reads %a writes %a@." 
      id.fun_name print_effects ef.reads print_effects ef.assigns;
    let ef  = {
      reads = union ef.reads (weak_invariants_for (union ef.reads ef.assigns));
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
    | Nfunspec (sp, _, id, _) ->
	declare id (spec sp)
    | Nfundef (sp, _, id, _, s) ->
	let ef_spec = spec sp and ef_body = statement s in
	begin
	  match sp.Clogic.assigns with
	    | None -> 
		(* no assigns given by user:
		   emit a warning if some side-effects have been detected *)
		if not (HeapVarSet.is_empty ef_body.assigns) then
		  Queue.add 
		    (d.loc,
		     "function " ^ id.fun_name ^ " has side-effects but no 'assigns' clause given")
		    warnings
	    | Some _ -> 
		(* some assigns given by user:
		   emit a warning if side-effects of spec differs from side-effects of body *) 
		if not (HeapVarSet.equal ef_spec.assigns ef_body.assigns) then 
		  begin 
		    Queue.add 
		      (d.loc,
		       "'assigns' clause for function " ^ id.fun_name ^
		       " do not match side-effects of its body ")
		      warnings		    
		  end
	end;
	declare id (ef_union ef_spec ef_body)
    | _ -> 
	()
  in
  List.iter decl dl;
  !fixpoint

