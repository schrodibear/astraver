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

(*i $Id: ceffect.ml,v 1.28 2004-03-25 10:37:22 filliatr Exp $ i*)

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
  | CTfloat(cfloat) -> "float"
  | CTarray(t,None) -> "pointer"      
  | CTarray(t,Some e) -> "pointer"
  | CTpointer(t) -> "pointer"      
  | CTunion _
  | CTstruct _ -> "pointer"
  | CTvar x -> x (* must be a logic type *)
  | CTfun _ -> unsupported "first-class functions"

let rec pointer_heap_var ty =
  match ty.ctype_node with
    | CTvar v -> assert false (* should have been expanded *)
    | CTvoid -> failwith "void * not supported"
    | CTint _ -> "int", "int"
    | CTenum _ -> "int", "int"
    | CTfloat _ -> "float", "float"
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
	(v ^ "P", memory_type ty)
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

let heap_var_type = function
  | "alloc" -> ([], "alloc")
  | v -> Hashtbl.find heap_vars v

let declare_heap_var v ty =
  if not (Hashtbl.mem heap_vars v) then Hashtbl.add heap_vars v ty
  else assert (Hashtbl.find heap_vars v = ty)

let heap_var_names = Hashtbl.create 97 

let name_heap_var v =
  let rec fresh i = 
    let un = v ^ "_" ^ string_of_int i in
    if Hashtbl.mem heap_vars un then fresh (succ i) else un
  in
  try
    Hashtbl.find heap_var_names v
  with Not_found ->
    let uv = if Hashtbl.mem heap_vars v then fresh 0 else v in
    Hashtbl.add heap_var_names v uv;
    uv

let empty = HeapVarSet.empty
let union = HeapVarSet.union

let add_var v ty s =
  let v = name_heap_var v in
  declare_heap_var v ([], interp_type ty);
  HeapVarSet.add v s
  
let add_alloc s = HeapVarSet.add "alloc" s

let add_field_var v ty s =
   let v = name_heap_var v in
   let _,ty = pointer_heap_var ty in
   declare_heap_var v (memory_type ty);
   HeapVarSet.add v s

let add_pointer_var ty s =
  let v,ty = pointer_heap_array_var ty in
  let v = name_heap_var v in
  declare_heap_var v ty;
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

let assigns_add_var v ty e = { e with assigns = add_var v ty e.assigns }
let assigns_add_field_var v ty e = 
  { e with assigns = add_field_var v ty e.assigns }
let assigns_add_pointer_var ty e = 
  { e with assigns = add_pointer_var ty e.assigns }

let rec term t =
  match t.term_node with 
    | Tvar v -> 
	if v.var_is_static
	then add_var v.var_name t.term_type empty
	else empty
    | Tdot ({term_node = Tunop (Ustar, t1)}, f)
    | Tdot (t1,f)
    | Tarrow (t1,f) -> 
	add_field_var f t.term_type (term t1)
    | Tarrget(t1,t2) ->
	union
	  (add_pointer_var t1.term_type (term t1))
	  (term t2) 
    | Tunop (Ustar, t) ->
	add_pointer_var t.term_type (term t)
    | Tunop (Uminus, t) -> term t
    | Tbase_addr t -> term t
    | Tblock_length t -> add_alloc (term t)
    | Tat (t, _) -> 
	term t
    | Told t -> 
	term t
    | Tif (t1, t2, t3) -> 
	union (term t1) (union (term t2) (term t3))
    | Tbinop (t1, _, t2) -> 
	union (term t1) (term t2) 
    | Tapp (id, l) -> 
	List.fold_left 
	  (fun acc t -> union acc (term t)) 
	  id.logic_args
	  l
    | Tconstant _ -> empty
    | Tnull -> empty
    | Tresult -> empty
    | Tcast (_, t) -> term t

let location loc =
  match loc with
    | Lterm t -> term t 
    | Lstar t ->
	add_pointer_var t.term_type (term t)
    | Lrange(t1,t2,t3) -> 
	add_pointer_var t1.term_type
	  (union 
	     (term t1)
	     (union (term t2) (term t3)))

let locations ll =
  List.fold_left
    (fun acc l -> union acc (location l)) empty ll


let rec predicate p = 
  match p with
    | Ptrue -> empty
    | Pfalse -> empty
    | Papp (id, tl) -> 	
	List.fold_left 
	  (fun acc t -> union acc (term t)) 
	  id.logic_args
	  tl
    | Prel (t1, _, t2) -> union (term t1) (term t2)
    | Pand (p1, p2)
    | Por (p1, p2) 
    | Pimplies (p1, p2) -> union (predicate p1) (predicate p2)
    | Pnot p -> predicate p
    | Pif (t, p1, p2) -> union (term t) (union (predicate p1) (predicate p2))
    | Pforall (_, p) -> predicate p	
    | Pexists (_, p) -> predicate p
    | Pfresh t -> add_alloc (term t)
    | Pvalid t -> add_alloc (term t)
    | Pvalid_index (t1,t2) -> add_alloc (union (term t1) (term t2))
    | Pvalid_range (t1,t2, t3) -> 
	add_alloc (union (term t1) (union (term t2) (term t3)))
    | Pold p -> predicate p
    | Pat (p,_) -> predicate p

let logic_type ls =
  match ls with
    | Clogic.Predicate_reads(args,locs) -> locations locs
    | Clogic.Predicate_def(args,pred) -> predicate pred
    | Clogic.Function(args,ret,locs) -> locations locs


let option f = function None -> empty | Some x -> f x
let ef_option f = function None -> ef_empty | Some x -> f x

let variant (t,_) = term t

let loop_annot a = 
  let r = union (option predicate a.invariant) (option variant a.variant) in
  { reads = r; assigns = empty }

let spec sp = 
  { reads = 
      union 
	(union (option predicate sp.requires) (option predicate sp.ensures))
	(option variant sp.decreases);
    assigns = locations sp.Clogic.assigns }

open Cast

let rec expr e = match e.texpr_node with
  | TEnop
  | TEconstant _
  | TEstring_literal _ 
  | TEsizeof _ ->
      ef_empty
  | TEvar v ->
      if v.var_is_static
      then reads_add_var v.var_name e.texpr_type ef_empty
      else ef_empty
  | TEdot ({texpr_node = TEunary (Ustar, e1)}, f)
  | TEdot (e1, f)
  | TEarrow (e1, f) ->	
      reads_add_field_var f e.texpr_type (expr e1)
  | TEarrget (e1, e2) ->	
      ef_union
	(reads_add_pointer_var e1.texpr_type (expr e1))
	(expr e2) 
  | TEbinary (e1, _, e2) | TEseq (e1, e2) ->
      ef_union (expr e1) (expr e2)
  | TEassign (lv, e) | TEassign_op (lv, _, e) ->
      ef_union (assign_expr lv) (expr e)
  | TEunary (Ustar, e) ->
      reads_add_pointer_var e.texpr_type (expr e)
  | TEunary (Uamp, e) ->
      address_expr e
  | TEunary 
      ((Uplus | Uminus | Unot | Utilde | Ufloat_of_int | Uint_of_float), e) ->
      expr e
  | TEincr (_, e) ->
      assign_expr e
  | TEcall (e, el) ->
      let ef = match e.texpr_node with
	| TEvar v -> { reads = v.function_reads; assigns = v.function_writes } 
	| _ -> expr e
      in
      List.fold_left (fun ef arg -> ef_union (expr arg) ef) ef el
  | TEcond (e1, e2, e3) ->
      ef_union (ef_union (expr e1) (expr e2)) (expr e3)
  | TEcast (_, e) | TEsizeof_expr e ->
      expr e

(* effects for [e = ...] *)
and assign_expr e = match e.texpr_node with
  | TEvar v -> 
      if v.var_is_static
      then assigns_add_var v.var_name e.texpr_type ef_empty
      else ef_empty
  | TEunary (Ustar, e) ->
      assigns_add_pointer_var e.texpr_type (expr e)
  | TEarrget (e1, e2) ->
      ef_union (assigns_add_pointer_var e1.texpr_type (expr e1)) (expr e2) 
  | TEdot ({texpr_node = TEunary (Ustar, e1)}, f)
  | TEdot (e1, f)
  | TEarrow (e1, f) ->
      assigns_add_field_var f e.texpr_type (expr e1)
  | TEcast (_, e1) ->
      assign_expr e1
  | _ -> 
      assert false (* not a left value *)

(* effects for [&e] *)
and address_expr e = match e.texpr_node with
  | TEvar v -> 
      begin match e.texpr_type.ctype_node with
	| CTstruct _ | CTunion _ -> ef_empty
	| _ -> ef_empty (* unsupported "& operator" *)
      end
  | TEunary (Ustar, e1) ->
      expr e1
  | TEarrget (e1, e2) ->
      ef_union (expr e1) (expr e2) 
  | TEdot ({texpr_node = TEunary (Ustar, e1)}, f)
  | TEdot (e1, f)
  | TEarrow (e1, f) ->
      begin match e1.texpr_type.ctype_node with
	| CTenum _ | CTint _ | CTfloat _ -> expr e1
	| _ -> reads_add_field_var f e.texpr_type (expr e1)
      end
  | TEcast (_, e1) ->
      address_expr e1
  | _ -> 
      assert false (* not a left value *)

let rec statement s = match s.st_node with
  | TSnop
  | TSbreak
  | TScontinue
  | TSgoto _ 
  | TSlogic_label _
  | TSreturn None ->
      ef_empty
  | TSexpr e -> 
      expr e
  | TSif (e, s1, s2) -> 
      ef_union (expr e) (ef_union (statement s1) (statement s2))
  | TSwhile (annot, e, s)
  | TSdowhile (annot, s, e) ->
      ef_union (loop_annot annot) (ef_union (statement s) (expr e))
  | TSfor (annot, e1, e2, e3, s) ->
      ef_union (loop_annot annot) (ef_union (ef_union (expr e1) (expr e2))
				     (ef_union (expr e3) (statement s)))
  | TSblock bl ->
      block bl
  | TSreturn (Some e) ->
      expr e
  | TSlabel (_, s) ->
      statement s
  | TSswitch (e, s)
  | TScase (e, s) ->
      ef_union (expr e) (statement s)
  | TSassert p ->
      { reads = predicate p; assigns = empty }
  | TSspec (sp, s) ->
      ef_union (spec sp) (statement s)

and block (dl, sl) =
  let local_decl d = match d.node with
    | Tdecl (_, _, i) -> initializer_ i
    | Ttypedecl _ -> ef_empty
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
    (print_list space pp_print_string) (HeapVarSet.elements l)

let decl d =
  match d.Cast.node with
    | Tlogic(id,ltype) -> 
	let l = logic_type ltype in
	lprintf 
	  "effects of logic declaration of %s: @[%a@]@." id.logic_name
	  print_effects l;
	id.logic_args <- l
    | Taxiom(id,p) -> () (* TODO *)
    | Ttypedef(ctype,id) -> () 
    | Ttypedecl(ctype) -> ()
    | Tdecl(ctype,v,init) -> () (* TODO *)
    | Tfunspec(spec,ctype,id,params) -> () (* TODO *)
    | Tfundef(spec,ctype,id,params,block) -> () (* TODO *)

let file l = List.iter decl l

let functions dl = 
  let fixpoint = ref true in
  let declare id ef =
    lprintf "effects for function %s: reads %a writes %a@." id.var_name 
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
    | Tfunspec (sp, _, id, _) ->
	declare id (spec sp)
    | Tfundef (sp, _, id, _, s) ->
	declare id (ef_union (spec sp) (statement s))
    | _ -> 
	()
  in
  List.iter decl dl;
  !fixpoint

