
open Cast
open Clogic
open Info
open Format
open Pp
open Output

let interp_type ctype =
  match ctype.ctype_node with
  | CTvoid -> "unit"
  | CTint(sign,cint) -> "int"
  | CTfloat(cfloat) -> "float"
  | CTarray(t,None) -> "pointer"      
  | CTarray(t,Some e) -> "pointer"
  | CTpointer(t) -> "pointer"      
  | _ -> assert false (* TODO *)
(*
  | CTvar of string
  | CTstruct_named of string
  | CTstruct of string * 'expr field list
  | CTunion_named of string
  | CTunion of string * 'expr field list
  | CTenum_named of string
  | CTenum of string * (string * 'expr option) list
  | CTfun of 'expr parameter list * 'expr ctype
*)



type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

let rec pointer_heap_var ty =
  match ty.ctype_node with
    | CTvar v -> assert false (* should have been expanded *)
    | CTvoid -> failwith "void * not supported"
    | CTint _ -> "int", "int"
    | CTfloat _ -> "float", "float"
    | CTarray (ty,_)
    | CTpointer ty ->
	let v,_ = pointer_heap_var ty in
	( v ^ "P", "pointer")
    | CTstruct _ -> "pointer", "pointer"
    | CTunion _ -> "pointer", "pointer"
    | CTenum _ -> "int", "int"
    | CTfun _ -> assert false (* bad typing ! *)

let memory_type t = ([t],"memory")

let pointer_heap_array_var ty =
  match ty.ctype_node with
    | CTarray (ty,_)
    | CTpointer ty ->
	let v,ty = pointer_heap_var ty in
	( v ^ "P", memory_type ty)
    | _ -> assert false (* location wrongly typed *)


let rec term t =
  match t.term_node with 
    | Tvar v -> 
	if v.var_is_static
	then HeapVarSet.singleton (v.var_name, ([],interp_type t.term_type)) 
	else HeapVarSet.empty
    | Tarrow(t,f) -> 
	HeapVarSet.add (f,([],interp_type t.term_type)) 
	  (HeapVarSet.add (pointer_heap_array_var t.term_type)
	     (term t))
    | Tdot(t,f) -> 
	HeapVarSet.add (f,([],interp_type t.term_type)) (term t)
    | Tarrget(t1,t2) ->
	HeapVarSet.union
	  (HeapVarSet.add (pointer_heap_array_var t1.term_type) (term t1))
	  (term t2) 
    | Tunop (Ustar, t) ->
	HeapVarSet.add (pointer_heap_array_var t.term_type) (term t)
    | Tunop (_,_) -> assert false (* TODO *)
    | Tlength _ -> assert false (* TODO *)
    | Tat (_, _) -> assert false (* TODO *)
    | Told _ -> assert false (* TODO *)
    | Tif (_, _, _) -> assert false (* TODO *)
    | Tbinop (t1, _, t2) -> 
	HeapVarSet.union (term t1) (term t2) 
    | Tapp (id, l) -> 
	List.fold_left 
	  (fun acc t -> HeapVarSet.union acc (term t)) 
	  id.logic_args
	  l
    | Tconstant _ -> HeapVarSet.empty
    | Tnull -> assert false (* TODO *)
    | Tresult -> assert false (* TODO *)
    | Tcast _ -> assert false (* TODO *)

let location loc =
  match loc with
    | Lterm t -> term t 
    | Lstar t ->
	HeapVarSet.add (pointer_heap_array_var t.term_type) (term t)
    | Lrange(t1,t2,t3) -> 
	HeapVarSet.add (pointer_heap_array_var t1.term_type)
	  (HeapVarSet.union 
	     (term t1)
	     (HeapVarSet.union (term t2) (term t3)))

let locations ll =
  List.fold_left
    (fun acc l -> HeapVarSet.union acc (location l)) HeapVarSet.empty ll


let logic_type ls =
  match ls with
    | Clogic.Predicate_reads(args,locs) -> locations locs
    | Clogic.Predicate_def(args,pred) -> assert false (* TODO *)
    | Clogic.Function(args,ret,locs) -> locations locs

let decl d =
  match d.Cast.node with
    | Tlogic(id,ltype) -> 
	let l = logic_type ltype in
	fprintf Coptions.log 
	  "effects of logic declaration of %s: %a@." id.logic_name
	  (print_list space pp_print_string) 
	  (List.map fst (HeapVarSet.elements l));
	id.logic_args <- l
    | Taxiom(id,p) -> () (* TODO *)
    | Ttypedef(ctype,id) -> assert false (* TODO *)
    | Ttypedecl(ctype) -> assert false (* TODO *)
    | Tdecl(ctype,v,init) -> () (* TODO *)
    | Tfunspec(spec,ctype,id,params) -> assert false (* TODO *)
    | Tfundef(spec,ctype,id,params,block,info) -> () (* TODO *)



let rec predicate p = 
  match p with
    | Ptrue -> HeapVarSet.empty
    | Pfalse -> assert false (* TODO *)
    | Papp (_, _) -> assert false (* TODO *)
    | Prel (t1, _, t2) -> 
	HeapVarSet.union (term t1) (term t2)
    | Pand (_, _) -> assert false (* TODO *)
    | Por (_, _) -> assert false (* TODO *)
    | Pimplies (_, _) -> assert false (* TODO *)
    | Pnot _ -> assert false (* TODO *)
    | Pif (_, _, _) -> assert false (* TODO *)
    | Pforall (_, p) -> predicate p	
    | Pexists (_, _) -> assert false (* TODO *)
    | Pvalid (_) -> assert false (* TODO *)
    | Pvalid_range (_, _, _) -> assert false (* TODO *)
    | Pold _ -> assert false (* TODO *)
    | Pat (_,_) -> assert false (* TODO *)

let file l = List.iter decl l

