
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


module HeapVarSet = Set.Make
 (struct type t = string * Output.base_type
	 let compare (a,_) (b,_) = String.compare a b end)

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


let rec term t acc =
  match t.node with 
    | Tvar v -> 
	if v.var_is_static
	then HeapVarSet.add (v.var_name, ([],interp_type t.info)) acc
	else acc
    | Tarrow(t,f) -> 
	term t (HeapVarSet.add (f,([],interp_type t.info)) 
		  (HeapVarSet.add (pointer_heap_array_var t.info) acc))
    | Tdot(t,f) -> term t (HeapVarSet.add (f,([],interp_type t.info)) acc)
    | Tarrget(t1,t2) ->
	term t1 
	(term t2 
	   (HeapVarSet.add (pointer_heap_array_var t1.info) acc))	
    | Tunop (Ustar, t) ->
	term t (HeapVarSet.add (pointer_heap_array_var t.info) acc)
    | _ -> assert false (* bad parsing ??? *)

let location loc =
  match loc with
    | Lterm t -> term t HeapVarSet.empty
    | Lstar t -> term t (HeapVarSet.singleton (pointer_heap_array_var t.info))
    | Lrange(t1,t2,t3) -> 
	term t1 
	(term t2 
	   (term t3 
	      (HeapVarSet.singleton (pointer_heap_array_var t1.info))))

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
	let l = HeapVarSet.elements (logic_type ltype) in
	fprintf Coptions.log 
	  "effects of logic declaration of %s: %a@." id.logic_name
	  (print_list space pp_print_string) (List.map fst l);
	id.logic_args <- l
    | Taxiom(id,p) -> () (* TODO *)
    | Ttypedef(ctype,id) -> assert false (* TODO *)
    | Ttypedecl(ctype) -> assert false (* TODO *)
    | Tdecl(ctype,v,init) -> () (* TODO *)
    | Tfunspec(spec,ctype,id,params) -> assert false (* TODO *)
    | Tfundef(spec,ctype,id,params,block,info) -> () (* TODO *)

let file l = List.iter decl l

