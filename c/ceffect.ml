
module StringSet = Set.Make(String)

open Cast
open Clogic
open Info
open Format
open Pp

type effect =
    {
      reads : StringSet.t;
      assigns : StringSet.t;
    }

let rec pointer_heap_var ty =
  match ty.ctype_node with
    | CTvar v -> assert false (* should have been expanded *)
    | CTvoid -> failwith "void * not supported"
    | CTint _ -> "int"
    | CTfloat _ -> "float"
    | CTarray (ty,_)
    | CTpointer ty ->
	(pointer_heap_var ty) ^ "P"
    | CTstruct _ -> "pointer"
    | CTunion _ -> "pointer"
    | CTenum _ -> "int"
    | CTfun _ -> assert false (* bad typing ! *)
  

let rec term t acc =
  match t.node with 
    | Tvar v -> 
	if v.var_is_static
	then StringSet.add v.var_name acc
	else acc
    | Tarrow(t,f) -> 
	term t (StringSet.add f 
		  (StringSet.add (pointer_heap_var t.info) acc))
    | Tdot(t,f) -> term t (StringSet.add f acc)
    | Tarrget(t1,t2) ->
	term t1 
	(term t2 
	   (StringSet.add (pointer_heap_var t1.info) acc))	
    | Tunop (Ustar, t) ->
	term t (StringSet.add (pointer_heap_var t.info) acc)
    | _ -> assert false (* bad parsing ??? *)

let location loc =
  match loc with
    | Lterm t -> term t StringSet.empty
    | Lstar t -> term t (StringSet.singleton (pointer_heap_var t.info))
    | Lrange(t1,t2,t3) -> 
	term t1 
	(term t2 
	   (term t3 
	      (StringSet.singleton (pointer_heap_var t1.info))))

let locations ll =
  List.fold_left
    (fun acc l -> StringSet.union acc (location l)) StringSet.empty ll


let logic_type ls =
  match ls with
    | Clogic.Predicate_reads(args,locs) -> locations locs
    | Clogic.Predicate_def(args,pred) -> assert false (* TODO *)
    | Clogic.Function(args,ret,locs) -> locations locs

let decl d =
  match d.Cast.node with
    | Tlogic(id,ltype) -> 
	let l = StringSet.elements (logic_type ltype) in
	fprintf Coptions.log 
	  "effects of logic declaration of %s: %a@." id.logic_name
	  (print_list space pp_print_string) l;
	id.logic_args <- l
    | Taxiom(id,p) -> () (* TODO *)
    | Ttypedef(ctype,id) -> assert false (* TODO *)
    | Ttypedecl(ctype) -> assert false (* TODO *)
    | Tdecl(ctype,v,init) -> () (* TODO *)
    | Tfunspec(spec,ctype,id,params) -> assert false (* TODO *)
    | Tfundef(spec,ctype,id,params,block,info) -> () (* TODO *)

let file l = List.iter decl l

