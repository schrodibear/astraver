open Cenv
open Cast
open Clogic
open Info
open Ctypes

let split_decl e ((invs,inits) as acc) = 
  match e.node with 
    | Tinvariant (_,p) -> (p :: invs, inits)
    | Tdecl (t, v, c) ->  (invs, e :: inits)
    | _ -> acc

let split_decls d = List.fold_right split_decl d ([],[])

let rec combine_inv = function
  | [] -> Ptrue
  | a::[] -> a
  | a::l -> Pand (a, combine_inv l)


let noattr loc ty e =
  { texpr_node = e;
    texpr_type = ty;
    texpr_loc  = loc
  }

let rec pop_initializer i =
  match i with 
    | [] -> raise Not_found
    | (Iexpr e)::l -> e,l
    | (Ilist [])::l -> pop_initializer l
    | (Ilist l)::l' -> 
	let e,r = pop_initializer l in e,r@l'

let rec init_expr loc t lvalue initializers =
  match t.ctype_node with
    | Tint _ | Tfloat _ | Tpointer _ -> 
	let x,l = pop_initializer initializers in
	[{st_node =TSexpr (noattr loc t (TEassign(lvalue,x)));
	  st_break = false;    
	  st_continue = false; 
	  st_return = false;   
	  st_term = true;
	  st_loc = loc     
	 }], l
    | Tstruct n ->
	begin match tag_type_definition n with
	  | TTStructUnion (Tstruct (_), fl) ->
	      List.fold_left 
		(fun (acc,init) (tyf, f) -> 
		   let block, init' =
		     init_expr loc tyf 
		       (noattr loc tyf (TEarrow(lvalue, find_field n f))) init
		   in (acc@block,init'))
		([],initializers)  fl
	  | _ ->
	      assert false
	end
    | Tunion n ->
	begin match tag_type_definition n with
	  | TTStructUnion (Tstruct (_), (tyf,f)::_) ->
	      let block, init' =
		init_expr loc tyf 
		  (noattr loc tyf (TEarrow(lvalue, find_field n f)))
		  initializers
	      in (block,init')
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
	init_cells Int64.zero ([],initializers)
    | Tarray (ty,None) -> assert false
    | Tfun (_, _) -> assert false
    | Tenum _ -> assert false
    | Tvar _ -> assert false
    | Tvoid -> assert false


let rec assigns decl =
  match decl with
    | [] -> []
    | {node = Tdecl (_,_,None)}::decl -> assigns decl
    | {node = Tdecl(t, v, Some c) ; loc = l }:: decl ->
	Coptions.lprintf "translating global declaration of %s@." v.var_name;
	let declar,_ = init_expr l t (noattr l t (TEvar (Var_info v))) [c] in
	declar @ (assigns decl)
    | _  -> assert false


let invariants_initially_established_info =
  default_fun_info "invariants_initially_established"

let add_init l = 
  let (inv,decl) = split_decls l in
  let inv = combine_inv inv in
  let init_fun =
    Tfundef ({requires = None;
	      assigns = None;
	      ensures = Some inv; 
	      decreases = None},
	     {ctype_node = Tvoid;
	      ctype_storage = No_storage;
	      ctype_const = false;
	      ctype_volatile = false},
	     invariants_initially_established_info,
	     [],
	     {st_node = TSblock ([], assigns decl);
	     st_break = false;    
	     st_continue = false; 
	     st_return = false;   
	     st_term = true;     
	     st_loc =Loc.dummy 
	    })
  in
  { node = init_fun; loc = Loc.dummy } :: l
