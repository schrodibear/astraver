open Cenv
open Cast
open Clogic
open Info
open Ctypes

let in_struct v1 v = 
 	{ texpr_node = TEdot (v1, v); 
	  texpr_loc = v1.texpr_loc;
	  texpr_type = v.var_type }

let split_decl e ((invs,inits) as acc) = 
  match e.node with 
    | Tinvariant (_,p) -> (p :: invs, inits)
    | Tdecl (t, v, c) ->  (invs, e :: inits)
    | _ -> acc

let split_decls d = List.fold_right split_decl d ([],[])

let dummy_pred p = { pred_node = p; pred_loc = Loc.dummy_position }

let rec combine_inv = function
  | [] -> dummy_pred Ptrue
  | a::[] -> a
  | a::l -> { a with pred_node = Pand (a, combine_inv l) }


let noattr loc ty e =
  { texpr_node = e;
    texpr_type = ty;
    texpr_loc  = loc
  }

let rec pop_initializer loc t i =
  match i with 
    | [] ->{ texpr_node = 
	       (match t.ctype_node with
		  | Tint _ | Tenum _-> TEconstant (IntConstant "0")
		  | Tfloat _ -> TEconstant (RealConstant "0.0")
		  | Tpointer _ -> TEcast (t, Ctyping.tezero)
		  | _ -> assert false);
	     texpr_type = t;
	     texpr_loc  = loc
	    },[]
    | (Iexpr e)::l -> e,l
    | (Ilist [])::l -> pop_initializer loc t l
    | (Ilist l)::l' -> 
	let e,r = pop_initializer loc t l in e,r@l'

let rec init_expr loc t lvalue initializers =
  match t.ctype_node with
    | Tint _ | Tfloat _ | Tpointer _ | Tenum _ -> 
	let x,l = pop_initializer loc t initializers in
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
		(fun (acc,init)  f -> 
		   let block, init' =
		     init_expr loc f.var_type 
		       (in_struct lvalue f) init
		   in (acc@block,init'))
		([],initializers)  fl
	  | _ ->
	      assert false
	end
    | Tunion n ->
	begin match tag_type_definition n with
	  | TTStructUnion (Tunion (_), f::_) ->
	      let block, init' =
		init_expr loc f.var_type 
		  (noattr loc f.var_type (TEarrow(lvalue, f)))
		  initializers
	      in (block,init')
	  | _ ->
	      assert false
	end
    | Tarray (_,ty,Some t) ->
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
    | Tarray (_,ty,None) -> assert false
    | Tfun (_, _) -> assert false
    | Tvar _ -> assert false
    | Tvoid -> [],initializers


let rec assigns decl =
  match decl with
    | [] -> []
    | {node = Tdecl (t,v,None); loc = l}::decl ->
	Coptions.lprintf "initialization of %s@." v.var_name;
	let declar,_ = init_expr l t (noattr l t (TEvar (Var_info v))) [] in
	declar @ (assigns decl)
    | {node = Tdecl(t, v, Some c) ; loc = l }:: decl ->
	Coptions.lprintf "initialization of %s@." v.var_name;
	let declar,_ = init_expr l t (noattr l t (TEvar (Var_info v))) [c] in
	declar @ (assigns decl)
    | _  -> assert false


let invariants_initially_established_info =
  default_fun_info "invariants_initially_established"

let rec reorder l =
  match l with 
    | { node = Tdecl _ }as e ::l  -> let decl,other = reorder l in
      e::decl,other
    | e::l -> let decl,other = reorder l in
      decl,e::other
    | [] -> [],[]

let user_invariants = ref false

let add_init l = 
  let (inv,decl) = split_decls l in
  if inv = [] then user_invariants := false
  else user_invariants := true;
  let inv = combine_inv inv in
  let init_fun =
    Tfundef ({requires = None;
	      assigns = None;
	      ensures = Some inv; 
		decreases = None},
	     c_void,
	     invariants_initially_established_info,
	     {st_node = TSblock ([], assigns decl);
	      st_break = false;    
	      st_continue = false; 
	      st_return = false;   
		st_term = true;     
		st_loc = Loc.dummy_position 
	     })
  in
  let decl,other = 
    reorder ({ node = init_fun; loc = Loc.dummy_position } :: l) in
  decl@other
