
open Info
open Cast

let debug = true
let debug_more = true

(* wrap treatment on option *)
module Option = struct
  let map f x = match x with None -> None | Some s -> Some (f s)
  let equal f x1 x2 = match x1,x2 with
    | None,None -> true
    | Some y1,Some y2 -> f y1 y2
    | _ -> false
end

(* to avoid warnings about missing cases in pattern-matching,
   when exact form of the list known due to context *)
let list1 l = match l with
  | [a] -> a
  | _ -> assert false
let list2 l = match l with
  | [a;b] -> a,b
  | _ -> assert false
let list3 l = match l with
  | [a;b;c] -> a,b,c
  | _ -> assert false
let list4 l = match l with
  | [a;b;c;d] -> a,b,c,d
  | _ -> assert false


(*****************************************************************************
 *                                                                           *
 * 		Pointer kinds used for local aliasing analysis               *
 *                                                                           *
 *****************************************************************************)

module type Variable = sig
  type t
  val pretty : Format.formatter -> t -> unit
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

module type Lattice = sig
  type t
  type var_t
  val top : t
  val bottom : t
  val equal : t -> t -> bool
  val pretty : Format.formatter -> t -> unit
  val join : t -> t -> t    
end

module type PointerLattice = sig
  include Lattice
    (* in the following, an [alias] is the same as an [index] of 0.
       It is provided for the sake of simplicity. *)
    (* constructors *)
  val make_alias : var_t -> t
  val make_index : var_t -> int -> t
  val make_offset : var_t -> var_t option -> t
  val make_defined : var_t -> var_t option -> t
    (* query functions *)
  val is_alias : t -> bool
  val is_index : t -> bool
  val is_self_index : var_t -> t -> bool
  val is_offset : t -> bool
  val is_self_offset : var_t -> t -> bool
  val is_defined : t -> bool
  val is_top : t -> bool
    (* destructors *)
  val get_alias : t -> var_t
  val get_index : t -> var_t * int
  val get_offset_opt : t -> var_t * var_t option
  val get_offset : t -> var_t * var_t
  val get_defined_opt : t -> var_t * var_t option
  val get_variable : t -> var_t
end

module Make_PtrLattice(V : Variable) : PointerLattice with type var_t = V.t
  = struct

  type var_t = V.t

  (* different kinds of pointers, depending on their local aliasing,
     obtained through assignments. 
     Only relevant for local variables, i.e. parameters and locals, 
     because globals could be modified inside a function call. *)
  type t =
        (* result of join between incompatible pointers on different paths *)
    | PKcomplex
	(* not known offset from local/global variable or parameter.
	   The optional variable will be set during the analysis to be 
	   an integer variable containing the actual offset. *)
    | PKoffset of V.t * V.t option
	(* known index from local/global variable or parameter.
	   In the particular case of a 0 index, it represents an alias of 
	   a local/global variable or parameter. *)
    | PKindex of V.t * int 
	(* defined pointer, but definition was too complex to be classified
	   as an offset or an index pointer. 
	   The 1st variable allows for a common treatment with other kinds.
	   The optional variable will be possibly set during the analysis 
	   to be an integer variable containing an offset to reset to 0
	   when assigning the pointer variable.
	   Conceptually, [PKdefined] is not far from [PKindex] on the same 
	   variable with index 0. *)
    | PKdefined of V.t * V.t option
	(* undefined pointer *)
    | PKundefined

  let top = PKcomplex
  let bottom = PKundefined

  (* get underlying variable if any *)
  let get_var_opt p1 = match p1 with
    | PKundefined | PKcomplex -> None
    | PKindex (v,_) | PKoffset (v,_) | PKdefined (v,_) -> Some v

  let same_var p1 p2 = match get_var_opt p1,get_var_opt p2 with
    | Some v1,Some v2 -> V.compare v1 v2 = 0
    | _ -> false

  let is_not_self_index_offset p = match p with
    | PKindex _ | PKoffset _ -> true
    | _ -> false

  (* constructors *)
  let make_alias v = PKindex (v,0)
  let make_index v i = PKindex (v,i)
  let make_offset v vo = PKoffset (v,vo)
  let make_defined v vo = PKdefined (v,vo)

  (* query functions *)
  let is_alias t = match t with PKindex (_,0) -> true | _ -> false
  let is_index t = match t with PKindex _ -> true | _ -> false
  let is_self_index var t = 
    match t with PKindex (v,_) -> V.equal var v | _ -> false
  let is_offset t = match t with PKoffset _ -> true | _ -> false
  let is_self_offset var t = 
    match t with PKoffset (v,_) -> V.equal var v | _ -> false
  let is_defined t = match t with PKdefined _ -> true | _ -> false
  let is_top t = match t with PKcomplex -> true | _ -> false

  (* destructors *)
  let get_alias t = match t with 
    | PKindex (v,0) -> v 
    | _ -> assert false
  let get_index t = match t with 
    | PKindex (v,i) -> v,i 
    | _ -> assert false
  let get_offset_opt t = match t with 
    | PKoffset (v,vo) -> v,vo 
    | _ -> assert false
  let get_offset t = match t with 
    | PKoffset (v,o) ->
	begin match o with
	  | Some off -> v,off
	  | _ -> 
	      (* when querying an [offset] pointer kind, we expect 
		 the offset variable to be set *)
	      assert false
	end
    | _ -> assert false
  let get_defined_opt t = match t with 
    | PKdefined (v,vo) -> v,vo 
    | _ -> assert false
  let get_variable t = match t with
    | PKindex _ -> fst (get_index t)
    | PKoffset _ -> fst (get_offset_opt t)
    | PKdefined _ -> fst (get_defined_opt t)
    | _ -> assert false

  let equal p1 p2 = match p1,p2 with
    | PKundefined,PKundefined -> true
    | PKindex (v1,o1),PKindex (v2,o2) ->
	V.equal v1 v2 && o1 = o2
    | PKoffset (v1,o1),PKoffset (v2,o2)
    | PKdefined (v1,o1),PKdefined (v2,o2) ->
	V.equal v1 v2 && (Option.equal V.equal o1 o2)
    | PKcomplex,PKcomplex -> true
    | _ -> false

  let pretty fmt t = match t with
    | PKundefined -> Format.fprintf fmt "PKundefined"
    | PKindex (v,i) -> Format.fprintf fmt "PKindex(%a,%d)" V.pretty v i
    | PKoffset (v,o) -> 
	begin
	  match o with
	    | None -> Format.fprintf fmt "PKoffset(%a)" V.pretty v
	    | Some vo -> 
		Format.fprintf fmt "PKoffset(%a,%a)" V.pretty v V.pretty vo
	end
    | PKdefined (v,o) ->
	begin
	  match o with
	    | None -> Format.fprintf fmt "PKdefined(%a)" V.pretty v
	    | Some vo -> Format.fprintf 
		fmt "PKdefined(%a,%a)" V.pretty v V.pretty vo
	end
    | PKcomplex -> Format.fprintf fmt "PKcomplex"

  (* lattice associated to var [v] has the following form:

                              PKcomplex
                                   |
                              PKoffset(v,o)
                                   |
                              PKindex(v,i)
                                   |
                              PKdefined(v,o)
                                   |
                              PKundefined

     2 different lattices for [u] and [v] only connect at top and bottom.
  *)

  (* 2 pointer kinds are comparable only if they have the same underlying 
     variable, if any. The opposite is true too, except for pairs of the same
     pointer kind with different second argument. 
     A subtlety is that a PKdefined pointer is comparable to a PKindex one
     only if the index is 0. *)
  let comparable p1 p2 = match get_var_opt p1,get_var_opt p2 with
    | Some v1,Some v2 -> 
	let second_arg_same = 
	  if is_offset p1 && (is_offset p2) then
	    let o1 = snd (get_offset_opt p1) in
	    let o2 = snd (get_offset_opt p2) in
	    Option.equal V.equal o1 o2
	  else if is_index p1 && (is_index p2) then
	    let o1 = snd (get_index p1) in
	    let o2 = snd (get_index p2) in
	    o1 = o2
	  else if is_defined p1 && (is_defined p2) then
	    let o1 = snd (get_defined_opt p1) in
	    let o2 = snd (get_defined_opt p2) in
	    Option.equal V.equal o1 o2
	  else true
	in
	let defined_with_index0 =
	  if is_defined p1 || (is_defined p2) then
	    if is_index p1 then snd (get_index p1) = 0
	    else if is_index p2 then snd (get_index p2) = 0
	    else true
	  else true
	in
	V.compare v1 v2 = 0 && second_arg_same && defined_with_index0
    | _ -> true

  (* p1 <= p2 *)
  let inf p1 p2 = 
    comparable p1 p2 &&
      match p1,p2 with
            (* PKundefined is the bottom element *)
	| PKundefined,_ -> true
	| _,PKundefined -> false
	    (* PKdefined is the next lowest element *)
	| PKdefined _,_ -> true
	| _,PKdefined _ -> false
	    (* PKindex is the next lowest element *)
	| PKindex _,_ -> true
	| _,PKindex _ -> false
	    (* PKoffset is the next lowest element *)
	| PKoffset _,_ -> true
	| _,PKoffset _ -> true
	    (* PKcomplex is the top element *)
	| PKcomplex,PKcomplex -> true

  (* union *)
  let rec join p1 p2 = 
    if not (comparable p1 p2) then 
      if same_var p1 p2 then
	(* case of interest here is 2 PKindex with different indices,
	   or equivalently a PKdefined with a PKindex of index different 
	   from 0 *)
	let v = get_variable p1 in
	PKoffset (v,None)
      else
	PKcomplex
    else if inf p2 p1 && not (equal p2 p1) then join p2 p1 else
      (* only treat here the case where p1 <= p2 *)
      match p1,p2 with
          (* PKundefined is the bottom element *)
	| PKundefined,p -> p
	    (* PKdefined is the next lowest element *)
	| PKdefined _,p -> p
	    (* PKindex is the next lowest element *)
	| PKindex _,p -> p
	    (* PKoffset is the next lowest element *)
	| PKoffset _,p -> p
	    (* PKcomplex is the top element *)
	| PKcomplex,_ -> PKcomplex

end

module type PointWiseLattice = sig
  include Lattice
  type value_t
  type map_t
    (* replace ignores the value already present for this variable, if any *)
  val replace : var_t -> value_t -> t -> t
    (* [add] performs a join if a value was already present for this variable, 
       otherwise a simple add *)
  val add : var_t -> value_t -> t -> t
    (* [addmap] performs an [add] for every entry in the map *)
  val addmap : map_t -> t -> t
    (* [find] never raises an exception, returns the bottom value to signify 
       the variable was not found *)
  val find : var_t -> t -> value_t
    (* [iter] not defined for [top] value *)
  val iter : (var_t -> value_t -> unit) -> t -> unit
    (* [fold] not defined for [top] value *)
  val fold : (var_t -> value_t -> 'a -> 'a) -> t -> 'a -> 'a
  val mapi : (var_t -> value_t -> value_t) -> t -> t
end

module Make_PointWiseLattice
  (V : Variable) (VMap : Map.S with type key = V.t) (L : Lattice)
  : PointWiseLattice with type var_t = V.t and type value_t = L.t 
  = struct

  type var_t = V.t
  type value_t = L.t
  type map_t = L.t VMap.t 

  type t =
    | PWempty
    | PWmap of L.t VMap.t
    | PWall

  let bottom = PWempty
  let top = PWall

  let equal pw1 pw2 = match pw1,pw2 with
    | PWempty,PWempty -> true
    | PWmap m1,PWmap m2 -> VMap.equal L.equal m1 m2
    | PWall,PWall -> true
    | _ -> false

  let pretty fmt pw = match pw with
    | PWempty -> Format.fprintf fmt "PWempty"
    | PWmap m -> Format.fprintf fmt "PWmap{%a}"
	(fun fmt m -> VMap.iter 
	   (fun v a -> Format.fprintf fmt "(%a,%a); " 
	      V.pretty v L.pretty a) m) m
    | PWall -> Format.fprintf fmt "PWall"

  let replace var value pw = match pw with
    | PWempty -> PWmap (VMap.add var value VMap.empty)
    | PWmap m -> PWmap (VMap.add var value m)
    | PWall -> PWall

  let find var pw = match pw with
    | PWempty -> L.bottom
    | PWmap m ->
	begin 
	  try VMap.find var m with Not_found -> L.bottom
	end
    | PWall -> L.top

  let add var value pw = match pw with
    | PWempty -> PWmap (VMap.add var value VMap.empty)
    | PWmap m -> 
	let new_value = L.join value (find var pw) in
	PWmap (VMap.add var new_value m)
    | PWall -> PWall

  let addmap m1 pw = match pw with
    | PWempty -> PWmap m1
    | PWmap m2 -> 
	(* add all elements of [m1] in [m2] *)
	VMap.fold add m1 pw
    | PWall -> PWall

  (* ideally, [pw2] should be smaller than [pw1] when adding maps *)
  let join pw1 pw2 = match pw1,pw2 with
    | PWempty,pw | pw,PWempty -> pw
    | PWall,_ | _,PWall -> PWall
    | PWmap m1,PWmap m2 -> 
	(* add all elements of [m2] in [m1] *)
	addmap m2 pw1
    
  let iter f pw = match pw with
    | PWempty -> ()
    | PWmap m -> VMap.iter f m
    | PWall -> failwith "[iter] should not be called on [PWall]"

  let fold f pw init = match pw with
    | PWempty -> init
    | PWmap m -> VMap.fold f m init
    | PWall -> failwith "[fold] should not be called on [PWall]"

  let mapi f pw = match pw with
    | PWempty -> PWempty
    | PWmap m -> PWmap (VMap.mapi f m)
    | PWall -> PWall

end


(*****************************************************************************
 *                                                                           *
 * 		Abstract interpretation of local aliasing                    *
 *                                                                           *
 *****************************************************************************)

(* gives operations on a control-flow graph *)

module type InterLang = sig
  type var_t
  type decl_t

  (* type of declaration/statement/expression in the intermediate language *)
  module Node : sig
    type t
    val compare : t -> t -> int
    val pretty : Format.formatter -> t -> unit
  end

  (* successors in both structural and operational graph *)
  (* first successor in the structural graph, if any *)
  val child : Node.t -> Node.t option
    (* list of successors in the structural graph, e.g.
       - list of operands of an operation
       - caller and arguments of a function call
       - list of statements in a block statement 
       ... 
    *)
  val children : Node.t -> Node.t list (* order matters *)
    (* list of successors in the operational graph, e.g.
       - surrounding expression for a sub-expression
       - [else] and [then] branches for an [if] test expression
       ... 
    *)
  val successors : Node.t -> Node.t list (* order does not matter *)
    (* list of predecessors in the operational graph *)
  val predecessors : Node.t -> Node.t list (* order does not matter *)

  (* query functions *)
  (* 4 kinds of nodes: expression/statement/declaration/internal *)
  type node_kind = NKexpr | NKstat | NKdecl | NKnone
    (* returns the node's kind *)
  val get_node_kind : Node.t -> node_kind
    (* returns the function's parameters *)
  val decl_get_params : Node.t -> var_t list
    (* is it a return statement ? *)
  val stat_is_return : Node.t -> bool
    (* is the type of this expression a pointer type ? *)
  val expr_type_is_ptr : Node.t -> bool
    (* is this expression a -local- variable ? *)
  val expr_is_local_var : Node.t -> bool
    (* is this expression a -local- variable of pointer type ? *)
  val expr_is_local_ptr_var : Node.t -> bool
    (* returns the variable in this expression over a variable *)
  val expr_var_get_var : Node.t -> var_t
    (* is this expression an assignment ? *)
  val expr_is_assign : Node.t -> bool
    (* is this expression a pointer assignment ? *)
  val expr_is_ptr_assign : Node.t -> bool
    (* if the left-hand side of this pointer assignment is a -local- variable, 
       return it *)
  val ptr_assign_get_local_lhs_var : Node.t -> var_t option
    (* if the right-hand side of this pointer assignment is a variable, 
       return it, with an optional constant offset if known.
       Only when [ptr_assign_get_local_lhs_var] has been called before
       with success. *)
  val ptr_assign_get_rhs_var : Node.t -> var_t option * int option
    (* takes a variable expression or an addition of an expression
       and an offset.
       returns as 1st item the possible variable in the addition.
       returns as 2nd item the possible offset expression in the addition. *)
  val get_ptr_add_on_var_opt : Node.t -> var_t option * Node.t option
    (* is this variable a pointer ? *)
  val var_is_pointer : var_t -> bool
    (* is this a local variable ? *)
  val var_is_local : var_t -> bool

  (* constructors.
     - [make_] functions operate directly on their arguments.
     - [change_] functions take a first node as context, and operate on 
     other arguments.
  *)
  (* create a new sequence expression node *)
  val make_seq_expr : Node.t -> Node.t -> Node.t
    (* create a new node expression + constant *)
  val make_int_expr_add_cst : Node.t -> int -> Node.t
    (* create a new node expression + variable *)
  val make_int_expr_add_var : Node.t -> var_t -> Node.t
    (* create a new node expression + expression *)
  val make_int_expr_add_expr : Node.t -> Node.t -> Node.t
    (* create a new node pointer expression + constant *)
  val make_ptr_expr_add_cst : Node.t -> int -> Node.t
    (* make this node be an expression over a variable *)
  val change_in_var : Node.t -> var_t -> Node.t
    (* make this node be a sum variable + constant *)
  val change_in_ptr_var_add_cst : Node.t -> var_t -> int -> Node.t
    (* make this node be a sum variable + variable *)
  val change_in_ptr_var_add_var : Node.t -> var_t -> var_t -> Node.t
    (* make this node be a sum variable + expression *)
  val change_in_ptr_var_add_expr : Node.t -> var_t -> Node.t -> Node.t
    (* make this node be an assignment variable = constant *)
  val change_in_var_assign_cst : Node.t -> var_t -> int -> Node.t
    (* make this node be an assignment variable = variable *)
  val change_in_var_assign_var : Node.t -> var_t -> var_t -> Node.t
    (* make this node be an assignment variable = expression *)
  val change_in_var_assign_expr : Node.t -> var_t -> Node.t -> Node.t
    (* make this node be an increment/decrement of the 2nd node,
       materialized as a pointer addition.
       The boolean is [true] if the function is called on the result of
       the assignment, to get back a pointer expression for the evaluation
       of the increment/decrement expression.
       The boolean is [false] if the function is called before the assignment,
       to get the result of the increment/decrement evaluation. *)
  val change_in_ptr_incr : Node.t -> Node.t -> bool -> Node.t
    (* make this node be an increment/decrement of the variable,
       materialized as an integer addition, that is asssigned to
       the 1st node *)
  val change_in_int_incr_assign : Node.t -> var_t -> Node.t
    (* change the structural sub-components of this node *)
  val change_sub_components : Node.t -> Node.t list -> Node.t 
    (* add new local variables to this declaration node.
       The boolean is [true] if the variables are zero-initialized. *)
  val introduce_new_vars : Node.t -> var_t list -> bool -> Node.t

  (* language interface *)
  (* returns a pair of the list of roots + the list of elements in the graph *)
  val from_file : decl_t list -> Node.t list * Node.t list
  val to_file : Node.t list -> decl_t list
end

(* defines program points where result of analysis is useful *)
  
module type WatchPoint = sig
  (* replicates type of InterLang *)
  type node_t
    (* defines watch-points *)
  val is_watch_node : node_t -> bool
end
  
(* connects the concrete and the abstract levels *)
  
module type Connection = sig
  (* replicates type of InterLang *)
  type node_t
    (* type of abstract value map *)
  type absval_t
    (* type of a map from variables to their offset variable *)
  type map_t
    (* result of analysis is an association from nodes to abstract values.
       First abstract value is the value before the node is entered.
       Second abstract value is the value after the node is exited. *)
  type analysis_t = (node_t, absval_t * absval_t) Hashtbl.t
    (* transfer function *)
  val transfer : node_t -> absval_t -> absval_t
    (* takes the result of the abstract interpretation.
       returns a formatted analysis easily exploited by [transform].
       The map returned is the map of all offset variables. *)
  val format : analysis_t -> analysis_t * map_t
    (* takes the initial program and the formatted analysis, as well as 
       a map of offset variables.
       returns a transformed program. *)
  val transform : analysis_t -> map_t -> node_t list -> node_t list
end

module type DataFlowAnalysis = sig
  (* replicates type of InterLang *)
  type node_t
    (* replicates type of Connection *)
  type analysis_t
    (* takes a program and computes the result of an analysis *)
  val compute : node_t list -> analysis_t
end

(* very simple data-flow analysis, with fixed characteristics:
   forward, not needing widening (for example on bounded lattice) *)

module Make_DataFlowAnalysis
  (V : Variable) (IL : InterLang with type var_t = V.t) 
  (PWL : PointWiseLattice with type var_t = V.t)
  (* (W : WatchPoint with type node_t = IL.Node.t) *)
  (C : Connection with type node_t = IL.Node.t and type absval_t = PWL.t)
  = struct

  open IL

  type node_t = Node.t
  type analysis_t = C.analysis_t

  module NSet = Set.Make(IL.Node)

  let compute (nodes : Node.t list) =

    if debug then Coptions.lprintf 
      "[compute] begin with %i nodes in working list@." (List.length nodes);

    (* working list/set of nodes to treat *)
    let work_list = ref nodes in
    let work_set = ref (List.fold_right NSet.add nodes NSet.empty) in

    (* add/remove node in working list/set -- only at top of list *)
    let add_node node = 
      work_list := node :: (!work_list);
      work_set := NSet.add node (!work_set)
    in
    let rem_node node =
      work_list := List.tl (!work_list);
      work_set := NSet.remove node (!work_set)
    in

    (* result of the analysis *)
    let res : C.analysis_t = Hashtbl.create 0 in

    (* find current values associated to [node] *)
    let res_val node =
      try Hashtbl.find res node
      with Not_found -> PWL.bottom,PWL.bottom
    in

    while not (NSet.is_empty !work_set) do
      (* find next node and associated value *)
      let cur_node = List.hd (!work_list) in
      let pre_val,post_val = res_val cur_node in
      if debug then Coptions.lprintf 
	"[compute] take node in working list@.";

      (* clear node in list/set *)
      rem_node cur_node;

      (* compute next value and replace existing one *)
      let cur_val = C.transfer cur_node pre_val in
      if debug_more then Coptions.lprintf 
	"[compute] computed value: %a@." PWL.pretty cur_val;

      (* change value if different *)
      if not (PWL.equal cur_val post_val) then
	begin
	  if debug then Coptions.lprintf 
	    "[compute] new value is different@.";
	  Hashtbl.replace res cur_node (pre_val,cur_val);
	  let next_nodes = IL.successors cur_node in
	  if debug then Coptions.lprintf 
	    "[compute] node has %i successor(s)@." (List.length next_nodes);
	  if debug then Coptions.lprintf 
	    "[compute] %a@." (fun fmt -> List.iter (Node.pretty fmt))
	    next_nodes;
	  List.iter (fun nx_node ->
		       let nx_pre,nx_post = res_val nx_node in
		       let nx_val = PWL.join nx_pre cur_val in
		       if debug_more then Coptions.lprintf 
			 "[compute] succ prev value: %a@." PWL.pretty nx_pre;
		       if debug_more then Coptions.lprintf 
			 "[compute] succ cur value: %a@." PWL.pretty nx_val;

		       (* change value if different *)
		       if not (PWL.equal nx_val nx_pre) then
			 begin
			   if debug then Coptions.lprintf 
			     "[compute] new value for successor \
			      is different@.";
			   if debug_more then Coptions.lprintf 
			     "[compute] new value: %a@." PWL.pretty nx_val;
			   Hashtbl.replace res nx_node (nx_val,nx_post);
			   (* add node in working list/set if not present *)
			   if not (NSet.mem nx_node (!work_set)) then
			     begin
			       if debug then Coptions.lprintf 
				 "[compute] add successor in working list@.";
			       add_node nx_node
			     end
			 end
		    ) next_nodes
	end
    done;
    res

end


(*****************************************************************************
 *                                                                           *
 * 		Concrete modules for local pointer analysis		     *
 *                                                                           *
 *****************************************************************************)

(* We make the following choices in the following:
   - variables are represented by an entity of type [Info.var_info]
   - the intermediate language is the normalized AST as described by
   Cast.ndecl/nstatement/nexpr
   
   Other choices are perfectly possible, e.g. the pre-normalized AST
   as described by Cast.tdecl/tstatement/texpr as intermediate language.
*)

(* type used for offset from pointer *)
let int_offset_type = Ctypes.c_int

(* type to represent a function in the normalized code.
   It has the same elements as the hash-table [Cenv.c_functions]. *)
type func_t = 
    {
      name : string;
      spec : Cast.nspec; 
      typ  : Ctypes.ctype;
      f    : Info.fun_info;
      s    : Cast.nstatement option;
      loc  : Loc.position
    }

module Var : Variable with type t = var_info = struct
  type t = var_info
  let pretty fmt v = Format.fprintf fmt "%s" v.var_name
  let compare v1 v2 = Pervasives.compare v1.var_uniq_tag v2.var_uniq_tag
  let equal v1 v2 = compare v1 v2 = 0
  let hash v = v.var_uniq_tag
end

module PtrLattice : PointerLattice with type var_t = Var.t 
  = Make_PtrLattice(Var)

module VarMap = Map.Make (Var)
module VarSet = Set.Make (Var)

module PointWisePtrLattice = Make_PointWiseLattice(Var)(VarMap)(PtrLattice)

(* translation targetted at very simple syntaxical analysis on paths,
   since effects of calls are not considered, and unspecified evaluation order
   is translated in parallel edges in the CFG *)

module CFGLangFromNormalized : InterLang 
  with type var_t = Var.t and type decl_t = func_t
  = struct

  type var_t = Var.t
  type decl_t = func_t

  type node_kind = NKexpr | NKstat | NKdecl | NKnone

  (* special node [Nfwd] used for special purposes:
     - during construction to reference future nodes
     - to translate [switch] into appropriate structural tree *)
  type norm_node = 
    | Nexpr of nexpr
    | Nstat of nstatement
    | Ndecl of decl_t
    | Nfwd

  (* type of labels on edges in the CFG *)
  module NodeRelation = struct
    type t =
      | Operational    (* edge in the operational graph *)
      | StructuralDown (* edge to first sub-node in the structural graph *)
      | StructuralSame (* other edges in the structural graph *)
    (* arbitrary index to provide total ordering *)
    let index r = match r with
      | Operational -> 0
      | StructuralDown -> 1
      | StructuralSame -> 2
    let compare r1 r2 = Pervasives.compare (index r1) (index r2)
    (* if not stated otherwise, an edge is an operational one *)
    let default = Operational
  end

  (* We use here an abstract imperative labeled graph.
     Labels are of 2 kinds :
         - operational labels form a graph that respects evaluation order,
     to facilitate data-flow analysis
         - structural labels form a graph that respects the hierarchical order
     between expressions and statements, e.g. with [StructuralDown] labels from
     an expression to its first sub-expression, and [StructuralSame] label 
     from a sub-expression to the next sub-expression at the same level. *)

  module Self = 
    Graph.Imperative.Digraph.AbstractLabeled
      (struct type t = norm_node end) (NodeRelation)
  module Node = struct
    include Self.V
    let pretty fmt n =
      match label n with
      | Nexpr e -> Cprint.nexpr fmt e
      | Nstat s -> 
	  begin match s.nst_node with
	    | NSnop -> Format.fprintf fmt "NSnop"
	    | NSassert _ -> Format.fprintf fmt "NSassert"
	    | NSlogic_label _ -> Format.fprintf fmt "NSlogic_label"
	    | NSexpr e -> Format.fprintf fmt "NSexpr" 
	    | NSif (e,s1,s2) -> Format.fprintf fmt "NSif"
	    | NSwhile (annot,e,s1) -> Format.fprintf fmt "NSwhile"
	    | NSdowhile (annot,s1,e) -> Format.fprintf fmt "NSdowhile"
	    | NSfor (annot,einit,etest,eincr,s1) -> Format.fprintf fmt "NSfor"
	    | NSblock sl -> Format.fprintf fmt "NSblock"
	    | NSreturn None -> Format.fprintf fmt "NSreturn"
	    | NSreturn (Some e) -> Format.fprintf fmt "NSreturn" 
	    | NSbreak -> Format.fprintf fmt "NSbreak"
	    | NScontinue -> Format.fprintf fmt "NScontinue" 
	    | NSlabel (str,s1) -> Format.fprintf fmt "NSlabel"
	    | NSspec (spec,s1) -> Format.fprintf fmt "NSspec"
	    | NSdecl (typ,var,None,s1) -> Format.fprintf fmt "NSdecl"
	    | NSdecl (typ,var,Some cinit,s1) -> Format.fprintf fmt "NSdecl"
	    | NSswitch (e,c,cases) -> Format.fprintf fmt "NSswitch" 
	  end
      | Ndecl _ -> Format.fprintf fmt "Ndecl"
      | Nfwd -> Format.fprintf fmt "Nfwd"
  end
  module Edge = Self.E

  (* shortcut query functions *)

  let get_node_kind node =
    match Node.label node with
      | Nexpr _ -> NKexpr
      | Nstat _ -> NKstat
      | Ndecl _ -> NKdecl
      | Nfwd -> NKnone

  let get_e node = 
    match Node.label node with
      | Nexpr e -> e
      | _ -> failwith "[get_e] should be called only on expression"
  let get_expr node = (get_e node).nexpr_node

  let get_s node = 
    match Node.label node with
      | Nstat s -> s
      | _ -> failwith "[get_s] should be called only on statement"
  let get_stat node = (get_s node).nst_node

  let get_decl node = 
    match Node.label node with
      | Ndecl d -> d
      | _ -> failwith "[get_decl] should be called only on declaration"
	  
  (* more elaborate query functions related to pointer usage *)

  let is_pointer_type ctyp = match ctyp.Ctypes.ctype_node with
    | Ctypes.Tvar _ -> assert false (* not allowed in code *)
    | Ctypes.Tarray _ | Ctypes.Tpointer _ -> true
    | _ -> false

  let var_is_pointer var =
    is_pointer_type var.var_type

  let var_is_local var =
    not var.var_is_static

  let decl_get_params node =
    (get_decl node).f.args

  let stat_is_return node =
    match get_stat node with
      | NSreturn _ -> true
      | _ -> false

  let expr_type_is_ptr node = is_pointer_type (get_e node).nexpr_type

  let expr_is_local_var node = match get_expr node with
    | NEvar (Var_info var) -> var_is_local var
    | _ -> false

  let expr_is_local_ptr_var node = match get_expr node with
    | NEvar (Var_info var) -> var_is_pointer var && var_is_local var
    | _ -> false

  let expr_var_get_var node = match get_expr node with
    | NEvar (Var_info var) -> var
    | _ -> assert false

  let expr_is_assign node = match get_expr node with
    | NEincr (_,e1) | NEassign (e1,_) | NEassign_op (e1,_,_) -> true
    | _ -> false

  let sub_expr_is_ptr_assign e = match e with
    | NEincr (_,e1) | NEassign (e1,_) | NEassign_op (e1,_,_) ->
	let lhs_type : Ctypes.ctype = e1.nexpr_type in
	is_pointer_type lhs_type
    | _ -> false
	
  let expr_is_ptr_assign node =
    sub_expr_is_ptr_assign (get_expr node)

  let sub_ptr_assign_get_lhs_var e = match e with
    | NEincr (_,e1) | NEassign (e1,_) | NEassign_op (e1,_,_) ->
	begin
	  (* exhaustive case analysis needed here, in order to 
	     guarantee no assignment can be missed *)
	  match e1.nexpr_node with
	      (* cast not allowed here for the moment, it is checked
		 and error possibly reported in an earlier stage *)
	    | NEcast _ -> assert false
		(* not an assignment to a pointer variable *)
	    | NEarrow _ | NEunary (Ustar,_) -> None
		(* pointer assignment to some variable [var] *)
	    | NEvar (Var_info var) -> Some var
		(* other cases should not be possible *)
	    | _ -> assert false
	end
    | _ -> failwith ("[sub_ptr_assign_get_lhs_var] should be called"
		     ^ " only on pointer assignment")

  let ptr_assign_get_lhs_var node =
    sub_ptr_assign_get_lhs_var (get_expr node)

  let ptr_assign_get_local_lhs_var node =
    match ptr_assign_get_lhs_var node with
      | None -> None
      | Some var -> if var_is_local var then Some var else None

  let ptr_assign_get_rhs_var node =
    match get_expr node with
      | NEincr (op,e) ->
	  let rhs_node = e.nexpr_node in
	  let var = match rhs_node with
	    | NEvar (Var_info var) -> var
	    | _ -> assert false (* only variable assignment are considered *)
	  in
	  begin match op with
	    | Upostfix_inc | Uprefix_inc ->
		Some var,Some 1
	    | Upostfix_dec | Uprefix_dec ->
		Some var,Some (-1)
	  end
      | NEassign (_,e) | NEassign_op (_,_,e) ->
	  let rhs_node = e.nexpr_node in
	  begin match rhs_node with
	    | NEvar (Var_info var) -> 
		(* direct alias *)
		Some var,Some 0
	    | NEincr _ | NEassign _ | NEassign_op _ ->
		(* right-hand side is itself an assignment *)
		if sub_expr_is_ptr_assign rhs_node then
		  (* rhs is a pointer assignment *) 
		  match sub_ptr_assign_get_lhs_var rhs_node with
		    | None -> None,None (* rhs variable not identified *)
		    | Some var ->
			(* rhs variable has been identified *)
			begin match rhs_node with
			  | NEincr (Upostfix_inc,_) ->
			      Some var,Some (-1)
			  | NEincr (Upostfix_dec,_) ->
			      Some var,Some 1
			  | _ -> Some var,Some 0
			end
		else None,None (* rhs is not a pointer assignment *)
	    | NEbinary (e1,Badd_pointer_int,e2) ->
		(* right-hand side is an offset from a pointer expression *)
		begin match e1.nexpr_node with
		  | NEvar (Var_info var) ->
		      (* rhs is an offset from some variable *)
		      begin match e2.nexpr_node with
			| NEconstant (Clogic.IntConstant s) ->
			    (* rhs is constant offset from variable *)
			    begin
			      try 
				(* constant offset is representable *)
				Some var,Some (int_of_string s)
			      with Failure "int_of_string" ->
				(* constant offset not representable *)
				Some var,None
			    end
			| _ -> Some var,None (* offset not known *)
			end
		  | _ -> None,None (* rhs not offset from variable *)
		end
	    | _ -> None,None (* rhs not recognized *)
	  end
      | _ -> failwith ("[ptr_assign_get_rhs_var] should be called"
		       ^ " only on pointer assignment")

  let get_ptr_add_on_var_opt node =
    let e = get_e node in
    match e.nexpr_node with
      | NEvar _ -> None,None
      | NEbinary (e1,Badd_pointer_int,e2) -> 
	  let add_opt = Some (Node.create (Nexpr e2)) in
	  let var_opt = match e1.nexpr_node with
	    | NEvar (Var_info v) -> Some v
	    | _ -> None
	  in
	  var_opt,add_opt
      | _ -> assert false

  (* construction of the graph(s), i.e. operational + structural *)

  let graph = Self.create ()
  let nodes_in_exec_order : Node.t list ref = ref []
  let add_node_in_order node = 
    nodes_in_exec_order := node :: (!nodes_in_exec_order)

  (* structural successors. Only [StructuralDown] and [StructuralSame]
     labels should be taken into account. *)
  let child n = 
    let el = Self.succ_e graph n in
    let el = List.filter 
      (fun e -> Edge.label e = NodeRelation.StructuralDown) el in
    match List.map Edge.dst el with
      | [] -> None
      | [a] -> Some a
      | _ -> failwith "[child n] should find at most one child for node [n]"
  let sibling n =
    let el = Self.succ_e graph n in
    let el = List.filter 
      (fun e -> Edge.label e = NodeRelation.StructuralSame) el in
    match List.map Edge.dst el with
      | [] -> None
      | [a] -> Some a
      | _ -> failwith ("[sibling n] should find at most one sibling"
		       ^ "for node [n]")
  let rec siblings n =
    match sibling n with
      | None -> []
      | Some m -> m :: (siblings m)
  let children n =
    match child n with
      | None -> []
      | Some m -> m :: (siblings m)
 
  (* [successors n] returns the operational successors of node [n] 
     for the data-flow analysis. Only [Operational] labels should be
     taken into account. It is also the case for [predecessors]. *)
  let successors n = 
    let el = Self.succ_e graph n in
    let el = List.filter 
      (fun e -> Edge.label e = NodeRelation.Operational) el in
    List.map Edge.dst el
  let predecessors n =
    let el = Self.pred_e graph n in
    let el = List.filter 
      (fun e -> Edge.label e = NodeRelation.Operational) el in
    List.map Edge.src el

  (* add a node *)
  let add_vertex = Self.add_vertex graph

  (* add an operational edge.
     - [force_add_opedge] should be used for edges that originate in 
     a jumping statement like a return/break/continue.
     - [add_opedge] should be used in all other cases, with the knowledge
     that an edge will be added only if the source statement is not
     a jumping one. *)
  let force_add_opedge = Self.add_edge graph
  let add_opedge v1 v2 =
    match get_node_kind v1 with
      | NKstat ->
	  begin match get_stat v1 with
	    | NSreturn _ | NSbreak | NScontinue ->
		(* normal operational edges should not originate from
		   a jumping statement, in which case [force_add_opedge]
		   is used. Do nothing. *)
		()
	    | _ -> force_add_opedge v1 v2
	  end
      | _ -> force_add_opedge v1 v2
    
  (* add structural edges: a [StructuralDown] edge from [v] to the first
     node in the list [vl], and [StructuralSame] edges between successive
     nodes in [vl]. *)
  let add_stedge v vl = 
    let add_down_edge v1 v2 = 
      let e = Edge.create v1 NodeRelation.StructuralDown v2 in
      Self.add_edge_e graph e
    in
    let add_same_edge v1 v2 = 
      let e = Edge.create v1 NodeRelation.StructuralSame v2 in
      Self.add_edge_e graph e
    in
    let rec add_same_edges vl = match vl with
      | a::b::r -> add_same_edge a b; add_same_edges (b::r)
      | _ -> ()
    in
    match vl with
      | [] -> ()
      | a::r -> add_down_edge v a; add_same_edges vl

  (* constructors *)

  let make_seq_expr node1 node2 =
    let e1 = get_e node1 in
    let e2 = get_e node2 in
    let new_e = NEseq (e1,e2) in
    let new_e = { e2 with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  let make_int_expr_add_cst node cst =
    let e = get_e node in
    let typ = e.nexpr_type in
    let op = match typ.Ctypes.ctype_node with 
      | Ctypes.Tint ik -> Badd_int ik
      | _ -> failwith ("[make_int_expr_add_cst] should only be called on"
		       ^ " integer expression") in
    let cst_e = NEconstant (Clogic.IntConstant (string_of_int cst)) in
    let cst_e = { e with nexpr_node = cst_e } in
    let new_e = NEbinary (e,op,cst_e) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  let make_int_expr_add_var node var =
    let e = get_e node in
    let typ = e.nexpr_type in
    let op = match typ.Ctypes.ctype_node with 
      | Ctypes.Tint ik -> Badd_int ik
      | _ -> failwith ("[make_int_expr_add_cst] should only be called on"
		       ^ " integer expression") in
    let cst_e = NEvar (Var_info var) in
    let cst_e = { e with nexpr_node = cst_e } in
    (* prefer var + expr to expr + var, for ergonomic issues *)
    let new_e = NEbinary (cst_e,op,e) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  let make_int_expr_add_expr node1 node2 =
    let e1 = get_e node1 in
    let e2 = get_e node2 in
    let typ = e1.nexpr_type in
    let op = match typ.Ctypes.ctype_node with 
      | Ctypes.Tint ik -> Badd_int ik
      | _ -> failwith ("[make_int_expr_add_expr] should only be called on"
		       ^ " integer expression") in
    let new_e = NEbinary (e1,op,e2) in
    let new_e = { e1 with nexpr_node = new_e } in
    Node.create (Nexpr new_e)    

  (* expr + neg_cst is coded as expr + (-abs(neg_cst))
     This format is expected by [Cconst] module. *)
  let make_ptr_expr_add_cst node cst =
    let e = get_e node in
    let cst_e = NEconstant (Clogic.IntConstant (string_of_int (abs cst))) in
    let cst_e = { e with nexpr_node = cst_e; nexpr_type = int_offset_type } in
    let cst_e = if cst >= 0 then cst_e else
      { cst_e with nexpr_node = NEunary (Uminus,cst_e) } in
    let new_e = NEbinary (e,Badd_pointer_int,cst_e) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  let change_in_var node var =
    let e = get_e node in
    let new_e = NEvar (Var_info var) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  (* var + neg_cst is coded as var + (-abs(neg_cst))
     This format is expected by [Cconst] module. *)
  let change_in_ptr_var_add_cst node var offset =
    let e = get_e node in
    let var_e = NEvar (Var_info var) in
    let var_e = { e with nexpr_node = var_e } in
    let cst_e = NEconstant (Clogic.IntConstant (string_of_int (abs offset))) in
    let cst_e = { e with nexpr_node = cst_e; nexpr_type = int_offset_type } in
    let cst_e = if offset >= 0 then cst_e else
      { cst_e with nexpr_node = NEunary (Uminus,cst_e) } in
    let new_e = NEbinary (var_e, Badd_pointer_int, cst_e) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  let change_in_ptr_var_add_var node var offset_var =
    let e = get_e node in
    let var_e = NEvar (Var_info var) in
    let var_e = { e with nexpr_node = var_e } in
    let cst_e = NEvar (Var_info offset_var) in
    let cst_e = { e with nexpr_node = cst_e; nexpr_type = int_offset_type } in
    let new_e = NEbinary (var_e, Badd_pointer_int, cst_e) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  let change_in_ptr_var_add_expr node var offset_expr =
    let e = get_e node in
    let var_e = NEvar (Var_info var) in
    let var_e = { e with nexpr_node = var_e } in
    let new_e = NEbinary (var_e, Badd_pointer_int, get_e offset_expr) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  (* changes the expression's type if necessary *)
  let change_in_var_assign_cst node var index =
    let e = get_e node in
    let var_e = NEvar (Var_info var) in
    let typ_e = var.var_type in
    let var_e = { e with nexpr_node = var_e; nexpr_type = typ_e } in
    let cst_e = NEconstant (Clogic.IntConstant (string_of_int index)) in
    let cst_e = { e with nexpr_node = cst_e; nexpr_type = typ_e } in
    let new_e = NEassign (var_e, cst_e) in
    let new_e = { e with nexpr_node = new_e; nexpr_type = typ_e } in
    Node.create (Nexpr new_e)
    
  (* changes the expression's type if necessary *)
  let change_in_var_assign_var node var other_var =
    let e = get_e node in
    let var_e = NEvar (Var_info var) in
    let typ_e = var.var_type in
    let var_e = { e with nexpr_node = var_e; nexpr_type = typ_e } in
    let cst_e = NEvar (Var_info other_var) in
    let cst_e = { e with nexpr_node = cst_e; nexpr_type = typ_e } in
    let new_e = NEassign (var_e, cst_e) in
    let new_e = { e with nexpr_node = new_e; nexpr_type = typ_e } in
    Node.create (Nexpr new_e)
      
  (* changes the expression's type if necessary *)
  let change_in_var_assign_expr node var sub_node =
    let e = get_e node in
    let var_e = NEvar (Var_info var) in
    let typ_e = var.var_type in
    let var_e = { e with nexpr_node = var_e; nexpr_type = typ_e } in
    let cst_e = get_e sub_node in
    let new_e = NEassign (var_e, cst_e) in
    let new_e = { e with nexpr_node = new_e; nexpr_type = typ_e } in
    Node.create (Nexpr new_e)    

  let change_in_ptr_incr node new_rhs_node is_after_assign =
    let e = get_e node in
    let op = match e.nexpr_node with NEincr (op,_) -> op | _ -> assert false in
    let is_inop_op op =
      if is_after_assign then
	(* prefix operations must have occurred after assignment *)
	op = Uprefix_inc || op = Uprefix_dec
      else
	(* postfix operations must not have occurred before assignment *)
	op = Upostfix_inc || op = Upostfix_dec
    in
    let is_add1_op op =
      if is_after_assign then
	(* postfix decrement should be reversed after asssignment *)
	op = Upostfix_dec
      else
	(* prefix increment must be coded before assignment *)
	op = Uprefix_inc
    in
    let is_sub1_op op =
      if is_after_assign then
	(* postfix increment should be reversed after asssignment *)
	op = Upostfix_inc
      else
	(* prefix decrement must be coded before assignment *)
	op = Uprefix_dec
    in
    if is_inop_op op then
      new_rhs_node
    else if is_add1_op op then
      make_ptr_expr_add_cst new_rhs_node 1
    else if is_sub1_op op then
      make_ptr_expr_add_cst new_rhs_node (-1)
    else
      assert false

  let change_in_int_incr_assign node offset_var =
    let e = get_e node in
    let var_e = NEvar (Var_info offset_var) in
    let var_e = { e with nexpr_node = var_e; nexpr_type = int_offset_type } in
    let new_e =
      match e.nexpr_node with
	| NEincr (op,_) -> 
	    (* keep the original increment/decrement operator for ergonomy
	       purposes. Postfix/prefix choice should have no effect here
	       since this node is not supposed to be used as 
	       a sub-expression. *)
	    NEincr (op,var_e)
	| _ -> assert false
    in
    let new_e = { e with nexpr_node = new_e; nexpr_type = int_offset_type } in
    Node.create (Nexpr new_e)

  (* exception used to report unexpected encoding in [change_sub_components] *)
  exception Bad_encoding

  let change_sub_components node sub_nodes =
    match get_node_kind node with
      | NKnone ->
	  (* forward node for upper level. Rebuild the correct one-level 
	     sub-graph so that the upper level can rely on it if necessary. *)
	  let fwd_node = Node.create Nfwd in
	  add_vertex fwd_node;
	  add_stedge fwd_node sub_nodes;
	  fwd_node
	  
      | NKdecl ->
	  let d = get_decl node in
	  let new_d =
	    match d.s with
	      | Some s ->
		  let new_s = list1 sub_nodes in
		  let new_s = get_s new_s in
		  { d with s = Some new_s }
	      | _ -> d
	  in
	  Node.create (Ndecl new_d)

      | NKstat ->
	  let s = get_s node in
	  (* in case an assignment was transformed into its right-hand side,
	     do not keep the resulting expression if useless.
	     In general this could be seen as an optimization.
	     Currently it is necessary because [Cinterp] module might fail
	     on such code that it considers as a "statement expression". *)
	  let rec useless_expr e = match e.nexpr_node with
	      (* only possible "statement expression" cases returned 
		 by the transformation *)
	    | NEconstant _ | NEvar _ -> true
	    | NEbinary (e1,_,e2) -> (useless_expr e1) && (useless_expr e2)
	    | NEunary (_,e1) -> useless_expr e1
	    | _ -> false
	  in
	  let rec simplify_expr e = match e.nexpr_node with
	    | NEseq (e1,e2) ->
		(* [e2] may be the pointer evaluation, useless here *)
		if useless_expr e2 then e1 else e
	    | _ -> e
	  in
	  let statement_expr_or_nop e = 
	    let e = simplify_expr e in
	    if useless_expr e then NSnop else NSexpr e
	  in
	  let new_s =
	    match s.nst_node with
	      | NSnop | NSassert _ | NSlogic_label _ ->
		  s.nst_node
	      | NSexpr e -> 
		  assert (List.length sub_nodes = 1);
		  let new_e = list1 sub_nodes in
		  let new_e = get_e new_e in
		  statement_expr_or_nop new_e
	      | NSif (e,s1,s2) ->
		  let new_e,new_s1,new_s2 = list3 sub_nodes in
		  let new_e,new_s1,new_s2 
		    = get_e new_e,get_s new_s1,get_s new_s2 in
		  let new_e = simplify_expr new_e in
		  NSif (new_e,new_s1,new_s2)
	      | NSwhile (annot,e,s1) ->
		  let new_e,new_s1 = list2 sub_nodes in
		  let new_e,new_s1 = get_e new_e,get_s new_s1 in
		  let new_e = simplify_expr new_e in
		  NSwhile (annot,new_e,new_s1)
	      | NSdowhile (annot,s1,e) ->
		  let new_s1,new_e = list2 sub_nodes in
		  let new_s1,new_e = get_s new_s1,get_e new_e in
		  let new_e = simplify_expr new_e in
		  NSdowhile (annot,new_s1,new_e)
	      | NSfor (annot,einit,etest,eincr,s1) ->
		  let new_einit,new_etest,new_eincr,new_s1 = list4 sub_nodes in
		  let new_einit,new_etest,new_eincr,new_s1 
		    = get_e new_einit,get_e new_etest,
		    get_e new_eincr,get_s new_s1 in
		  let new_einit = simplify_expr new_einit in
		  let new_etest = simplify_expr new_etest in
		  let new_eincr = simplify_expr new_eincr in
		  NSfor (annot,new_einit,new_etest,new_eincr,new_s1)
	      | NSblock sl ->
		  let new_sl = List.map get_s sub_nodes in
		  NSblock new_sl
	      | NSreturn None ->
		  s.nst_node
	      | NSreturn (Some e) -> 
		  assert (List.length sub_nodes = 1);
		  let new_e = list1 sub_nodes in
		  let new_e = get_e new_e in
		  let new_e = simplify_expr new_e in
		  NSreturn (Some new_e)
	      | NSbreak | NScontinue -> 
		  s.nst_node
	      | NSlabel (str,s1) ->
		  assert (List.length sub_nodes = 1);
		  let new_s = list1 sub_nodes in
		  let new_s = get_s new_s in
		  NSlabel (str,new_s)
	      | NSspec (spec,s1) ->
		  assert (List.length sub_nodes = 1);
		  let new_s = list1 sub_nodes in
		  let new_s = get_s new_s in
		  NSspec (spec,new_s)
	      | NSdecl (typ,var,None,s1) ->
		  assert (List.length sub_nodes = 1);
		  let new_s = list1 sub_nodes in
		  let new_s = get_s new_s in
		  NSdecl (typ,var,None,new_s)
	      | NSdecl (typ,var,Some cinit,s1) ->
		  let new_e,new_s1 = list2 sub_nodes in
		  let new_e = get_e new_e in
		  let new_s1 = get_s new_s1 in
		  begin try
		    (* to be matched with [encode_list] below *)
		    let rec decode_list einit = match einit.nexpr_node with
		      | NEcall ce ->
			  let caller = ce.ncall_fun in
			  if caller.nexpr_node = NEnop then
			    (* encoding of an initialization list *)
			    let args = ce.ncall_args in
			    Ilist (List.map decode_list args)
			  else
			    (* only other possibility is expression *)
			    Iexpr einit
		      | _ -> Iexpr einit
		    in
		    let lhs_expr,rhs_expr = match new_e.nexpr_node with 
		      | NEassign (lhs_expr,rhs_expr) -> lhs_expr,rhs_expr
		      | _ -> raise Bad_encoding in
		    let new_var = match lhs_expr.nexpr_node with
		      | NEvar (Var_info new_var) -> new_var
		      | _ -> raise Bad_encoding
		    in
		    if Var.equal var new_var then
		      (* not an offset assignment *)
		      let new_cinit = decode_list rhs_expr in
		      NSdecl (typ,var,Some new_cinit,new_s1)
		    else if var_is_pointer new_var then
		      (* neither the original variable nor an offset 
			 assignment. It must be of pointer type. *)
		      raise Bad_encoding
		    else
		      begin
			(* offset assignment.
			   Can only occur for [Iexpr] initializer, because 
			   [Ilist] initializer is encoded into a call, which
			   can only lead to a complex pointer kind for [var].
			   The variable [var] is not used anymore in the new
			   program. We can safely eliminate it. *)
			match cinit with
			  | Iexpr e ->
			      (* remove the initialization, since it is 
				 performed globally at the beginning of 
				 the function body for all offset variables *)
			      let assign_stat = 
				{ s with nst_node = NSexpr new_e } in
			      let block_stat = NSblock [assign_stat;new_s1] in
			      let block_stat = { s with nst_node = block_stat }
			      in
			      (* always keep the pointer declaration *)
			      NSdecl (typ,var,None,block_stat)
			  | _ -> assert false
		      end
		  with Bad_encoding ->
		    (* exception [Bad_encoding] was raised if the encoded
		       assignment was neither maintained nor transformed 
		       into an offset assignment. This can happen if
		       the assignment was detected as useless, and therefore
		       only the right-hand side was returned. Keep it. *)
		    let new_s = statement_expr_or_nop new_e in
		    let new_stat = { s with nst_node = new_s } in
		    let block_stat = NSblock [new_stat;new_s1] in
		    let block_stat = { s with nst_node = block_stat }
		    in
		    (* always keep the pointer declaration *)
		    NSdecl (typ,var,None,block_stat)
		  end
	      | NSswitch (e,c,cases) -> 
		  let new_e = List.hd sub_nodes in
		  let new_cases = List.tl sub_nodes in
		  let new_e = get_e new_e in
		  let new_e = simplify_expr new_e in
		  (* remove [Nfwd] node introduced for each [case] *)
		  let new_cases = List.map (fun n -> children n) new_cases in
		  let new_cases = List.map (List.map get_s) new_cases in
		  let new_cases = 
		    List.map2 (fun (cmap,_) sl -> (cmap,sl)) cases new_cases in
		  NSswitch (new_e,c,new_cases)
	  in
	  let new_s = { s with nst_node = new_s } in
	  Node.create (Nstat new_s)

      | NKexpr ->
	  let e = get_e node in
	  let new_e =
	    match e.nexpr_node with
	      | NEnop | NEconstant _ | NEstring_literal _ | NEvar _ ->
		  e.nexpr_node
	      | NEarrow (e1,zone,var) ->
		  assert (List.length sub_nodes = 1);
		  let new_e = list1 sub_nodes in
		  let new_e = get_e new_e in
		  NEarrow (new_e,zone,var)
	      | NEunary (op,e1) ->
		  assert (List.length sub_nodes = 1);
		  let new_e = list1 sub_nodes in
		  let new_e = get_e new_e in
		  NEunary (op,new_e)
	      | NEincr (op,e1) ->
		  assert (List.length sub_nodes = 1);
		  let new_e = list1 sub_nodes in
		  let new_e = get_e new_e in
		  NEincr (op,new_e)
	      | NEcast (typ,e1) ->
		  assert (List.length sub_nodes = 1);
		  let new_e = list1 sub_nodes in
		  let new_e = get_e new_e in
		  NEcast (typ,new_e)
	      | NEmalloc (typ,e1) ->
		  assert (List.length sub_nodes = 1);
		  let new_e = list1 sub_nodes in
		  let new_e = get_e new_e in
		  NEmalloc (typ,new_e)
	      | NEseq (e1,e2) ->
		  let new_e1,new_e2 = list2 sub_nodes in
		  let new_e1,new_e2 = get_e new_e1,get_e new_e2 in
		  NEseq (new_e1,new_e2)
	      | NEassign (e1,e2) ->
		  let new_e1,new_e2 = list2 sub_nodes in
		  let new_e1,new_e2 = get_e new_e1,get_e new_e2 in
		  NEassign (new_e1,new_e2)
	      | NEassign_op (e1,op,e2) ->
		  let new_e1,new_e2 = list2 sub_nodes in
		  let new_e1,new_e2 = get_e new_e1,get_e new_e2 in
		  NEassign_op (new_e1,op,new_e2)
	      | NEbinary (e1,op,e2) ->
		  let new_e1,new_e2 = list2 sub_nodes in
		  let new_e1,new_e2 = get_e new_e1,get_e new_e2 in
		  begin match op with
		    | Bsub_pointer | Blt_pointer | Bgt_pointer | Ble_pointer 
		    | Bge_pointer | Beq_pointer | Bneq_pointer ->
			(* binary operation on pointers. If both arguments are
			   indices/offsets from the same pointer, translate
			   the pointer operation into an equivalent integer 
			   operation. *)
			let rec destr_ptr_off e = match e.nexpr_node with
			  | NEbinary(e1,Badd_pointer_int,e2) ->
			      begin match e1.nexpr_node with
				| NEvar (Var_info v) -> Some (v,e2)
				| _ -> 
				    (* recursive call *)
				    begin match destr_ptr_off e1 with
				      | Some (v,e3) ->
					  let e2 = Node.create (Nexpr e2) in
					  let e3 = Node.create (Nexpr e3) in
					  let e4 = make_int_expr_add_expr e2 e3
					  in
					  Some (v,get_e e4)
				      | None -> None
				    end
			      end
			  | _ -> None
			in
			let pointer_op_to_int_op op = match op with
			  | Bsub_pointer -> Bsub
			  | Blt_pointer -> Blt
			  | Bgt_pointer -> Bgt
			  | Ble_pointer -> Ble
			  | Bge_pointer -> Bge
			  | Beq_pointer -> Beq
			  | Bneq_pointer -> Bneq
			  | _ -> assert false
			in
			begin 
			  match destr_ptr_off new_e1,destr_ptr_off new_e2 with
			    | Some (v1,e3),Some (v2,e4) ->
				if Var.equal v1 v2 then NEbinary (e3,op,e4)
				else NEbinary (new_e1,op,new_e2)
			    | _ -> NEbinary (new_e1,op,new_e2)
			end
		    | _ -> NEbinary (new_e1,op,new_e2)
		  end
	      | NEcall c ->
		  let new_f = List.hd sub_nodes in
		  let new_args = List.tl sub_nodes in
		  let new_f = get_e new_f in
		  let new_args = List.map get_e new_args in
		  NEcall { c with ncall_fun = new_f; ncall_args = new_args }
	      | NEcond (e1,e2,e3) ->
		  let new_e1,new_e2,new_e3 = list3 sub_nodes in
		  let new_e1,new_e2,new_e3 
		    = get_e new_e1,get_e new_e2,get_e new_e3 in
		  NEcond (new_e1,new_e2,new_e3)
	  in		
	  let new_e = { e with nexpr_node = new_e } in
	  Node.create (Nexpr new_e)

  let introduce_new_vars node var_list zero_init =
    let d = get_decl node in
    let new_d =
      match d.s with
	| Some s ->
	    let new_s = 
	      List.fold_left 
		(fun next_s var -> 
		   let init = 
		     if zero_init then
		       let zero_cst = 
			 NEconstant (Clogic.IntConstant (string_of_int 0)) in
		       let zero_expr = { nexpr_node = zero_cst; 
					 nexpr_type = int_offset_type;
					 nexpr_loc = Loc.dummy_position } in
		       Some (Iexpr zero_expr)
		     else None
		   in
		   let decl_stat = 
		     NSdecl (var.var_type,var,init,next_s) in
		   { next_s with nst_node = decl_stat }
		) s var_list
	    in
	    { d with s = Some new_s }
	| None -> 
	    begin match var_list with
	      | [] -> d
	      | _ -> failwith ("[introduce_new_vars] should be called with"
			       ^ " empty [var_list] in this case")
	    end
    in
    Node.create (Ndecl new_d)

  (* extraction of graph from normalized AST *)

  let rec from_expr start_node (e : nexpr) = 
    let enode = Node.create (Nexpr e) in
    add_vertex enode;
    begin
      match e.nexpr_node with
	| NEnop | NEconstant _ | NEstring_literal _ | NEvar _ ->
	    (* oper *) add_opedge start_node enode
	| NEarrow (e1,_,_) | NEunary (_,e1) | NEincr (_,e1) 
	| NEcast (_,e1) | NEmalloc (_,e1) ->
	    let e1node = from_expr start_node e1 in
	    (* oper *) add_opedge e1node enode;
	    (* struct *) add_stedge enode [e1node]
	| NEseq (e1,e2) ->
	    let e1node = from_expr start_node e1 in
	    let e2node = from_expr e1node e2 in
	    (* oper *) add_opedge e2node enode;
	    (* struct *) add_stedge enode [e1node; e2node]
	| NEassign (e1,e2) | NEassign_op (e1,_,e2) | NEbinary (e1,_,e2) ->
	    let e1node = from_expr start_node e1 in
	    let e2node = from_expr start_node e2 in
	    (* oper *) add_opedge e1node enode;
	    (* oper *) add_opedge e2node enode;
	    (* struct *) add_stedge enode [e1node; e2node]
	| NEcall c ->
	    let fnode = from_expr start_node c.ncall_fun in
	    let anodes = List.map (from_expr start_node) c.ncall_args in
	    (* oper *) add_opedge fnode enode;
	    (* oper *) List.iter (fun anode -> add_opedge anode enode) anodes;
	    (* struct *) add_stedge enode (fnode::anodes)
	| NEcond (e1,e2,e3) ->
	    let e1node = from_expr start_node e1 in
	    let e2node = from_expr e1node e2 in
	    let e3node = from_expr e1node e3 in
	    (* oper *) add_opedge e2node enode;
	    (* oper *) add_opedge e3node enode;
	    (* struct *) add_stedge enode [e1node; e2node; e3node]
    end;
    add_node_in_order enode;
    enode

  type loop_descr = 
      { 
	(* target for [continue] statements in loops *)
	loop_starts : Node.t list; 
	(* target for [break] statements in loops and switches *)
	loop_switch_ends : Node.t list 
      }

  let rec from_stat (loops : loop_descr) start_node (s : nstatement) =
    let snode = Node.create (Nstat s) in
    add_vertex snode;
    begin
      match s.nst_node with
	| NSnop | NSassert _ | NSlogic_label _ ->
	    (* oper *) add_opedge start_node snode
	| NSexpr e -> 
	    let enode = from_expr start_node e in
	    (* oper *) add_opedge enode snode;
	    (* struct *) add_stedge snode [enode]
	| NSif (e,s1,s2) ->
	    let enode = from_expr start_node e in
	    let s1node = from_stat loops enode s1 in
	    let s2node = from_stat loops enode s2 in
	    (* oper *) add_opedge s1node snode;
	    (* oper *) add_opedge s2node snode;
	    (* struct *) add_stedge snode [enode; s1node; s2node]
	| NSwhile (_,e,s1) ->
	    (* target of backward edge in loop *)
	    let bwd_node = Node.create Nfwd in
	    add_vertex bwd_node;
	    (* connect backward edge *)
	    (* oper *) add_opedge start_node bwd_node;
	    let enode = from_expr bwd_node e in
	    let upd_loops =
	      { loop_starts = bwd_node :: loops.loop_starts;
		loop_switch_ends = snode :: loops.loop_switch_ends } in
	    let s1node = from_stat upd_loops enode s1 in
	    (* oper *) add_opedge s1node bwd_node; (* before [e]'s eval *)
	    (* oper *) add_opedge enode snode; (* after [e]'s eval *)
	    (* struct *) add_stedge snode [enode; s1node]
	| NSdowhile (_,s1,e) ->
	    (* target of backward edge in loop *)
	    let bwd_node = Node.create Nfwd in
	    add_vertex bwd_node;
	    (* connect backward edge *)
	    (* oper *) add_opedge start_node bwd_node;
	    let fwd_enode = Node.create Nfwd in
	    add_vertex fwd_enode;
	    let upd_loops =
	      { loop_starts = fwd_enode :: loops.loop_starts;
		loop_switch_ends = snode :: loops.loop_switch_ends } in
	    let s1node = from_stat upd_loops bwd_node s1 in
	    let enode = from_expr fwd_enode e in
	    (* oper *) add_opedge s1node fwd_enode;
	    (* oper *) add_opedge enode bwd_node; (* before [s1]'s eval *)
	    (* oper *) add_opedge enode snode;
	    (* struct *) add_stedge snode [s1node; enode]
	| NSfor (_,einit,etest,eincr,s1) ->
	    (* target of backward edge in loop *)
	    let bwd_node = Node.create Nfwd in
	    add_vertex bwd_node;
	    let einit_node = from_expr start_node einit in
	    (* connect backward edge *)
	    (* oper *) add_opedge einit_node bwd_node;
	    let etest_node = from_expr bwd_node etest in
	    let fwd_enode = Node.create Nfwd in
	    add_vertex fwd_enode;
	    let upd_loops =
	      { loop_starts = fwd_enode :: loops.loop_starts;
		loop_switch_ends = snode :: loops.loop_switch_ends } in
	    let s1node = from_stat upd_loops etest_node s1 in
	    let eincr_node = from_expr fwd_enode eincr in
	    (* oper *) add_opedge s1node fwd_enode;
	    (* oper *) add_opedge eincr_node bwd_node; (* before [etest] *)
	    (* oper *) add_opedge etest_node snode; (* after [etest]'s eval *)
	    (* struct *) add_stedge snode [einit_node; etest_node;
					   eincr_node; s1node]
	| NSblock sl ->
	    let (bnode,snodes) = 
	      List.fold_left 
		(fun (stnode,s1nodes) s1 -> 
		   let s1node = from_stat loops stnode s1 in
		   s1node,s1node::s1nodes
		) (start_node,[]) sl in
	    let snodes = List.rev snodes in
	    (* oper *) add_opedge bnode snode;
	    (* struct *) add_stedge snode snodes
	| NSreturn None ->
	    (* oper *) add_opedge start_node snode;
	| NSreturn (Some e) -> 
	    let enode = from_expr start_node e in
	    (* oper *) add_opedge enode snode;
	    (* struct *) add_stedge snode [enode]
	| NSbreak -> 
	    (* oper *) add_opedge start_node snode;
	    (* oper *) force_add_opedge snode (List.hd loops.loop_switch_ends);
	| NScontinue -> 
	    (* oper *) add_opedge start_node snode;
	    (* oper *) force_add_opedge snode (List.hd loops.loop_starts)
	| NSlabel (_,s1) | NSspec (_,s1) | NSdecl (_,_,None,s1) ->
	    let s1node = from_stat loops start_node s1 in
	    (* oper *) add_opedge s1node snode;
	    (* struct *) add_stedge snode [s1node]
	| NSdecl (_,var,Some cinit,s1) ->
	    (* create an assignment expression node so that the treatment
	       of this initialization is shared with normal assignment *)
	    let rec first_expr cinit = match cinit with
	      | Iexpr e -> Some e
	      | Ilist clinit ->
		  List.fold_left (fun e_opt cinit ->
				    begin match e_opt with
				      | None -> first_expr cinit
				      | _ -> e_opt
				    end) None clinit
	    in
	    let base_expr = match cinit with
	      | Iexpr e -> e
	      | Ilist il -> 
		  begin match first_expr (Ilist il) with
		    | None -> 
			(* initialization list cannot be totally empty *)
			assert false 
		    | Some e -> e
		  end 
	    in
	    (* to be matched with [decode_list] above *)
	    let rec encode_list cinit = match cinit with
	      | Iexpr e -> e
	      | Ilist clinit ->
		  (* special encoding of [Ilist il] in the form of a fake call
		     to [NEnop] so that:
		     - assignments in the initialization expression are taken 
		     into account
		     - decoding is easy and safe *)
		  let encoded_clinit = List.map encode_list clinit in
		  let fake_caller = { base_expr with nexpr_node = NEnop } in
		  let fake_call = 
		    { ncall_fun = fake_caller;
		      ncall_args = encoded_clinit;
		      ncall_zones_assoc = [] } in
		  { base_expr with nexpr_node = NEcall fake_call }
	    in
	    let var_expr = 
	      { base_expr with nexpr_node = NEvar (Var_info var) } in
	    let encoded_expr = match cinit with
	      | Iexpr e -> e
	      | Ilist il -> encode_list cinit in
	    let explicit_assign = NEassign (var_expr,encoded_expr) in
	    let explicit_assign = 
	      { base_expr with nexpr_node = explicit_assign } in
	    let enode = from_expr start_node explicit_assign in
	    let s1node = from_stat loops enode s1 in
	    (* oper *) add_opedge s1node snode;
	    (* struct *) add_stedge snode [enode;s1node]
	| NSswitch (e,_,cases) -> 
	    let enode = from_expr start_node e in
	    let upd_loops =
	      { loop_starts = loops.loop_starts;
		loop_switch_ends = snode :: loops.loop_switch_ends } in
	    let cnodes = List.map
	      (fun (_,sl) -> 
		 let cnode,clnodes =
		   List.fold_left 
		     (fun (stnode,s1nodes) s1 -> 
			let s1node = from_stat upd_loops stnode s1 in
			s1node,s1node::s1nodes
		     ) (enode,[]) sl
		 in
		 (* [cnode] is the node representing this [case], which is 
		    the same as the last statement in the list of statements
		    for this [case], when this list is not empty.
		    [clnodes] is the list of statements in this [case]. *)
		 cnode,List.rev clnodes
	      ) cases
	    in
	    let last_cnode =
	      List.fold_left 
		(fun prev_cnode (cnode,clnodes) -> 
		   begin match clnodes with
		     | [] -> (* no statement in this [case] *)
			 prev_cnode
		     | first_node::_ -> 
			 (* in case of fallthrough, control passes from 
			    the last statement of a [case] to the first 
			    statement of next [case].
			    If [prev_cnode] is a [break], call to 
			    [add_opedge] will do nothing. *)
			 (* oper *) add_opedge prev_cnode first_node;
			 cnode
		   end) enode cnodes
	    in
	    (* control flows from end of last case to end of switch *)
	    (* oper *) add_opedge last_cnode snode;
	    (* in absence of stable way of recognizing presence of [default]
	       case in switch (emptiness of integer map is not stable),
	       we consider the control always flows from start to end
	       of switch *)
	    (* oper *) add_opedge start_node snode;
	    let first_nodes = 
	      List.map (fun (_,clnodes) ->
			  (* special encoding so that [switch] can be seen as
			     a correct structured tree: a node [Nfwd] is
			     created for every [case] and serves as 
			     intermediate *)
			  let fnode = Node.create Nfwd in
			  add_vertex fnode;
			  begin match clnodes with
			    | [] -> ()
			    | _ -> (* struct *) add_stedge fnode clnodes
			  end;
			  fnode) cnodes
	    in
	    (* struct *) add_stedge snode (enode::first_nodes)
    end;
    add_node_in_order snode;
    snode

  let rec from_decl d =
    if debug then Coptions.lprintf 
      "[from_decl] treating function %s@." d.name;
    let dnode = Node.create (Ndecl d) in
    add_vertex dnode;
    begin match d.s with
      | Some s ->
	  let start_loops = { loop_starts = []; loop_switch_ends = [] } in
	  let snode = from_stat start_loops dnode s in
	  (* struct *) add_stedge dnode [snode]
      | None -> ()
    end;
    add_node_in_order dnode;
    dnode

  let from_file file =
    let decls = List.map from_decl file in
    nodes_in_exec_order := List.rev (!nodes_in_exec_order);
    decls,!nodes_in_exec_order

  let to_decl node =
    match get_node_kind node with
      | NKdecl -> get_decl node
      | _ -> failwith "[to_decl] should be called only on declaration"

  let to_file nodes =
    List.map to_decl nodes

end

module ConnectCFGtoPtr : Connection 
  with type node_t = CFGLangFromNormalized.Node.t 
  and type absval_t = PointWisePtrLattice.t
  and type map_t = Var.t VarMap.t
  = struct

  open CFGLangFromNormalized

  type node_t = Node.t
  type absval_t = PointWisePtrLattice.t
  type analysis_t = (node_t, absval_t * absval_t) Hashtbl.t
  type map_t = Var.t VarMap.t

  (* type used in [transfer] to compute the representant of a pointer *)
  type transfer_rep_t = 
      {
	orig_var : Var.t;
	is_index : bool;
	sum_index : int;
	is_offset : bool
      }

  (* exception used in [representative] to end the search *)
  exception End_representative of int

  (* transfer function.
     Only interesting case is the assignment to a pointer variable,
     in which case we discriminate on the form of the right-hand side.
  *)
  let transfer node cur_val =

    if debug_more then Coptions.lprintf 
      "[transfer] %a@." Node.pretty node;

    (* returns the representative pointer kind for offset/index on [var], 
       as described by [rep], with the invariant that [cur_val] does not 
       contain a loop between variables, except possible self-loops.
       [rep] is an accumulator that tells if on the current path of 
       representative pointers, we found index or offset pointer kinds. 
       [rep.orig_var] is the original variable for which we compute 
       a representant.
    *)
    let rec representative rep cur_val var =
      try
	let pval = PointWisePtrLattice.find var cur_val in
	(* [var] has itself a representant *)
	if PtrLattice.is_index pval then
	  let new_var,index = PtrLattice.get_index pval in
	  if Var.equal var new_var then
	    (* [var] is a self-index *)
	    raise (End_representative index)
	  else
	    let new_rep = { rep with is_index = true; 
			      sum_index = rep.sum_index + index } in
	    representative new_rep cur_val new_var
	else if PtrLattice.is_offset pval then
	  let new_var,_ = PtrLattice.get_offset_opt pval in
	  if Var.equal var new_var then
	    (* [var] is a self-offset *)
	    raise (End_representative 0)
	  else
	    let new_rep = { rep with is_offset = true } in
	    representative new_rep cur_val new_var
	else 
	  (* [var] has no representant *)
	  raise (End_representative 0)
      with End_representative last_index ->
	if rep.is_offset then
	  begin
	    if debug then Coptions.lprintf 
	      "[transfer] %a is represented by an offset of %a@."
	      Var.pretty rep.orig_var Var.pretty var;
	    PtrLattice.make_offset var None
	  end
	else if rep.is_index then
	  begin
	    let idx = rep.sum_index + last_index in
	    if debug then Coptions.lprintf 
	      "[transfer] %a is represented by an index of %i from %a@."
	      Var.pretty rep.orig_var idx Var.pretty var;
	    PtrLattice.make_index var idx
	  end
	else assert false
    in
    match get_node_kind node with
      | NKnone | NKstat -> cur_val

      | NKdecl ->
	  (* initially define an abstract value for parameters *)
	  let param_list = decl_get_params node in
	  List.fold_left 
	    (fun pw param ->
	       let init_val = PtrLattice.make_defined param None in
	       PointWisePtrLattice.replace param init_val pw
	    ) cur_val param_list

      | NKexpr ->
	  if expr_is_ptr_assign node then
	    match ptr_assign_get_local_lhs_var node with
	      | None -> cur_val
	      | Some lhs_var ->
		  begin
		    let rhs_val =
		      match ptr_assign_get_rhs_var node with
			| None,None -> 
			    PtrLattice.make_defined lhs_var None
			| Some rhs_var,None -> 
			    let rep = { orig_var = lhs_var; is_index = false; 
					sum_index = 0; is_offset = true } in
			    representative rep cur_val rhs_var
			| Some rhs_var,Some index ->
			    let rep = { orig_var = lhs_var; is_index = true;
					sum_index = index; is_offset = false }
			    in
			    representative rep cur_val rhs_var
			| _ -> assert false
		    in
		    PointWisePtrLattice.replace lhs_var rhs_val cur_val
		  end
	  else cur_val

  (* format function.
     Only the post-part of the analysis is relevant here.
     - If a variable is always referenced as an (un)defined or an index 
     pointer, leave it as such.
     - If a variable is always references as an (un)defined, index or offset
     pointer, make it always an offset pointer, with a fixed offset variable.
     - If a variable is sometimes references as a complex pointer, make it
     a complex pointer everywhere.

     Self-index/offset pointers are those that only reference themselves.

     This allows to exploit the pointer kind information locally to transform 
     the program.
  *)
  let format analysis =

    (* sets of variables of interest *)
    let index_vars = ref VarSet.empty in
    let self_index_vars = ref VarSet.empty in
    let offset_vars = ref VarSet.empty in
    let self_offset_vars = ref VarSet.empty in
    let defined_vars = ref VarSet.empty in
    let complex_vars = ref VarSet.empty in

    (* basic operations on sets of variables *)
    let add_to_set var set =
      set := VarSet.add var (!set) in
    let print_set set msg =
      Coptions.lprintf 
	"[format] detected %i %s pointer(s)@." (VarSet.cardinal set) msg;
      if not (VarSet.is_empty set) then 
	Coptions.lprintf "[format] %a@." 
	  (fun fmt -> (VarSet.iter (Coptions.lprintf "%a " Var.pretty))) set
    in

    (* collect variables in the sets they match *)
    Hashtbl.iter
	(fun _ (_,pwval) ->
	   PointWisePtrLattice.iter
	     (fun var pval ->
		if PtrLattice.is_index pval then
		  if PtrLattice.is_self_index var pval then
		    add_to_set var self_index_vars
		  else
		    add_to_set var index_vars
		else if PtrLattice.is_offset pval then
		  if PtrLattice.is_self_offset var pval then
		    add_to_set var self_offset_vars
		  else
		    add_to_set var offset_vars
		else if PtrLattice.is_defined pval then
		  add_to_set var defined_vars
		else if PtrLattice.is_top pval then
		  add_to_set var complex_vars
		else (* undefined pointer value *)
		  ()
	     ) pwval
	) analysis;

    (* remove references *)
    let index_vars = !index_vars in
    let self_index_vars = !self_index_vars in
    let offset_vars = !offset_vars in
    let self_offset_vars = !self_offset_vars in
    let defined_vars = !defined_vars in
    let complex_vars = !complex_vars in
    if debug then print_set index_vars "basic index";
    if debug then print_set self_index_vars "basic self-index";
    if debug then print_set offset_vars "basic offset";
    if debug then print_set self_offset_vars "basic self-offset";
    if debug then print_set defined_vars "basic defined";
    if debug then print_set complex_vars "basic complex";

    (* compute cross-referencing pointers *)
    let cross_vars = VarSet.union offset_vars index_vars in
    (* cross-referencing pointers (index/offset) cannot be self-ones *)
    let cross_rest = VarSet.inter self_offset_vars cross_vars in
    let self_offset_vars = VarSet.diff self_offset_vars cross_rest in
    let offset_vars = VarSet.union offset_vars cross_rest in
    (* offset pointers must never be complex *)
    let offset_vars = VarSet.diff offset_vars complex_vars in
    if debug then print_set offset_vars "offset"; 
    (* self-offset pointers must never be complex *)
    let self_offset_vars = VarSet.diff self_offset_vars complex_vars in
    if debug then print_set self_offset_vars "self-offset";
    (* compute sum of offset and self-offset pointers *)
    let all_offset_vars = VarSet.union offset_vars self_offset_vars in

    (* index pointers must never be offset *)
    let index_vars = VarSet.diff index_vars all_offset_vars in
    (* self-index pointers must never be offset *)
    let self_index_vars = VarSet.diff self_index_vars all_offset_vars in
    (* index pointers must never be complex *)
    let index_vars = VarSet.diff index_vars complex_vars in
    if debug then print_set index_vars "index";
    (* self_index pointers must never be complex *)
    let self_index_vars = VarSet.diff self_index_vars complex_vars in
    if debug then print_set self_index_vars "self-index";

    (* defined pointers must never be complex *)
    let defined_vars = VarSet.diff defined_vars complex_vars in

    (* associate a unique offset variable to every offset pointer *)
    let offset_map =
      VarSet.fold (fun var m ->
		     let offset_var = 
		       Info.default_var_info (var.var_name ^ "_offset") in
		     Info.set_assigned offset_var;
		     Cenv.set_var_type 
		       (Var_info offset_var) int_offset_type false;
		     VarMap.add var offset_var m
		  ) offset_vars VarMap.empty 
    in
    let offset_map =
      VarSet.fold (fun var m ->
		     let offset_var = 
		       Info.default_var_info (var.var_name ^ "_self_offset") in
		     Info.set_assigned offset_var;
		     Cenv.set_var_type 
		       (Var_info offset_var) int_offset_type false;
		     VarMap.add var offset_var m
		  ) self_offset_vars offset_map
    in

    (* compute the formatted analysis from the information just gathered *)
    let formatted_analysis = 
      Hashtbl.fold 
	(fun node (_,pwval) new_analysis ->
	   let new_pwval =
	     PointWisePtrLattice.mapi
	       (fun var pval ->
		  if VarSet.mem var index_vars then
		    (* pval = undefined/self-index/index/defined *)
		    pval 
		  else if VarSet.mem var self_index_vars then
		    (* pval = undefined/self-index/defined *)
		    pval
		  else if VarSet.mem var offset_vars then
		    (* pval = all except complex *)
		    if PtrLattice.is_defined pval then
		      (* explicit the offset variable for initialization *)
		      let offset_var = VarMap.find var offset_map in
		      PtrLattice.make_defined var (Some offset_var)
		    else if PtrLattice.is_index pval 
		      || PtrLattice.is_offset pval then
			(* explicit the offset variable *)
			let avar = PtrLattice.get_variable pval in
			let offset_var = VarMap.find var offset_map in
			PtrLattice.make_offset avar (Some offset_var)
		    else (* undefined *)
		      pval
		  else if VarSet.mem var self_offset_vars then
		    (* pval = undefined/self-index/self-offset/defined *)
		    if PtrLattice.is_defined pval then
		      (* explicit the offset variable for initialization *)
		      let offset_var = VarMap.find var offset_map in
		      PtrLattice.make_defined var (Some offset_var)
		    else if PtrLattice.is_index pval 
		      || PtrLattice.is_offset pval then
			(* explicit the offset variable *)
			let avar = PtrLattice.get_variable pval in
			assert (Var.equal avar var);
			let offset_var = VarMap.find var offset_map in
			PtrLattice.make_offset var (Some offset_var)
		    else (* undefined *)
		      pval
		  else if VarSet.mem var defined_vars then
		    (* pval = all except complex *)
		    PtrLattice.make_defined var None
		  else if VarSet.mem var complex_vars then
		    (* pval = any one is possible
		       Destroy any information associated to [var]. *)
		    PtrLattice.top
		  else
		    (* pval = undefined *)
		    pval
	       ) pwval
	   in
	   Hashtbl.add new_analysis node 
	     (PointWisePtrLattice.bottom,new_pwval);
	   new_analysis
	) analysis (Hashtbl.create 0)
    in
    formatted_analysis,offset_map

  (* exception used to share the default treatment in [sub_transform] *)
  exception Rec_transform

  (* transformation on an individual node.
     takes as input a node [node] in the graph(s) previously created.
     returns a pair consisting of:
     - a main part, i.e. a potentially new node that is not connected 
     to the graph(s), that corresponds to the transformed node.
     - an addon part, i.e. a potentially new node that corresponds to
     the resulting pointer.

     On an assignment 
          [p = q], 
     the main part could be e.g. 
          [p_offset = q_offset] 
     and the addon part could be 
          [r + p_offset].
     The statement 
          [p = q;] 
     would be transformed into 
          [p_offset = q_offset;]
     and the statement 
          [return (p = q);] 
     into the more complex:
          [return (p_offset = q_offset,r + p_offset);]

     The results of the data-flow analysis [analysis] contain only 
     the relevant information for code transformation. Other intermediate
     results of the analysis have been erased after the analysis phase.
     Only the post-part of the analysis is relevant here.
  *)
  let rec sub_transform analysis offset_vars offset_map node =

    (* apply [sub_transform] recursively on sub-nodes *)
    let sub_nodes = children node in
    let new_sub_nodes = 
      List.map (sub_transform analysis offset_vars offset_map) sub_nodes
    in

    (* every offset variable that is used in the code must be stored in 
       the repository [offset_vars], to be declared later on by a call to
       [introduce_new_vars]. *)
    let store_offset_var offset_var =
      offset_vars := VarSet.add offset_var (!offset_vars)
    in

    (* treat declaration/statement/expression separately *)
    try match get_node_kind node with
      | NKnone | NKstat -> raise Rec_transform

      | NKdecl -> 
	  (* no type change needed here, keep only main part *)
	  let new_sub_nodes = List.map fst new_sub_nodes in
	  let new_node = change_sub_components node new_sub_nodes in
	  let param_list = decl_get_params node in
	  let param_offset_vars =
	    List.fold_left 
	      (fun set param ->
		 try 
		   let offset_var = VarMap.find param offset_map in
		   if VarSet.mem offset_var (!offset_vars) then
		     VarSet.add offset_var set
		   else set
		 with Not_found -> set
	      ) VarSet.empty param_list
	  in
	  let other_offset_vars = 
	    VarSet.diff (!offset_vars) param_offset_vars in
	  let new_node = introduce_new_vars new_node 
	    (VarSet.elements other_offset_vars) (* zero_init= *)false
	  in
	  let new_node = introduce_new_vars new_node 
	    (VarSet.elements param_offset_vars) (* zero_init= *)true
	  in
	  (new_node,None) (* addon part has no meaning here *)

      | NKexpr ->
	  begin
	    (* transformation is possible only if analysis provides 
	       some information *)
	    let _,aval = Hashtbl.find analysis node in

	    (* 3 sub-functions that share code between cases below *)

	    (* returns a pointer read that corresponds to the abstract value
	       [aval], with other elements taken in [node] 
	    *)
	    let make_pointer_read node pval =
	      if PtrLattice.is_alias pval then
		(* rewrite alias of v as v *)
		let new_var = PtrLattice.get_alias pval in
		change_in_var node new_var
	      else if PtrLattice.is_index pval then
		(* rewrite constant offset i of v as v+i *)
		let new_var,index = PtrLattice.get_index pval in
		change_in_ptr_var_add_cst node new_var index
	      else if PtrLattice.is_offset pval then
		(* rewrite offset o of v as v+o *)
		let new_var,offset_var = PtrLattice.get_offset pval in
		store_offset_var offset_var;
		change_in_ptr_var_add_var node new_var offset_var
	      else if PtrLattice.is_defined pval then
		(* rewrite possible assignment to v as v *)
		let new_var,_ = PtrLattice.get_defined_opt pval in
		change_in_var node new_var
	      else node
	    in

	    (* returns an offset assignment from the abstract value [rhs_val]
	       to the variable [offset_lhs_var], with the possible addition
	       of an expression [add_offset_opt]. Other elements are taken
	       in [node]. 
	    *)
	    let make_offset_assign 
		node offset_lhs_var rhs_val add_offset_opt is_incr_decr =
	      if PtrLattice.is_index rhs_val then
		begin
		  (* it cannot be an increment/decrement *)
		  assert (not is_incr_decr);
		  (* [offset_lhs_var] is assigned a constant *)
		  let (_,index) = PtrLattice.get_index rhs_val in
		  match add_offset_opt with
		    | None -> 
			change_in_var_assign_cst node offset_lhs_var index
		    | Some offset_expr ->
			let add_expr = make_int_expr_add_cst offset_expr index
			in
			change_in_var_assign_expr node offset_lhs_var add_expr
		end
	      else if PtrLattice.is_offset rhs_val then
		(* [offset_lhs_var] is assigned another offset *)
		let (_,offset_rhs_var) = 
		  PtrLattice.get_offset rhs_val in
		store_offset_var offset_rhs_var;
		match add_offset_opt with
		  | None -> 
		      (* only possible case for an increment/decrement *)
		      if is_incr_decr then
			change_in_int_incr_assign node offset_lhs_var
		      else
			change_in_var_assign_var 
			  node offset_lhs_var offset_rhs_var
		  | Some offset_expr ->
		      begin
			(* it cannot be an increment/decrement *)
			assert (not is_incr_decr);
			let add_expr = 
			  make_int_expr_add_var offset_expr offset_rhs_var in
			change_in_var_assign_expr node offset_lhs_var add_expr
		      end
	      else
		begin
		  (* it cannot be an increment/decrement *)
		  assert (not is_incr_decr);
		  match add_offset_opt with
		    | None -> (* [offset_lhs_var] is reset *)
			change_in_var_assign_cst node offset_lhs_var 0
		    | Some offset_expr ->
			change_in_var_assign_expr 
			  node offset_lhs_var offset_expr
		end
	    in

	    (* returns a pointer assignment from [new_rhs_node] to [lhs_node],
	       with [new_rhs_type_is_ptr] telling if the new right-hand side
	       is still of pointer type or not. Other elements are taken
	       in [node]. 
	    *)
	    let keep_pointer_assignment 
		node new_rhs_type_is_ptr lhs_node new_rhs_node is_incr_decr =
	      (* pointer assignment must be kept.
		 The only possible problem is that the right-hand
		 side might be a pointer assignment too, that could
		 have been transformed into an offset assignment. *)
	      if new_rhs_type_is_ptr then
		if is_incr_decr then
		  (* nothing to change *)
		  node
		else
		  (* keep old lhs and new rhs *)
		  change_sub_components node [lhs_node;new_rhs_node]
	      else
		begin
		  (* it cannot be an increment/decrement *)
		  assert (not is_incr_decr);
		  (* The rhs is now an offset assignment.
		     In all cases, the analysis must have computed 
		     an index or an offset for the right-hand side.
		     Create an equivalent sequence of assignments. *)
		  let rhs_val =
		    match ptr_assign_get_rhs_var node with
		      | Some rhs_var,_ -> 
			  PointWisePtrLattice.find rhs_var aval
		      | _ -> assert false
		  in
		  let ptr_node = make_pointer_read node rhs_val in
		  let assign_node = 
		    change_sub_components node [lhs_node;ptr_node]
		  in
		  make_seq_expr new_rhs_node assign_node
		end
	    in

	    (* beginning of transformation for expressions *)
	    
	    (* reading some pointer variable.
	       This is called also on pointer write, but the result
	       of this rewrite is ignored by the calling [sub_transform]
	       on pointer assignment. *)
	    if expr_is_local_ptr_var node then
	      let var = expr_var_get_var node in
	      let pval = PointWisePtrLattice.find var aval in 
	      (make_pointer_read node pval,
	       None) (* nothing to add to make it a pointer *)

	    (* writing some pointer variable *)
	    else if expr_is_ptr_assign node then
	      (* 2 possibilities: it may be a real assignment or 
		 an increment/decrement operation *)
	      let is_incr_decr = List.length sub_nodes = 1 in
	      assert (List.length sub_nodes = List.length new_sub_nodes);
	      let lhs_node,new_rhs_node =
		if is_incr_decr then
		  (* increment/decrement *)
		  list1 sub_nodes,list1 new_sub_nodes
		else
		  (* assignment *)
		  fst (list2 sub_nodes),snd (list2 new_sub_nodes)
	      in
	      (* separate main part from addon part *)
	      let new_rhs_node,new_rhs_node_addon = new_rhs_node in
	      let new_rhs_is_assign = expr_is_assign new_rhs_node in
	      let new_rhs_type_is_ptr = expr_type_is_ptr new_rhs_node in
	      match ptr_assign_get_local_lhs_var node with
		| None -> 
		    (keep_pointer_assignment node 
		       new_rhs_type_is_ptr lhs_node new_rhs_node is_incr_decr,
		     None) (* nothing to add to make it a pointer *)
		     
		| Some lhs_var ->
		    let lhs_val = PointWisePtrLattice.find lhs_var aval in 

		    (* share addon part used in offset/defined cases *)
		    let addon_node = 
		      if is_incr_decr then
			(* [new_rhs_node] must be a variable here,
			   in the offset/defined cases *)
			change_in_ptr_incr node new_rhs_node true
		      else
			make_pointer_read node lhs_val 
		    in
		    let wrap_addon node = node,Some addon_node in

		    if PtrLattice.is_index lhs_val then
		      (* assignment to [lhs_var] not useful, since reading
			 [lhs_var] will be replaced by reading its alias
			 or its constant offset from some variable.
			 Contains the test [PtrLattice.is_alias lhs_val]. *)
		      if is_incr_decr then
			(change_in_ptr_incr node new_rhs_node false,
			 None) (* nothing to add to make it a pointer *)
		      else
			(* just propagate the right-hand side *)
			(new_rhs_node,new_rhs_node_addon)

		    else if PtrLattice.is_offset lhs_val then
		      let (new_lhs_var,offset_lhs_var) =
			PtrLattice.get_offset lhs_val in
		      store_offset_var offset_lhs_var;
		      (* right-hand side can only be another variable or
			 another pointer assignment.
			 In either case, the analysis must have computed 
			 an index or an offset for the right-hand side. *)
		      let rhs_val =
			match ptr_assign_get_rhs_var node with
			  | Some rhs_var,_ -> 
			      PointWisePtrLattice.find rhs_var aval
			  | _ -> assert false
		      in
		      (* The pointer assignment must be changed into
			 an offset assignment. 4 cases are possible depending
			 on the new right-hand side computed :
			 - the rhs is still a pointer assignment, e.g. in
			      p = q = malloc(...);
			   Create an equivalent sequence of assignments, e.g.:
			      q = malloc(...), p_offset = 0;
			 - the rhs is itself an offset assignment. Use it.
			 - the rhs is the sum of a pointer and an integer
			   expression. Ignore the pointer and keep 
			   the expression.
			 - the rhs is a pointer. Ignore it. *)
		      if new_rhs_is_assign then
			begin
			  (* it cannot be an increment/decrement *)
			  assert (not is_incr_decr);
			  if new_rhs_type_is_ptr then	
			    (* The rhs is still a pointer assignment.
			       Create an equivalent sequence of assignments. *)
			    let offset_node = 
			      make_offset_assign 
				node offset_lhs_var rhs_val None false
			    in
			    wrap_addon (make_seq_expr new_rhs_node offset_node)
			  else
			    (* The rhs is itself an offset assignment. 
			       Use it. *)
			    wrap_addon (change_in_var_assign_expr 
					  node offset_lhs_var new_rhs_node)
			end
		      else
			(* The rhs can be:
			   - a pointer
			   - the sum of a pointer and an integer expression.
			   The last case can be the original source code or 
			   due to the transformation of an offset pointer 
			   or an index pointer.
			*)
			if is_incr_decr then
			  (* do not compute [off_opt] here, it would be equal
			     to the offset variable, because the rhs has been
			     translated to the sum var + offset_var *)
			  wrap_addon (make_offset_assign 
					node offset_lhs_var rhs_val None true)
			else
			  let var_opt,off_opt = 
			    get_ptr_add_on_var_opt new_rhs_node in
			  let off_opt = match off_opt with
			    | None -> None
			    | Some off_node ->
				if expr_is_local_var off_node then
				  (* rule out transformation of offset *)
				  let off_var = expr_var_get_var off_node in
				  if VarSet.mem off_var (!offset_vars) then
				    (* here, offset is only the transformation
				       on the sub-node. Same as the increment/
				       decrement case. Ignore it. *)
				    None
				  else off_opt
				else 
				  match var_opt with
				    | Some var ->
					(* rule out transformation of index *)
					let var_val = PointWisePtrLattice.find 
					  var aval in 
					if PtrLattice.is_index var_val
					  && not (PtrLattice.is_alias var_val)
					then None
					else off_opt
				    | None -> off_opt
			  in    
			  wrap_addon 
			    (make_offset_assign 
			       node offset_lhs_var rhs_val off_opt false)

		    else if PtrLattice.is_defined lhs_val then
		      let assign_node = 
			keep_pointer_assignment node new_rhs_type_is_ptr 
			  lhs_node new_rhs_node is_incr_decr
		      in
		      match PtrLattice.get_defined_opt lhs_val with
			| _,Some offset_var ->
			    store_offset_var offset_var;
			    let reset_node = 
			      change_in_var_assign_cst node offset_var 0 in
			    (* sequence in this order due to possible effects
			       in [assign_node]. Use [wrap_addon] to return 
			       pointer. *) 
			    wrap_addon (make_seq_expr assign_node reset_node)
			| _,None -> (* like in the default assignment case *)
			    (assign_node,
			     None) (* nothing to add to make it a pointer *)

		    else (* default: not any of index/offset/defined pointer *)
		      (keep_pointer_assignment node new_rhs_type_is_ptr 
			 lhs_node new_rhs_node is_incr_decr,
		       None) (* nothing to add to make it a pointer *)

	    else raise Rec_transform
	  end

    with Rec_transform | Not_found -> 
      (* return same expression on new sub-nodes.
	 Only subtlety is to use the addon part of an expression sub-node when
	 the new sub-node is not of pointer type while the original sub-node
	 was of pointer type. *)
      let new_sub_nodes =
	List.map2 (fun sub_node (new_main,new_addon) ->
		     begin match get_node_kind sub_node with
		       | NKexpr ->
			   if expr_type_is_ptr sub_node
			     && not (expr_type_is_ptr new_main) then
			       match new_addon with
				 | Some new_addon ->
				     assert (expr_type_is_ptr new_addon);
				     make_seq_expr new_main new_addon
				 | None -> assert false
			   else
			     new_main
		       | _ -> new_main
		     end
		  ) sub_nodes new_sub_nodes
      in
      (change_sub_components node new_sub_nodes,
       None) (* addon part empty here *)

  let transform analysis offset_map decls =
    let offset_vars = ref VarSet.empty in
    List.map (fun decl ->
		let new_decl,_ = 
		  sub_transform analysis offset_vars offset_map decl in
		offset_vars := VarSet.empty;
		new_decl
	     ) decls

end

module LocalPtrAnalysis = Make_DataFlowAnalysis(Var)(CFGLangFromNormalized)
  (PointWisePtrLattice)(ConnectCFGtoPtr)


(*****************************************************************************
 *                                                                           *
 * 		External interface for local pointer analysis		     *
 *                                                                           *
 *****************************************************************************)

let local_aliasing_transform () =
  (* necessary prefix to translate the hash-table of functions in 
     the normalized code into a list of function representatives,
     as defined by type [func_t] above *)
  let file = Hashtbl.fold 
    (fun name (spec,typ,f,s,loc) funcs ->
       { name = name; spec = spec; typ = typ; f = f; s = s; loc = loc } 
       :: funcs
    ) Cenv.c_functions []
  in

  if debug then Coptions.lprintf 
    "[local_aliasing_transform] %i functions to treat@." (List.length file); 

  (* build control-flow graph *)
  let decls,all = CFGLangFromNormalized.from_file file in
  (* perform local pointer analysis *)
  let raw_analysis = LocalPtrAnalysis.compute all in
  (* format results of the analysis *)
  let analysis,offset_map = ConnectCFGtoPtr.format raw_analysis in
  (* transform the program using the analysis *)
  let new_decls = ConnectCFGtoPtr.transform analysis offset_map decls in
  (* return the new program *)
  let file = CFGLangFromNormalized.to_file new_decls in

  if debug then Coptions.lprintf 
    "[local_aliasing_transform] %i functions treated@." (List.length file);

  (* necessary suffix to translate the list of function representatives
     to the hash-table format *)
  List.iter (fun { name = name; spec = spec; typ = typ; 
		   f = f; s = s; loc = loc } ->
	       Cenv.add_c_fun name (spec,typ,f,s,loc)) file
