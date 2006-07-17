
open Info
open Clogic
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
let list1 l = match l with [a] -> a | _ -> assert false
let list2 l = match l with [a;b] -> a,b | _ -> assert false
let list3 l = match l with [a;b;c] -> a,b,c | _ -> assert false
let list4 l = match l with [a;b;c;d] -> a,b,c,d | _ -> assert false
let list5 l = match l with [a;b;c;d;e] -> a,b,c,d,e | _ -> assert false


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

    (* list of successors in the operational graph, e.g.
       - surrounding expression for a sub-expression
       - [else] and [then] branches for an [if] test expression
       ... *)
  val successors : Node.t -> Node.t list (* order does not matter *)
    (* list of predecessors in the operational graph *)
  val predecessors : Node.t -> Node.t list (* order does not matter *)
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

module CFGLangFromNormalized : sig
  include InterLang with type var_t = Var.t and type decl_t = func_t

  (* successors in both structural and logical graph *)

    (* list of successors in the structural graph, e.g.
       - list of operands of an operation
       - caller and arguments of a function call
       - list of statements in a block statement 
       ... *)
  val code_children : Node.t -> Node.t list (* order matters *)
    (* list of successors in the logical graph, e.g.
       - loop annotation of a loop
       - spec of block of code
       - invariant of a loop annotation
       - sub-predicate in an invariant
       - term in a predicate
       ... *)
  val logic_children : Node.t -> Node.t list (* order matters *)
    (* beginning of logical block
       Used for \old annotations and specifications. *)
  val logic_begin : Node.t -> Node.t
    (* end of logical block
       Used for annotations and specifications. *)
  val logic_end : Node.t -> Node.t
  
  (* query functions *)
  (* 8 kinds of nodes: 
     for code: expression/statement/declaration
     for logic: specification/loop annotation/term/predicate
     for internal use: internal
  *)
  type node_kind = 
    | NKexpr | NKstat | NKdecl | NKspec | NKannot | NKterm | NKpred | NKnone
    (* returns the node's kind *)
  val get_node_kind : Node.t -> node_kind
    (* returns the function's parameters *)
  val decl_get_params : Node.t -> var_t list
    (* is it a return statement ? *)
  val stat_is_return : Node.t -> bool
    (* is it an assert statement ? *)
  val stat_is_assert : Node.t -> bool
    (* is it a loop statement ? *)
  val stat_is_loop : Node.t -> bool
    (* is it a spec statement ? *)
  val stat_is_spec : Node.t -> bool
    (* is it a label statement ? *)
  val stat_is_label : Node.t -> bool
    (* get the label associated with this label statement *)
  val stat_get_label : Node.t -> string
    (* is the type of this expression a pointer type ? *)
  val expr_type_is_ptr : Node.t -> bool
    (* is this expression a -local- variable ? *)
  val expr_is_local_var : Node.t -> bool
    (* is this term/expression a -local- variable of pointer type ? *)
  val termexpr_is_local_ptr_var : Node.t -> bool
    (* returns the variable in this term/expression over a variable *)
  val termexpr_var_get_var : Node.t -> var_t
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
    (* is this term/predicate an \old one ? *)
  val termpred_is_old : Node.t -> bool
    (* is this term/predicate an \at one ? *)
  val termpred_is_at : Node.t -> bool
    (* get the label associated with this \at term/predicate *)
  val termpred_get_label : Node.t -> string

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
    (* create a new node term/expression + term/expression *)
  val make_int_termexpr_add_termexpr : Node.t -> Node.t -> Node.t
    (* create a new node pointer expression + constant *)
  val make_ptr_expr_add_cst : Node.t -> int -> Node.t
    (* make this node be a term/expression over a variable *)
  val change_in_var : Node.t -> var_t -> Node.t
    (* make this node be a term/expression of a sum variable + constant *)
  val change_in_ptr_var_add_cst : Node.t -> var_t -> int -> Node.t
    (* make this node be a term/expression of a sum variable + variable *)
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
       materialized as an integer addition, that is assigned to
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

end = struct
  
  type var_t = Var.t
  type decl_t = func_t

  type node_kind = 
    | NKexpr | NKstat | NKdecl | NKspec | NKannot | NKterm | NKpred | NKnone

  (* special node [Nfwd] used for special purposes:
     - during construction to reference future nodes
     - to translate [switch] into appropriate structural tree
     - in loops to create a destination node for back edge
     ...
     It carries a boolean [true] when part of the structural graph,
     [false] when part of the logical graph.
  *)
  type norm_node = 
      (* coding constructs *)
    | Nexpr of nexpr
    | Nstat of nstatement
    | Ndecl of decl_t
      (* logical constructs *)
    | Nspec of nspec
    | Nannot of nloop_annot
    | Nterm of nterm
    | Npred of npredicate
      (* special construct *)
    | Nfwd of bool

  (* type of labels on edges in the CFG *)
  module NodeRelation = struct
    type t =
      | Operational    (* edge in the operational graph *)
      | StructuralDown (* edge to first sub-node in the structural graph *)
      | StructuralSame (* other edges in the structural graph *)
      | LogicalDown    (* edge to first sub-node in the logical graph *)
      | LogicalSame    (* other edges in the logical graph *)
      | LogicalBegin   (* edge to first node in logical block *)
      | LogicalEnd     (* edge to last node in logical block *)
    (* arbitrary index to provide total ordering *)
    let index r = match r with
      | Operational -> 0
      | StructuralDown -> 1
      | StructuralSame -> 2
      | LogicalDown -> 3
      | LogicalSame -> 4
      | LogicalBegin -> 5
      | LogicalEnd -> 6
    let compare r1 r2 = Pervasives.compare (index r1) (index r2)
    (* if not stated otherwise, an edge is an operational one *)
    let default = Operational
  end

  (* We use here an abstract imperative labeled graph.
     Labels are of 3 kinds :
         - operational labels form a graph that respects evaluation order,
     to facilitate data-flow analysis
         - structural labels form a graph that respects the hierarchical order
     between expressions and statements, e.g. with [StructuralDown] labels from
     an expression to its first sub-expression, and [StructuralSame] label 
     from a sub-expression to the next sub-expression at the same level.
         - logical labels form a graph similar to the structural graph, except
     it is used for logical properties on the code instead of the code itself.

     Beware that since the operational graph is used for data-flow analysis 
     computation, the action associated to the node will be repeated when
     going through this node in the graph. This makes it necessary sometimes
     to create internal nodes whose sole purpose is to connect parts of 
     the graph with no associated action.
     This is not the case with the structural or logical graph.
  *)

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
      | Nspec _ -> Format.fprintf fmt "Nspec"
      | Nannot _ -> Format.fprintf fmt "Nannot"
      | Nterm _ -> Format.fprintf fmt "Nterm"
      | Npred _ -> Format.fprintf fmt "Npred"
      | Nfwd _ -> Format.fprintf fmt "Nfwd"
  end
  module Edge = Self.E

  (* shortcut query functions *)

  let get_node_kind node =
    match Node.label node with
      | Nexpr _ -> NKexpr
      | Nstat _ -> NKstat
      | Ndecl _ -> NKdecl
      | Nspec _ -> NKspec
      | Nannot _ -> NKannot
      | Nterm _ -> NKterm
      | Npred _ -> NKpred
      | Nfwd _ -> NKnone

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

  let get_spec node = 
    match Node.label node with
      | Nspec s -> s
      | _ -> failwith "[get_spec] should be called only on specification"
	  
  let get_annot node = 
    match Node.label node with
      | Nannot a -> a
      | _ -> failwith "[get_annot] should be called only on loop annotation"

  let get_t node = 
    match Node.label node with
      | Nterm t -> t
      | _ -> failwith "[get_t] should be called only on term"
  let get_term node = (get_t node).nterm_node

  let get_p node = 
    match Node.label node with
      | Npred p -> p
      | _ -> failwith "[get_p] should be called only on predicate"
  let get_predicate node = (get_p node).npred_node

  let fwd_is_structural node = match Node.label node with
    | Nfwd b -> b
    | _ -> failwith "[fwd_is_structural] should be called only on forward node"
  let fwd_is_logical node = not (fwd_is_structural node)

  (* more elaborate query functions related to pointer usage *)

  let is_pointer_type ctyp = match ctyp.Ctypes.ctype_node with
    | Ctypes.Tvar _ -> assert false (* not allowed in code *)
    | Ctypes.Tarray _ | Ctypes.Tpointer _ -> true
    | _ -> false

  let var_is_pointer var =
    is_pointer_type var.var_type

  let var_is_local var =
    not var.var_is_static

  let termpred_is_old node = 
    match get_node_kind node with
      | NKpred -> 
	  begin match get_predicate node with
	    | NPold _ -> true
	    | _ -> false
	  end
      | NKterm ->
	  begin match get_term node with
	    | NTold _ -> true
	    | _ -> false
	  end
      | _ -> false

  let termpred_is_at node = 
    match get_node_kind node with
      | NKpred -> 
	  begin match get_predicate node with
	    | NPat _ -> true
	    | _ -> false
	  end
      | NKterm ->
	  begin match get_term node with
	    | NTat _ -> true
	    | _ -> false
	  end
      | _ -> false

  let termpred_get_label node = 
    match get_node_kind node with
      | NKpred -> 
	  begin match get_predicate node with
	    | NPat (_,lab) -> lab
	    | _ -> assert false
	  end
      | NKterm ->
	  begin match get_term node with
	    | NTat (_,lab) -> lab
	    | _ -> assert false
	  end
      | _ -> assert false

  let decl_get_params node =
    (get_decl node).f.args

  let stat_is_return node =
    match get_stat node with NSreturn _ -> true | _ -> false

  let stat_is_assert node =
    match get_stat node with NSassert _ -> true | _ -> false

  let stat_is_loop node =
    match get_stat node with 
      | NSwhile _ | NSdowhile _ | NSfor _ -> true | _ -> false

  let stat_is_spec node =
    match get_stat node with NSspec _ -> true | _ -> false

  let stat_is_label node =
    match get_stat node with NSlabel _ | NSlogic_label _ -> true | _ -> false

  let stat_get_label node =
    match get_stat node with 
      | NSlabel (lab,_) | NSlogic_label lab -> lab | _ -> assert false

  let expr_type_is_ptr node = is_pointer_type (get_e node).nexpr_type

  let expr_is_local_var node = match get_expr node with
    | NEvar (Var_info var) -> var_is_local var
    | _ -> false

  let termexpr_is_local_ptr_var node =
    match get_node_kind node with
      | NKexpr -> 
	  begin match get_expr node with
	    | NEvar (Var_info var) -> var_is_pointer var && var_is_local var
	    | _ -> false
	  end
      | NKterm ->
	  begin match get_term node with
	    | NTvar var -> var_is_pointer var && var_is_local var
	    | _ -> false
	  end
      | _ -> assert false

  let termexpr_var_get_var node =
    match get_node_kind node with
      | NKexpr -> 
	  begin match get_expr node with
	    | NEvar (Var_info var) -> var
	    | _ -> assert false
	  end
      | NKterm ->
	  begin match get_term node with
	    | NTvar var -> var
	    | _ -> assert false
	  end
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
			| NEconstant (IntConstant s) ->
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

  (* add a node *)
  let add_vertex = Self.add_vertex graph

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

  (* hierarchical successors. Used for structural and logical successors. *)
  let succ edge n = 
    let el = Self.succ_e graph n in
    let el = List.filter (fun e -> Edge.label e = edge) el in
    match List.map Edge.dst el with
      | [] -> None
      | [a] -> Some a
      | _ -> failwith ("[succ edge n] should find at most one successor"
		       ^ " for node [n]")
  let child is_structural n = 
    if is_structural then
      succ NodeRelation.StructuralDown n
    else
      succ NodeRelation.LogicalDown n
  let sibling is_structural n =
    if is_structural then
      succ NodeRelation.StructuralSame n
    else
      succ NodeRelation.LogicalSame n
  let rec siblings is_structural n =
    match sibling is_structural n with
      | None -> []
      | Some m -> m :: (siblings is_structural m)
  let children is_structural n =
    match child is_structural n with
      | None -> []
      | Some m -> m :: (siblings is_structural m)

  (* structural successors. Only [StructuralDown] and [StructuralSame]
     labels should be taken into account. *)
  let code_children = children (* is_structural= *)true

  (* logical successors. Only [LogicalDown] and [LogicalSame]
     labels should be taken into account. *)
  let logic_children = children (* is_structural= *)false

  let logic_begin n = 
    match succ NodeRelation.LogicalBegin n with
      | Some nb -> nb
      | None -> failwith "no logical beginning node found"
  let logic_end n = 
    match succ NodeRelation.LogicalEnd n with
      | Some ne -> ne
      | None -> failwith "no logical end node found"

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
    
  (* add hierarchical edges. Used for adding structural and logical edges. *)
  let add_edge edge v1 v2 =
    let e = Edge.create v1 edge v2 in
    Self.add_edge_e graph e
  let add_edges is_structural v vl = 
    let add_down_edge = 
      if is_structural then
	add_edge NodeRelation.StructuralDown 
      else
	add_edge NodeRelation.LogicalDown
    in
    let add_same_edge = 
      if is_structural then
	add_edge NodeRelation.StructuralSame
      else
	add_edge NodeRelation.LogicalSame
    in
    let rec add_same_edges vl = match vl with
      | a::b::r -> add_same_edge a b; add_same_edges (b::r)
      | _ -> ()
    in
    match vl with
      | [] -> ()
      | a::r -> add_down_edge v a; add_same_edges vl

  (* add structural edges: a [StructuralDown] edge from [v] to the first
     node in the list [vl], and [StructuralSame] edges between successive
     nodes in [vl]. *)
  let add_stedge = add_edges (* is_structural= *)true

  (* add logical edges: a [LogicalDown] edge from [v] to the first
     node in the list [vl], and [LogicalSame] edges between successive
     nodes in [vl]. *)
  let add_logedge = add_edges (* is_structural= *)false

  (* add logical block edge *)
  let add_begedge = add_edge NodeRelation.LogicalBegin
  let add_endedge = add_edge NodeRelation.LogicalEnd

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
    let cst_e = NEconstant (IntConstant (string_of_int cst)) in
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

  let make_int_termexpr_add_termexpr node1 node2 =
    match get_node_kind node1 with
      | NKexpr -> 
	  let e1 = get_e node1 in
	  let e2 = get_e node2 in
	  let typ = e1.nexpr_type in
	  let op = match typ.Ctypes.ctype_node with 
	    | Ctypes.Tint ik -> Badd_int ik
	    | _ -> failwith ("[make_int_termexpr_add_termexpr] should only"
			     ^ " be called on integer expression") in
	  let new_e = NEbinary (e1,op,e2) in
	  let new_e = { e1 with nexpr_node = new_e } in
	  Node.create (Nexpr new_e)    
      | NKterm ->
	  let t1 = get_t node1 in
	  let t2 = get_t node2 in
	  let typ = t1.nterm_type in
	  let op = Clogic.Badd in
	  let new_t = NTbinop (t1,op,t2) in
	  let new_t = { t1 with nterm_node = new_t } in
	  Node.create (Nterm new_t)
      | _ -> assert false

  (* expr + neg_cst is coded as expr + (-abs(neg_cst))
     This format is expected by [Cconst] module. *)
  let make_ptr_expr_add_cst node cst =
    let e = get_e node in
    let cst_e = NEconstant (IntConstant (string_of_int (abs cst))) in
    let cst_e = { e with nexpr_node = cst_e; nexpr_type = int_offset_type } in
    let cst_e = if cst >= 0 then cst_e else
      { cst_e with nexpr_node = NEunary (Uminus,cst_e) } in
    let new_e = NEbinary (e,Badd_pointer_int,cst_e) in
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  let change_in_var node var =
    match get_node_kind node with
      | NKexpr -> 
	  let e = get_e node in
	  let new_e = NEvar (Var_info var) in
	  let new_e = { e with nexpr_node = new_e } in
	  Node.create (Nexpr new_e)
      | NKterm ->
	  let t = get_t node in
	  let new_t = NTvar var in
	  let new_t = { t with nterm_node = new_t } in
	  Node.create (Nterm new_t)
      | _ -> assert false

  (* var + neg_cst is coded as var + (-abs(neg_cst))
     This format is expected by [Cconst] module. *)
  let change_in_ptr_var_add_cst node var offset =
    match get_node_kind node with
      | NKexpr -> 
	  let e = get_e node in
	  let var_e = NEvar (Var_info var) in
	  let var_e = { e with nexpr_node = var_e } in
	  let cst_e = NEconstant (IntConstant (string_of_int (abs offset))) in
	  let cst_e = { e with nexpr_node = cst_e; 
			  nexpr_type = int_offset_type } in
	  let cst_e = if offset >= 0 then cst_e else
	    { cst_e with nexpr_node = NEunary (Uminus,cst_e) } in
	  let new_e = NEbinary (var_e, Badd_pointer_int, cst_e) in
	  let new_e = { e with nexpr_node = new_e } in
	  Node.create (Nexpr new_e)
      | NKterm ->
	  let t = get_t node in
	  let var_t = NTvar var in
	  let var_t = { t with nterm_node = var_t } in
	  let cst_t = NTconstant (IntConstant (string_of_int (abs offset))) in
	  let cst_t = { t with nterm_node = cst_t; 
			  nterm_type = int_offset_type } in
	  let cst_t = if offset >= 0 then cst_t else
	    { cst_t with nterm_node = NTunop (Clogic.Uminus,cst_t) } in
	  let new_t = NTbinop (var_t, Clogic.Badd, cst_t) in
	  let new_t = { t with nterm_node = new_t } in
	  Node.create (Nterm new_t)
      | _ -> assert false

  let change_in_ptr_var_add_var node var offset_var =
    match get_node_kind node with
      | NKexpr -> 
	  let e = get_e node in
	  let var_e = NEvar (Var_info var) in
	  let var_e = { e with nexpr_node = var_e } in
	  let cst_e = NEvar (Var_info offset_var) in
	  let cst_e = { e with nexpr_node = cst_e; 
			  nexpr_type = int_offset_type } in
	  let new_e = NEbinary (var_e, Badd_pointer_int, cst_e) in
	  let new_e = { e with nexpr_node = new_e } in
	  Node.create (Nexpr new_e)
      | NKterm ->
	  let t = get_t node in
	  let var_t = NTvar var in
	  let var_t = { t with nterm_node = var_t } in
	  let cst_t = NTvar offset_var in
	  let cst_t = { t with nterm_node = cst_t; 
			  nterm_type = int_offset_type } in
	  let new_t = NTbinop (var_t, Clogic.Badd, cst_t) in
	  let new_t = { t with nterm_node = new_t } in
	  Node.create (Nterm new_t)
      | _ -> assert false

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
    let cst_e = NEconstant (IntConstant (string_of_int index)) in
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

  (* exception used to report unexpected encoding in [change_sub_components]
     or its sub-functions. *)
  exception Bad_encoding

  let change_sub_components_in_stat node sub_nodes =
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
    let new_s = match s.nst_node with
      | NSnop | NSlogic_label _ ->
	  assert (List.length sub_nodes = 0);
	  s.nst_node
      | NSassert _ ->
	  assert (List.length sub_nodes = 1);
	  let new_p1 = list1 sub_nodes in
	  let new_p1 = get_p new_p1 in
	  NSassert new_p1	  
      | NSexpr e -> 
	  assert (List.length sub_nodes = 1);
	  let new_e = list1 sub_nodes in
	  let new_e = get_e new_e in
	  statement_expr_or_nop new_e
      | NSif (e,s1,s2) ->
	  assert (List.length sub_nodes = 3);
	  let new_e,new_s1,new_s2 = list3 sub_nodes in
	  let new_e,new_s1,new_s2 
	    = get_e new_e,get_s new_s1,get_s new_s2 in
	  let new_e = simplify_expr new_e in
	  NSif (new_e,new_s1,new_s2)
      | NSwhile (annot,e,s1) ->
	  assert (List.length sub_nodes = 3);
	  let new_e,new_s1,new_a = list3 sub_nodes in
	  let new_e,new_s1,new_a = get_e new_e,get_s new_s1,get_annot new_a in
	  let new_e = simplify_expr new_e in
	  NSwhile (new_a,new_e,new_s1)
      | NSdowhile (annot,s1,e) ->
	  assert (List.length sub_nodes = 3);
	  let new_s1,new_e,new_a = list3 sub_nodes in
	  let new_s1,new_e,new_a = get_s new_s1,get_e new_e,get_annot new_a in
	  let new_e = simplify_expr new_e in
	  NSdowhile (new_a,new_s1,new_e)
      | NSfor (annot,einit,etest,eincr,s1) ->
	  assert (List.length sub_nodes = 5);
	  let new_einit,new_etest,new_eincr,new_s1,new_a = list5 sub_nodes in
	  let new_einit,new_etest,new_eincr,new_s1,new_a
	    = get_e new_einit,get_e new_etest,
	    get_e new_eincr,get_s new_s1,get_annot new_a in
	  let new_einit = simplify_expr new_einit in
	  let new_etest = simplify_expr new_etest in
	  let new_eincr = simplify_expr new_eincr in
	  NSfor (new_a,new_einit,new_etest,new_eincr,new_s1)
      | NSblock sl ->
	  let new_sl = List.map get_s sub_nodes in
	  NSblock new_sl
      | NSreturn None ->
	  assert (List.length sub_nodes = 0);
	  s.nst_node
      | NSreturn (Some e) -> 
	  assert (List.length sub_nodes = 1);
	  let new_e = list1 sub_nodes in
	  let new_e = get_e new_e in
	  let new_e = simplify_expr new_e in
	  NSreturn (Some new_e)
      | NSbreak | NScontinue -> 
	  assert (List.length sub_nodes = 0);
	  s.nst_node
      | NSlabel (str,s1) ->
	  assert (List.length sub_nodes = 1);
	  let new_s = list1 sub_nodes in
	  let new_s = get_s new_s in
	  NSlabel (str,new_s)
      | NSspec (spec,s1) ->
	  assert (List.length sub_nodes = 2);
	  let new_s,new_spc = list2 sub_nodes in
	  let new_s,new_spc = get_s new_s,get_spec new_spc in
	  NSspec (new_spc,new_s)
      | NSdecl (typ,var,None,s1) ->
	  assert (List.length sub_nodes = 1);
	  let new_s = list1 sub_nodes in
	  let new_s = get_s new_s in
	  NSdecl (typ,var,None,new_s)
      | NSdecl (typ,var,Some cinit,s1) ->
	  assert (List.length sub_nodes = 2);
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
	  let new_cases = 
	    List.map (fun n -> code_children n) new_cases in
	  let new_cases = List.map (List.map get_s) new_cases in
	  let new_cases = 
	    List.map2 (fun (cmap,_) sl -> (cmap,sl)) cases new_cases in
	  NSswitch (new_e,c,new_cases)
    in
    let new_s = { s with nst_node = new_s } in
    Node.create (Nstat new_s)

  let change_sub_components_in_expr node sub_nodes =
    let e = get_e node in
    let new_e = match e.nexpr_node with
      | NEnop | NEconstant _ | NEstring_literal _ | NEvar _ ->
	  assert (List.length sub_nodes = 0);
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
	  assert (List.length sub_nodes = 2);
	  let new_e1,new_e2 = list2 sub_nodes in
	  let new_e1,new_e2 = get_e new_e1,get_e new_e2 in
	  NEseq (new_e1,new_e2)
      | NEassign (e1,e2) ->
	  assert (List.length sub_nodes = 2);
	  let new_e1,new_e2 = list2 sub_nodes in
	  let new_e1,new_e2 = get_e new_e1,get_e new_e2 in
	  NEassign (new_e1,new_e2)
      | NEassign_op (e1,op,e2) ->
	  assert (List.length sub_nodes = 2);
	  let new_e1,new_e2 = list2 sub_nodes in
	  let new_e1,new_e2 = get_e new_e1,get_e new_e2 in
	  NEassign_op (new_e1,op,new_e2)
      | NEbinary (e1,op,e2) ->
	  assert (List.length sub_nodes = 2);
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
				  let e4 = make_int_termexpr_add_termexpr e2 e3
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
		begin match destr_ptr_off new_e1,destr_ptr_off new_e2 with
		  | Some (v1,e3),Some (v2,e4) ->
		      if Var.equal v1 v2 then 
			let op = pointer_op_to_int_op op in
			NEbinary (e3,op,e4)
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
	  assert (List.length sub_nodes = 3);
	  let new_e1,new_e2,new_e3 = list3 sub_nodes in
	  let new_e1,new_e2,new_e3 
	    = get_e new_e1,get_e new_e2,get_e new_e3 in
	  NEcond (new_e1,new_e2,new_e3)
    in		
    let new_e = { e with nexpr_node = new_e } in
    Node.create (Nexpr new_e)

  (* recognize offset from pointer *)
  let rec term_destr_ptr_off t = match t.nterm_node with
    | NTbinop(t1,Clogic.Badd,t2) ->
	begin match t1.nterm_node with
	  | NTvar v -> Some (v,t2)
	  | _ -> 
	      (* recursive call *)
	      begin match term_destr_ptr_off t1 with
		| Some (v,t3) ->
		    let t2 = Node.create (Nterm t2) in
		    let t3 = Node.create (Nterm t3) in
		    let t4 = make_int_termexpr_add_termexpr t2 t3
		    in
		    Some (v,get_t t4)
		| None -> None
	      end
	end
    | _ -> None

  let change_sub_components_in_term node sub_nodes =
    let t = get_t node in
    let new_t = match t.nterm_node with
      | NTconstant _ | NTvar _ -> 
	  assert (List.length sub_nodes = 0);
	  t.nterm_node
      | NTapp a ->
	  let new_args = sub_nodes in
	  let new_args = List.map get_t new_args in
	  NTapp { a with napp_args = new_args }
      | NTunop (op,t1) ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NTunop (op,new_t)
      | NTarrow (t1,zone,var) ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NTarrow (new_t,zone,var)
      | NTold t1 ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NTold new_t
      | NTat (t1,label) ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NTat (new_t,label)
      | NTbase_addr t1 ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NTbase_addr new_t
      | NToffset t1 ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NToffset new_t
      | NTblock_length t1 ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NTblock_length new_t
      | NTcast (typ,t1) ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NTcast (typ,new_t)
      | NTbinop (t1,op,t2) ->
	  assert (List.length sub_nodes = 2);
	  let new_t1,new_t2 = list2 sub_nodes in
	  let new_t1,new_t2 = get_t new_t1,get_t new_t2 in
	  begin match op with
	    | Clogic.Bsub ->
		(* could be a binary operation on pointers. 
		   If both arguments are indices/offsets from the same pointer,
		   translate the pointer operation into an equivalent integer 
		   operation. *)
		begin match term_destr_ptr_off new_t1,
		  term_destr_ptr_off new_t2 with
		    | Some (v1,t3),Some (v2,t4) ->
			if Var.equal v1 v2 then NTbinop (t3,op,t4)
			else NTbinop (new_t1,op,new_t2)
		    | _ -> NTbinop (new_t1,op,new_t2)
		end
	    | _ -> NTbinop (new_t1,op,new_t2)
	  end
      | NTif (t1,t2,t3) ->
	  assert (List.length sub_nodes = 3);
	  let new_t1,new_t2,new_t3 = list3 sub_nodes in
	  let new_t1,new_t2,new_t3 
	    = get_t new_t1,get_t new_t2,get_t new_t3 in
	  NTif (new_t1,new_t2,new_t3)
      | NTrange (t1,t2opt,t3opt,zone,info) ->
	  assert (List.length sub_nodes = 3);
	  let new_t1,new_t2,new_t3 = list3 sub_nodes in
	  let new_t1 = get_t new_t1 in
	  let new_t2 = match logic_children new_t2 with
	    | [new_t2] -> Some (get_t new_t2)
	    | [] -> None
	    | _ -> assert false (* bad encoding *)
	  in
	  let new_t3 = match logic_children new_t3 with
	    | [new_t3] -> Some (get_t new_t3)
	    | [] -> None
	    | _ -> assert false (* bad encoding *)
	  in
	  (* [new_t1] could be an offset from some pointer *)
	  begin match term_destr_ptr_off new_t1 with
	    | Some (v,t4) ->
		let new_t2 = match new_t2 with
		  | Some new_t2 -> 
		      let t2 = Node.create (Nterm new_t2) in
		      let t4 = Node.create (Nterm t4) in
		      Some (get_t (make_int_termexpr_add_termexpr t2 t4))
		  | None -> None
		in
		let new_t3 = match new_t3 with
		  | Some new_t3 -> 
		      let t3 = Node.create (Nterm new_t3) in
		      let t4 = Node.create (Nterm t4) in
		      Some (get_t (make_int_termexpr_add_termexpr t3 t4))
		  | None -> None
		in
		let new_t1 = { new_t1 with nterm_node = NTvar v } in
		NTrange (new_t1,new_t2,new_t3,zone,info)
	    | None ->
		NTrange (new_t1,new_t2,new_t3,zone,info)
	  end
    in		
    let new_t = { t with nterm_node = new_t } in
    Node.create (Nterm new_t)

  let change_sub_components_in_pred node sub_nodes =
    let p = get_p node in
    let new_p = match p.npred_node with
      | NPfalse | NPtrue -> 
	  assert (List.length sub_nodes = 0);
	  p.npred_node
      | NPapp a ->
	  let new_args = sub_nodes in
	  let new_args = List.map get_t new_args in
	  NPapp { a with napp_args = new_args }
      | NPrel (t1,rel,t2) ->
	  assert (List.length sub_nodes = 2);
	  let new_t1,new_t2 = list2 sub_nodes in
	  let new_t1,new_t2 = get_t new_t1,get_t new_t2 in
	  (* could be a binary operation on pointers. 
	     If both arguments are indices/offsets from the same pointer,
	     translate the pointer operation into an equivalent integer 
	     operation. *)
	  begin match term_destr_ptr_off new_t1,term_destr_ptr_off new_t2 with
	    | Some (v1,t3),Some (v2,t4) ->
		if Var.equal v1 v2 then NPrel (t3,rel,t4)
		else NPrel (new_t1,rel,new_t2)
	    | _ -> NPrel (new_t1,rel,new_t2)
	  end
      | NPvalid_index (t1,t2) ->
	  assert (List.length sub_nodes = 2);
	  let new_t1,new_t2 = list2 sub_nodes in
	  let new_t1,new_t2 = get_t new_t1,get_t new_t2 in
	  NPvalid_index (new_t1,new_t2)
      | NPand (p1,p2) ->
	  assert (List.length sub_nodes = 2);
	  let new_p1,new_p2 = list2 sub_nodes in
	  let new_p1,new_p2 = get_p new_p1,get_p new_p2 in
	  NPand (new_p1,new_p2)		
      | NPor (p1,p2) ->
	  assert (List.length sub_nodes = 2);
	  let new_p1,new_p2 = list2 sub_nodes in
	  let new_p1,new_p2 = get_p new_p1,get_p new_p2 in
	  NPor (new_p1,new_p2)		
      | NPimplies (p1,p2) ->
	  assert (List.length sub_nodes = 2);
	  let new_p1,new_p2 = list2 sub_nodes in
	  let new_p1,new_p2 = get_p new_p1,get_p new_p2 in
	  NPimplies (new_p1,new_p2)		
      | NPiff (p1,p2) ->
	  assert (List.length sub_nodes = 2);
	  let new_p1,new_p2 = list2 sub_nodes in
	  let new_p1,new_p2 = get_p new_p1,get_p new_p2 in
	  NPiff (new_p1,new_p2)		
      | NPnot p1 ->
	  assert (List.length sub_nodes = 1);
	  let new_p1 = list1 sub_nodes in
	  let new_p1 = get_p new_p1 in
	  NPnot new_p1
      | NPforall (q,p1) ->
	  assert (List.length sub_nodes = 1);
	  let new_p1 = list1 sub_nodes in
	  let new_p1 = get_p new_p1 in
	  NPforall (q,new_p1)
      | NPexists (q,p1) ->
	  assert (List.length sub_nodes = 1);
	  let new_p1 = list1 sub_nodes in
	  let new_p1 = get_p new_p1 in
	  NPexists (q,new_p1)
      | NPold p1 ->
	  assert (List.length sub_nodes = 1);
	  let new_p1 = list1 sub_nodes in
	  let new_p1 = get_p new_p1 in
	  NPold new_p1
      | NPat (p1,label) ->
	  assert (List.length sub_nodes = 1);
	  let new_p1 = list1 sub_nodes in
	  let new_p1 = get_p new_p1 in
	  NPat (new_p1,label)
      | NPnamed (name,p1) ->
	  assert (List.length sub_nodes = 1);
	  let new_p1 = list1 sub_nodes in
	  let new_p1 = get_p new_p1 in
	  NPnamed (name,new_p1)
      | NPif (t1,p2,p3) ->
	  assert (List.length sub_nodes = 3);
	  let new_t1,new_p2,new_p3 = list3 sub_nodes in
	  let new_t1,new_p2,new_p3
	    = get_t new_t1,get_p new_p2,get_p new_p3 in
	  NPif (new_t1,new_p2,new_p3)		
      | NPvalid t1 ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NPvalid new_t
      | NPfresh t1 ->
	  assert (List.length sub_nodes = 1);
	  let new_t = list1 sub_nodes in
	  let new_t = get_t new_t in
	  NPfresh new_t
      | NPvalid_range (t1,t2,t3) ->
	  assert (List.length sub_nodes = 3);
	  let new_t1,new_t2,new_t3 = list3 sub_nodes in
	  let new_t1,new_t2,new_t3 
	    = get_t new_t1,get_t new_t2,get_t new_t3 in
	  NPvalid_range (new_t1,new_t2,new_t3)
    in		
    let new_p = { p with npred_node = new_p } in
    Node.create (Npred new_p)

  let change_sub_components_in_annot node sub_nodes =
    let a = get_annot node in
    assert (List.length sub_nodes = 3);
    let new_inv,new_ass,new_var = list3 sub_nodes in
    let new_inv = match logic_children new_inv with
      | [new_inv] -> Some (get_p new_inv)
      | [] -> None
      | _ -> assert false (* bad encoding *)
    in
    let new_ass = match logic_children new_ass with
      | [new_ass] ->
	  let new_ass = List.map get_t (logic_children new_ass) in
	  Some new_ass
      | [] -> None
      | _ -> assert false (* bad encoding *)
    in
    let name_var = match a.variant with
      | None -> None
      | Some (_,so) -> so in
    let new_var = match logic_children new_var with
      | [new_var] -> Some (get_t new_var,name_var)
      | [] -> None
      | _ -> assert false (* bad encoding *)
    in
    let new_a = { a with invariant = new_inv; 
		    loop_assigns = new_ass; variant = new_var } in
    Node.create (Nannot new_a)

  let change_sub_components_in_spec node sub_nodes =
    let s = get_spec node in
    assert (List.length sub_nodes = 4);
    let new_req,new_ass,new_ens,new_dec = list4 sub_nodes in
    let new_req = match logic_children new_req with
      | [new_req] -> Some (get_p new_req)
      | [] -> None
      | _ -> assert false (* bad encoding *)
    in
    let new_ass = match logic_children new_ass with
      | [new_ass] ->
	  let new_ass = List.map get_t (logic_children new_ass) in
	  Some new_ass
      | [] -> None
      | _ -> assert false (* bad encoding *)
    in
    let new_ens = match logic_children new_ens with
      | [new_ens] -> Some (get_p new_ens)
      | [] -> None
      | _ -> assert false (* bad encoding *)
    in
    let name_dec = match s.decreases with
      | None -> None
      | Some (_,so) -> so in
    let new_dec = match logic_children new_dec with
      | [new_dec] -> Some (get_t new_dec,name_dec)
      | [] -> None
      | _ -> assert false (* bad encoding *)
    in
    let new_s = { s with requires = new_req; assigns = new_ass;
		    ensures = new_ens; decreases = new_dec } in
    Node.create (Nspec new_s)

  let change_sub_components node sub_nodes =
    match get_node_kind node with
      | NKnone ->
	  (* forward node for upper level. Rebuild the correct one-level 
	     sub-graph so that the upper level can rely on it if necessary.
	     Chained forward nodes can recreate more than one level. *)
	  let is_structural = fwd_is_structural node in
	  let fwd_node = Node.create (Nfwd is_structural) in 
	  add_vertex fwd_node;
	  if is_structural then
	    add_stedge fwd_node sub_nodes
	  else
	    add_logedge fwd_node sub_nodes;
	  fwd_node
	  
      | NKdecl ->
	  let d = get_decl node in
	  let new_d =
	    match d.s with
	      | Some s ->
		  let new_s,new_spec = list2 sub_nodes in
		  let new_s,new_spec = get_s new_s,get_spec new_spec in
		  { d with s = Some new_s; spec = new_spec }
	      | _ -> d
	  in
	  Node.create (Ndecl new_d)

      | NKstat ->
	  change_sub_components_in_stat node sub_nodes
	    
      | NKexpr ->
	  change_sub_components_in_expr node sub_nodes
	    
      | NKterm ->
	  change_sub_components_in_term node sub_nodes
	    
      | NKpred ->
	  change_sub_components_in_pred node sub_nodes
	    
      | NKannot ->
	  change_sub_components_in_annot node sub_nodes
	    
      | NKspec ->
	  change_sub_components_in_spec node sub_nodes

  let introduce_new_vars node var_list zero_init =
    let d = get_decl node in
    let new_d = match d.s with
      | Some s ->
	  let new_s = 
	    List.fold_left 
	      (fun next_s var -> 
		 let init = 
		   if zero_init then
		     let zero_cst = 
		       NEconstant (IntConstant (string_of_int 0)) in
		     let zero_expr = { nexpr_node = zero_cst; 
				       nexpr_type = int_offset_type;
				       nexpr_loc = Loc.dummy_position }
		     in
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

  let rec from_term (t : nterm) = 
    let tnode = Node.create (Nterm t) in
    add_vertex tnode;
    begin
      match t.nterm_node with
	| NTconstant _ | NTvar _ -> ()
	| NTapp a ->
	    let args_nodes = List.map from_term a.napp_args in
	    (* logic *) add_logedge tnode args_nodes
	| NTunop (_,t1) | NTarrow (t1,_,_) | NTold t1 | NTat (t1,_)
	| NTbase_addr t1 | NToffset t1 | NTblock_length t1 | NTcast (_,t1) ->
	    let t1node = from_term t1 in
	    (* logic *) add_logedge tnode [t1node]
	| NTbinop (t1,_,t2) ->
	    let t1node = from_term t1 in
	    let t2node = from_term t2 in
	    (* logic *) add_logedge tnode [t1node; t2node]
	| NTif (t1,t2,t3) ->
	    let t1node = from_term t1 in
	    let t2node = from_term t2 in
	    let t3node = from_term t3 in
	    (* logic *) add_logedge tnode [t1node; t2node; t3node]
	| NTrange (t1,t2opt,t3opt,_,_) ->
	    let t1node = from_term t1 in
	    let t2node = Node.create (Nfwd (* is_structural= *)false) in 
	    add_vertex t2node;
	    begin match t2opt with 
	      | Some t2 ->
		  let t2optnode = from_term t2 in
		  (* logic *) add_logedge t2node [t2optnode]
	      | None -> ()
	    end;
	    let t3node = Node.create (Nfwd (* is_structural= *)false) in
	    add_vertex t3node;
	    begin match t3opt with 
	      | Some t3 ->
		  let t3optnode = from_term t3 in
		  (* logic *) add_logedge t3node [t3optnode]
	      | None -> ()
	    end;
	    (* logic *) add_logedge tnode [t1node; t2node; t3node]
    end;
    tnode

  let rec from_pred (p : npredicate) =
    let pnode = Node.create (Npred p) in
    add_vertex pnode;
    begin
      match p.npred_node with
	| NPfalse | NPtrue -> ()
	| NPapp a ->
	    let args_nodes = List.map from_term a.napp_args in
	    (* logic *) add_logedge pnode args_nodes
	| NPrel (t1,_,t2) | NPvalid_index (t1,t2) ->
	    let t1node = from_term t1 in
	    let t2node = from_term t2 in
	    (* logic *) add_logedge pnode [t1node; t2node]
	| NPand (p1,p2) | NPor (p1,p2) | NPimplies (p1,p2) | NPiff (p1,p2) ->
	    let p1node = from_pred p1 in
	    let p2node = from_pred p2 in
	    (* logic *) add_logedge pnode [p1node; p2node]
	| NPnot p1 | NPforall (_,p1) | NPexists (_,p1) | NPold p1 
	| NPat (p1,_) | NPnamed (_,p1) ->
	    let p1node = from_pred p1 in
	    (* logic *) add_logedge pnode [p1node]
	| NPif (t1,p2,p3) ->
	    let t1node = from_term t1 in
	    let p2node = from_pred p2 in
	    let p3node = from_pred p3 in
	    (* logic *) add_logedge pnode [t1node; p2node; p3node]
	| NPvalid t1 | NPfresh t1 ->
	    let t1node = from_term t1 in
	    (* logic *) add_logedge pnode [t1node]
	| NPvalid_range (t1,t2,t3) ->
  	    let t1node = from_term t1 in
	    let t2node = from_term t2 in
	    let t3node = from_term t3 in
	    (* logic *) add_logedge pnode [t1node; t2node; t3node]
    end;
    pnode

  let from_spec (s : nspec) = 
    let requires_node = Node.create (Nfwd (* is_structural= *)false) in
    add_vertex requires_node;
    begin match s.requires with
      | Some p ->
	  let reqnode = from_pred p in
	  (* logic *) add_logedge requires_node [reqnode]
      | None -> ()
    end;
    let assigns_node = Node.create (Nfwd (* is_structural= *)false) in
    add_vertex assigns_node;
    begin match s.assigns with
      | Some tl ->
	  (* differenciate [None] from [Some([])] *)
	  let assnode = Node.create (Nfwd (* is_structural= *)false) in
	  add_vertex assnode;
	  (* logic *) add_logedge assigns_node [assnode];
	  let tnodes = List.map from_term tl in
	  add_logedge assnode tnodes
      | None -> ()
    end;
    let ensures_node = Node.create (Nfwd (* is_structural= *)false) in
    add_vertex ensures_node;
    begin match s.ensures with
      | Some p ->
	  let ensnode = from_pred p in
	  (* logic *) add_logedge ensures_node [ensnode]
      | None -> ()
    end;
    let decreases_node = Node.create (Nfwd (* is_structural= *)false) in
    add_vertex decreases_node;
    begin match s.decreases with
      | Some (t,_) ->
	  let decnode = from_term t in
	  (* logic *) add_logedge decreases_node [decnode]
      | None -> ()
    end;
    let snode = Node.create (Nspec s) in add_vertex snode;
    (* logic *) add_logedge snode [requires_node; assigns_node;
				   ensures_node; decreases_node];
    snode

  let from_annot (a : nloop_annot) =
    let invariant_node = Node.create (Nfwd (* is_structural= *)false) in
    add_vertex invariant_node;
    begin match a.invariant with
      | Some p ->
	  let invnode = from_pred p in
	  (* logic *) add_logedge invariant_node [invnode]
      | None -> ()
    end;
    let assigns_node = Node.create (Nfwd (* is_structural= *)false) in
    add_vertex assigns_node;
    begin match a.loop_assigns with
      | Some tl ->
	  (* differenciate [None] from [Some([])] *)
	  let assnode = Node.create (Nfwd (* is_structural= *)false) in
	  add_vertex assnode;
	  (* logic *) add_logedge assigns_node [assnode];
	  let tnodes = List.map from_term tl in
	  add_logedge assnode tnodes
      | None -> ()
    end;
    let variant_node = Node.create (Nfwd (* is_structural= *)false) in
    add_vertex variant_node;
    begin match a.variant with
      | Some (t,_) ->
	  let varnode = from_term t in
	  (* logic *) add_logedge variant_node [varnode]
      | None -> ()
    end;
    let anode = Node.create (Nannot a) in add_vertex anode;
    (* logic *) add_logedge anode [invariant_node; assigns_node; variant_node];
    anode

  let rec from_expr start_node (e : nexpr) = 
    let enode = Node.create (Nexpr e) in add_vertex enode;
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

  type context_descr = 
      { 
	(* target for [continue] statements in loops *)
	loop_starts : Node.t list; 
	(* target for [break] statements in loops and switches *)
	loop_switch_ends : Node.t list;
	(* context of \old logical terms *)
	function_begin : Node.t;
	(* target of return and last statement of function *)
	function_end : Node.t
      }

  let rec from_stat (ctxt : context_descr) start_node (s : nstatement) =
    let snode = Node.create (Nstat s) in add_vertex snode;
    begin
      match s.nst_node with
	| NSnop | NSlogic_label _ ->
	    (* oper *) add_opedge start_node snode
	| NSassert p ->
	    (* oper *) add_opedge start_node snode;
	    let pnode = from_pred p in
	    (* logic *) add_logedge snode [pnode];
	    (* assert node is its self-begin and its self-end *)
	    (* logic *) add_begedge snode snode; 
	    (* logic *) add_endedge snode snode
	| NSexpr e -> 
	    let enode = from_expr start_node e in
	    (* oper *) add_opedge enode snode;
	    (* struct *) add_stedge snode [enode]
	| NSif (e,s1,s2) ->
	    let enode = from_expr start_node e in
	    let s1node = from_stat ctxt enode s1 in
	    let s2node = from_stat ctxt enode s2 in
	    (* oper *) add_opedge s1node snode;
	    (* oper *) add_opedge s2node snode;
	    (* struct *) add_stedge snode [enode; s1node; s2node]
	| NSwhile (a,e,s1) ->
	    (* target of backward edge in loop *)
	    let bwd_node = Node.create (Nfwd (* is_structural= *)true) in
	    add_vertex bwd_node;
	    (* connect backward edge *)
	    (* oper *) add_opedge start_node bwd_node;
	    let enode = from_expr bwd_node e in
	    let upd_ctxt =
	      { loop_starts = bwd_node :: ctxt.loop_starts;
		loop_switch_ends = snode :: ctxt.loop_switch_ends;
		function_begin = ctxt.function_begin;
		function_end = ctxt.function_end } in
	    let s1node = from_stat upd_ctxt enode s1 in
	    (* oper *) add_opedge s1node bwd_node; (* before [e]'s eval *)
	    (* oper *) add_opedge enode snode; (* after [e]'s eval *)
	    (* struct *) add_stedge snode [enode; s1node];
	    let anode = from_annot a in
	    (* logic *) add_logedge snode [anode];
	    (* the logical "annot" node is linked to the start and end nodes *)
	    (* [bwd_node] is the end node of the loop *)
	    (* logic *) add_begedge anode ctxt.function_begin;
	    (* logic *) add_endedge anode bwd_node
	| NSdowhile (a,s1,e) ->
	    (* target of backward edge in loop *)
	    let bwd_node = Node.create (Nfwd (* is_structural= *)true) in
	    add_vertex bwd_node;
	    (* connect backward edge *)
	    (* oper *) add_opedge start_node bwd_node;
	    let fwd_enode = Node.create (Nfwd (* is_structural= *)true) in
	    add_vertex fwd_enode;
	    let upd_ctxt =
	      { loop_starts = fwd_enode :: ctxt.loop_starts;
		loop_switch_ends = snode :: ctxt.loop_switch_ends;
		function_begin = ctxt.function_begin;
		function_end = ctxt.function_end } in
	    let s1node = from_stat upd_ctxt bwd_node s1 in
	    let enode = from_expr fwd_enode e in
	    (* oper *) add_opedge s1node fwd_enode;
	    (* oper *) add_opedge enode bwd_node; (* before [s1]'s eval *)
	    (* oper *) add_opedge enode snode;
	    (* struct *) add_stedge snode [s1node; enode];
	    let anode = from_annot a in
	    (* logic *) add_logedge snode [anode];
	    (* the logical "annot" node is linked to the start and end nodes *)
	    (* [bwd_node] is the end node of the loop *)
	    (* logic *) add_begedge anode ctxt.function_begin;
	    (* logic *) add_endedge anode bwd_node
	| NSfor (a,einit,etest,eincr,s1) ->
	    (* target of backward edge in loop *)
	    let bwd_node = Node.create (Nfwd (* is_structural= *)true) in
	    add_vertex bwd_node;
	    let einit_node = from_expr start_node einit in
	    (* connect backward edge *)
	    (* oper *) add_opedge einit_node bwd_node;
	    let etest_node = from_expr bwd_node etest in
	    let fwd_enode = Node.create (Nfwd (* is_structural= *)true) in
	    add_vertex fwd_enode;
	    let upd_ctxt =
	      { loop_starts = fwd_enode :: ctxt.loop_starts;
		loop_switch_ends = snode :: ctxt.loop_switch_ends;
		function_begin = ctxt.function_begin;
		function_end = ctxt.function_end } in
	    let s1node = from_stat upd_ctxt etest_node s1 in
	    let eincr_node = from_expr fwd_enode eincr in
	    (* oper *) add_opedge s1node fwd_enode;
	    (* oper *) add_opedge eincr_node bwd_node; (* before [etest] *)
	    (* oper *) add_opedge etest_node snode; (* after [etest]'s eval *)
	    (* struct *) add_stedge snode [einit_node; etest_node;
					   eincr_node; s1node];
	    let anode = from_annot a in
	    (* logic *) add_logedge snode [anode];
	    (* the logical "annot" node is linked to the start and end nodes *)
	    (* [bwd_node] is the end node of the loop *)
	    (* logic *) add_begedge anode ctxt.function_begin;
	    (* logic *) add_endedge anode bwd_node
	| NSblock sl ->
	    let (bnode,snodes) = 
	      List.fold_left 
		(fun (stnode,s1nodes) s1 -> 
		   let s1node = from_stat ctxt stnode s1 in
		   s1node,s1node::s1nodes
		) (start_node,[]) sl in
	    let snodes = List.rev snodes in
	    (* oper *) add_opedge bnode snode;
	    (* struct *) add_stedge snode snodes
	| NSreturn None ->
	    (* oper *) add_opedge start_node snode;
	    (* logic *) force_add_opedge snode ctxt.function_end
	| NSreturn (Some e) -> 
	    let enode = from_expr start_node e in
	    (* oper *) add_opedge enode snode;
	    (* struct *) add_stedge snode [enode];
	    (* logic *) force_add_opedge snode ctxt.function_end
	| NSbreak -> 
	    (* oper *) add_opedge start_node snode;
	    (* oper *) force_add_opedge snode (List.hd ctxt.loop_switch_ends);
	| NScontinue -> 
	    (* oper *) add_opedge start_node snode;
	    (* oper *) force_add_opedge snode (List.hd ctxt.loop_starts)
	| NSspec (spc,s1) ->
	    let s1node = from_stat ctxt start_node s1 in
	    (* oper *) add_opedge s1node snode;
	    (* struct *) add_stedge snode [s1node];
	    let spcnode = from_spec spc in
	    (* logic *) add_logedge snode [spcnode];
	    (* the logical "spec" node is linked to the start and end nodes *)
	    (* logic *) add_begedge spcnode start_node;
	    (* logic *) add_endedge spcnode snode
	| NSlabel (_,s1) | NSdecl (_,_,None,s1) ->
	    let s1node = from_stat ctxt start_node s1 in
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
	    let s1node = from_stat ctxt enode s1 in
	    (* oper *) add_opedge s1node snode;
	    (* struct *) add_stedge snode [enode;s1node]
	| NSswitch (e,_,cases) -> 
	    let enode = from_expr start_node e in
	    let upd_ctxt =
	      { loop_starts = ctxt.loop_starts;
		loop_switch_ends = snode :: ctxt.loop_switch_ends;
		function_begin = ctxt.function_begin;
		function_end = ctxt.function_end } in
	    let cnodes = List.map
	      (fun (_,sl) -> 
		 let cnode,clnodes =
		   List.fold_left 
		     (fun (stnode,s1nodes) s1 -> 
			let s1node = from_stat upd_ctxt stnode s1 in
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
			  let fnode = 
			    Node.create (Nfwd (* is_structural= *)true) in
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
    let dnode = Node.create (Ndecl d) in add_vertex dnode;
    begin match d.s with
      | Some s ->
	  (* In order to be able to transform any [ensures] part of 
	     a function, we must create an end node for the function body,
	     so that all pointers are known under the same name at that point.
	     All return statements and the last statement should be linked
	     to this end node.
	     This transformation may lead to a less precise analysis. 
	     It could be restricted to functions that need it to translate
	     their [ensures] part.
	  *)
	  let end_node = Node.create (Nfwd (* is_structural= *)true) in
	  add_vertex end_node;
	  let start_ctxt = 
	    { 
	      loop_starts = []; 
	      loop_switch_ends = [];
	      function_begin = dnode;
	      function_end = end_node
	    } in
	  let snode = from_stat start_ctxt dnode s in
	  (* oper *) add_opedge snode end_node;
	  (* struct *) add_stedge dnode [snode];
	  let spcnode = from_spec d.spec in
	  (* logic *) add_logedge dnode [spcnode];
	  (* the logical "spec" node is linked to the start and end nodes *)
	  (* logic *) add_begedge spcnode dnode; (* begin of decl is itself *)
	  (* logic *) add_endedge spcnode end_node
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
	    
      | _ ->
	  failwith "[transfer] should not be called on logical nodes"

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
		       Info.default_var_info (var.var_unique_name ^ "_offset")
		     in
		     Info.set_assigned offset_var;
		     Cenv.set_var_type 
		       (Var_info offset_var) int_offset_type false;
		     VarMap.add var offset_var m
		  ) offset_vars VarMap.empty 
    in
    let offset_map =
      VarSet.fold (fun var m ->
		     let offset_var = 
		       Info.default_var_info 
			 (var.var_unique_name ^ "_self_offset") in
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

  (* used in [transform_t] for the correspondance between labels and their 
     representative node *)
  module StringMap = Map.Make (String)

  (* type used to propagate information in [sub_transform] and
     its sub-functions *)
  type transform_t =
      {
	offset_vars : VarSet.t ref;
	offset_map : Var.t VarMap.t;
	label_corresp : Node.t StringMap.t;
	block_begin : Node.t;
	block_end : Node.t;
	has_old : bool;
	has_at : String.t option
      }

  (* type used to pass information from [sub_transform] to its sub-functions *)
  type local_nodes_t =
      {
	node : Node.t;
	sub_nodes : Node.t list;
	new_sub_nodes : (Node.t * Node.t option) list
      }

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

  (* 4 sub-functions that share code between cases below *)

  (* every offset variable that is used in the code must be stored in 
     the repository [offset_vars], to be declared later on by a call to
     [introduce_new_vars]. *)
  let store_offset_var params offset_var =
    params.offset_vars := VarSet.add offset_var (!(params.offset_vars))

  (* returns a pointer read that corresponds to the abstract value
     [aval], with other elements taken in [node] 
  *)
  let make_pointer_read params node pval =
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
      store_offset_var params offset_var;
      change_in_ptr_var_add_var node new_var offset_var
    else if PtrLattice.is_defined pval then
      (* rewrite possible assignment to v as v *)
      let new_var,_ = PtrLattice.get_defined_opt pval in
      change_in_var node new_var
    else node

  (* returns an offset assignment from the abstract value [rhs_val]
     to the variable [offset_lhs_var], with the possible addition
     of an expression [add_offset_opt]. Other elements are taken
     in [node]. 
  *)
  let make_offset_assign params 
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
      store_offset_var params offset_rhs_var;
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

  (* returns a pointer assignment from [new_rhs_node] to [lhs_node],
     with [new_rhs_type_is_ptr] telling if the new right-hand side
     is still of pointer type or not. Other elements are taken
     in [node]. 
  *)
  let keep_pointer_assignment params 
      node aval new_rhs_type_is_ptr lhs_node new_rhs_node is_incr_decr =
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
	let ptr_node = make_pointer_read params node rhs_val in
	let assign_node = 
	  change_sub_components node [lhs_node;ptr_node]
	in
	make_seq_expr new_rhs_node assign_node
      end

  (* part of the transformation that deals with expressions.
     Can raise exception Rec_transform for a common treatment with
     [sub_transform]. *)
  let sub_transform_on_expr analysis params local_nodes =
    let node = local_nodes.node in
    let sub_nodes = local_nodes.sub_nodes in
    let new_sub_nodes = local_nodes.new_sub_nodes in

    (* transformation is possible only if analysis provides some information. 
       Otherwise raise Not_found. *)
    let _,aval = 
      try Hashtbl.find analysis node 
      with Not_found -> raise Rec_transform
    in

    (* beginning of transformation for expressions *)
    
    (* reading some pointer variable.
       This is called also on pointer write, but the result
       of this rewrite is ignored by the calling [sub_transform]
       on pointer assignment. *)
    if termexpr_is_local_ptr_var node then
      let var = termexpr_var_get_var node in
      let pval = PointWisePtrLattice.find var aval in 
      (make_pointer_read params node pval,
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
	    (keep_pointer_assignment params node aval
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
		make_pointer_read params node lhs_val 
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
	      store_offset_var params offset_lhs_var;
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
		      make_offset_assign params 
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
		  wrap_addon (make_offset_assign params 
				node offset_lhs_var rhs_val None true)
		else
		  let var_opt,off_opt = 
		    get_ptr_add_on_var_opt new_rhs_node in
		  let off_opt = match off_opt with
		    | None -> None
		    | Some off_node ->
			if expr_is_local_var off_node then
			  (* rule out transformation of offset *)
			  let off_var = termexpr_var_get_var off_node in
			  if VarSet.mem off_var (!(params.offset_vars)) then
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
		    (make_offset_assign params 
		       node offset_lhs_var rhs_val off_opt false)

	    else if PtrLattice.is_defined lhs_val then
	      let assign_node = 
		keep_pointer_assignment params node aval new_rhs_type_is_ptr 
		  lhs_node new_rhs_node is_incr_decr
	      in
	      match PtrLattice.get_defined_opt lhs_val with
		| _,Some offset_var ->
		    store_offset_var params offset_var;
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
	      (keep_pointer_assignment params node aval new_rhs_type_is_ptr 
		 lhs_node new_rhs_node is_incr_decr,
	       None) (* nothing to add to make it a pointer *)

    else raise Rec_transform

  let sub_transform_on_term analysis params local_nodes =
    let node = local_nodes.node in
    let sub_nodes = local_nodes.sub_nodes in
    let new_sub_nodes = local_nodes.new_sub_nodes in

    if termexpr_is_local_ptr_var node then
      let var = termexpr_var_get_var node in
      let pval = 
	if params.has_old then
	  begin
	    assert (params.has_at = None);
	    let begin_val = 
	      try 
		let _,begin_val = Hashtbl.find analysis params.block_begin in
		begin_val
	      with Not_found -> PointWisePtrLattice.bottom
	    in
	    PointWisePtrLattice.find var begin_val
	  end
	else match params.has_at with
	  | Some lab ->
	      begin
		assert (not params.has_old);
		let at_node = StringMap.find lab params.label_corresp in
		let at_val = 
		  try 
		    let _,at_val = Hashtbl.find analysis at_node in
		    at_val
		  with Not_found -> PointWisePtrLattice.bottom
		in
		PointWisePtrLattice.find var at_val
	      end
	  | None ->
	      let end_val = 
		try 
		  let _,end_val = Hashtbl.find analysis params.block_end in
		  end_val
		with Not_found -> PointWisePtrLattice.bottom
	      in
	      PointWisePtrLattice.find var end_val
      in
      (make_pointer_read params node pval,
       None) (* addon part useless here *)
    else raise Rec_transform

  let rec sub_transform analysis params node =

    let params = match get_node_kind node with
      | NKstat ->
	  if stat_is_assert node then
	    let beg_node = logic_begin node in
	    let end_node = logic_end node in
	    { params with block_begin = beg_node; block_end = end_node }
	  else if stat_is_label node then (* both kinds of labels ? *)
	    let lab = stat_get_label node in
	    { params with label_corresp = 
		StringMap.add lab node params.label_corresp }
	  else params 
      | NKpred | NKterm ->
	  if termpred_is_old node then
	    { params with has_old = true }
	  else if termpred_is_at node then
	    let lab = termpred_get_label node in
	    { params with has_at = Some lab }
	  else params
      | _ -> params
    in

    (* apply [sub_transform] recursively on sub-nodes *)
    let sub_nodes = (code_children node) @ (logic_children node) in
    let new_sub_nodes = match get_node_kind node with
      | NKannot ->
	  let beg_function = logic_begin node and beg_loop = logic_end node in
	  let inv_params = 
	    { params with block_begin = beg_function; block_end = beg_loop } in
	  let ass_params = inv_params in
	  let var_params = inv_params in
	  let params = [inv_params; ass_params; var_params] in
	  List.map2 (sub_transform analysis) params sub_nodes
      | NKspec ->
	  let beg_block = logic_begin node and end_block = logic_end node in
	  let req_params = 
	    { params with block_begin = beg_block; block_end = beg_block } in
	  let ass_params = req_params in
	  let ens_params = 
	    { params with block_begin = beg_block; block_end = end_block } in
	  let dec_params = req_params in
	  let params = [req_params; ass_params; ens_params; dec_params] in
	  List.map2 (sub_transform analysis) params sub_nodes	  
      | _ ->
	  List.map (sub_transform analysis params) sub_nodes
    in
    let local_nodes =
      {
	node = node;
	sub_nodes = sub_nodes;
	new_sub_nodes = new_sub_nodes
      } 
    in

    (* treat declaration/statement/expression separately *)
    try match get_node_kind node with
      | NKnone | NKstat | NKpred | NKannot | NKspec -> raise Rec_transform

      | NKdecl -> 
	  (* no type change needed here, keep only main part *)
	  let new_sub_nodes = List.map fst new_sub_nodes in
	  let new_node = change_sub_components node new_sub_nodes in
	  let param_list = decl_get_params node in
	  let param_offset_vars =
	    List.fold_left 
	      (fun set param ->
		 try 
		   let offset_var = VarMap.find param params.offset_map in
		   if VarSet.mem offset_var (!(params.offset_vars)) then
		     VarSet.add offset_var set
		   else set
		 with Not_found -> set
	      ) VarSet.empty param_list
	  in
	  let other_offset_vars = 
	    VarSet.diff (!(params.offset_vars)) param_offset_vars in
	  let new_node = introduce_new_vars new_node 
	    (VarSet.elements other_offset_vars) (* zero_init= *)false
	  in
	  let new_node = introduce_new_vars new_node 
	    (VarSet.elements param_offset_vars) (* zero_init= *)true
	  in
	  (new_node,None) (* addon part has no meaning here *)

      | NKexpr ->
	  sub_transform_on_expr analysis params local_nodes

      | NKterm ->
	  sub_transform_on_term analysis params local_nodes
	  

    with Rec_transform -> 
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
    List.map (fun decl ->
		let params = 
		  { 
		    offset_vars = ref VarSet.empty;
		    offset_map = offset_map;
		    label_corresp = StringMap.empty;
		    block_begin = decl; (* dummy value *)
		    block_end = decl; (* dummy value *)
		    has_old = false;
		    has_at = None
		  } 
		in
		let new_decl,_ = 
		  sub_transform analysis params decl in
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
