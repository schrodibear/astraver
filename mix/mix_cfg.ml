
module type INPUT = sig
  
  module Label : sig
    type t
    val create : unit -> t
    val equal : t -> t -> bool
    val hash : t -> int
  end

  type predicate
    
  val ptrue : predicate

  type statement
    
  val void_stmt : statement

  val append_stmt : statement -> statement -> statement

  val assert_stmt : predicate -> statement
    
end

module Make(X : INPUT) = struct

  type asm =
    | Ainvariant of X.predicate
    | Ajump of X.Label.t
    | Acond of X.Label.t * X.statement * X.statement
    | Ahalt
    | Aother of X.statement

  type asm_code = (X.Label.t option * asm) list
  
  type seq =
    | Sassert of X.predicate
    | Sstmt of X.statement

  type seq_code = {
    seq_pre : X.predicate option;
    seq_code : seq list;
  }

  (* phase 1: from assembly code to CFG *)

  type node_kind =
    | Ninvariant of X.predicate
    | Nother

  type node = { 
    node_id : int;
    node_name : X.Label.t;
    node_kind : node_kind
  }

  type graph = node -> (node * X.statement) list

  module HL = Hashtbl.Make(X.Label)
      
  module HN = struct
    let create = Hashtbl.create 
    let add h n = Hashtbl.add h n.node_id
    let mem h n = Hashtbl.mem h n.node_id
  end

  let make_cfg asm init =
    (* first pass: find out labels which are node starting points *)
    let node_labels = HL.create 97 in
    HL.add node_labels init ();
    List.iter (fun (_, a)-> match a with
		 | Ainvariant _ | Ahalt | Aother _ -> ()
		 | Ajump l | Acond (l,_,_) -> HL.add node_labels l ()) asm;
    (* second pass: create nodes *)
    let nodes = HL.create 97 in
    let create_node =
      let id = ref 0 in
      fun lab kind -> 
	incr id; 
	let node = { node_id = !id; node_name = lab; node_kind = kind } in
	HL.add nodes lab node;
	node
    in
    let lcfg = HL.create 97 in (* label -> (label * stmt) list *)
    let rec descend st = function
      | (l, Aother st1) :: asm when 
	(match l with None -> true | Some l -> not (HL.mem node_labels l)) ->
 	  descend (X.append_stmt st st1) asm
      | _ ->
	  st, asm
    in
    let rec make_nodes = function
      | [] -> 
	  (* end of code -> dummy node *)
	  let l = X.Label.create () in
	  let _ = create_node l Nother in
	  HL.add lcfg l [];
	  l
      | (l, Ainvariant i) :: asm ->
	  (* invariant -> create a node *)
	  let l = match l with None -> X.Label.create () | Some l -> l in
	  let _ = create_node l (Ninvariant i) in
	  let m = make_nodes asm in
	  HL.add lcfg l [m, X.void_stmt];
	  l
      | (l, a) :: asm  ->
	  let l = match l with None -> X.Label.create () | Some l -> l in
	  let _ = create_node l Nother in
	  begin match a with
	    | Ainvariant _ -> 
		assert false
	    | Ahalt -> 
		HL.add lcfg l []; 
		ignore (make_nodes asm)
	    | Ajump l1 -> 
		HL.add lcfg l [l1, X.void_stmt]; 
		ignore (make_nodes asm)
	    | Acond (lt, st, sf) ->
		let lf = make_nodes asm in
		HL.add lcfg l [lt, st; lf, sf]
	    | Aother s ->
		let s,asm = descend s asm in
		let l1 = make_nodes asm in
		HL.add lcfg l [l1, s]
	  end;
	  l
    in
    ignore (make_nodes asm);
    (* finally create the CFG *)
    let cfg = HN.create 97 in
    let node l = try HL.find nodes l with Not_found -> assert false in
    HL.iter (fun l succ -> 
	       HN.add cfg (node l) 
		 (List.map (fun (l1,s1) -> (node l1, s1)) succ)) lcfg;
    Hashtbl.find cfg, node init

  (* phase 2: from CFG to purely sequential programs *)

  module S = struct
    include Set.Make(struct type t = int let compare = compare end)
    let add n = add n.node_id
    let mem n = mem n.node_id
  end

(***
  let transform g init =
    let invariants = HN.create 17 in
    let seq = ref [] in
    let rec dfs visited path n = match n.node_kind with
      | Ninvariant inv ->
	  seq := (Sassert inv :: path) :: !seq;
	  if not (H.mem invariants n) then dfs0 n
      | Nassert _ when S.mem n visited ->  
	  failwith "loop without any invariant"
      | Nassert p ->
	  dfs_children visited (Sassert p :: path) n
    and dfs_children visited path n =
      let children = g n in
      if children = [] then 
	seq := path :: !seq
      else
	let visited = S.add n visited in
	List.iter (fun (m,s) -> dfs visited (Sstmt s :: path) m) (g n)
    and dfs0 n = 
      H.add invariants n ();
      let path = match n.node_kind with
	| Ninvariant inv -> [Spre inv]
	| Nassert p -> [Sassert p]
      in
      dfs_children S.empty path n
    in
    dfs0 init;
    !seq
***)

  let make_seq cfg init =
    assert false

  let transform asm init =
    let cfg,ninit = make_cfg asm init in
    make_seq cfg ninit

end

