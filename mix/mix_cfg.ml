
type 'p node_kind =
  | Nassert of 'p
  | Ninvariant of 'p

type 'p node = { 
  node_id : int;
  node_name : string;
  node_kind : 'p node_kind
}

type ('p, 's) graph = 'p node -> ('p node * 's) list

type ('p, 's) seq_stmt =
  | Spre of 'p
  | Sstmt of 's
  | Sassert of 'p

module H = struct
  let create = Hashtbl.create 
  let add h n = Hashtbl.add h n.node_id
  let mem h n = Hashtbl.mem h n.node_id
end
module S = struct
  include Set.Make(struct type t = int let compare = compare end)
  let add n = add n.node_id
  let mem n = mem n.node_id
end

let transform g init =
  let invariants = H.create 17 in
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

(** test **)

let init = { node_id = 0; node_name = "init"; node_kind = Ninvariant "PRE" }
let changem = { node_id = 1; node_name = "changem"; node_kind = Nassert "" }
let dec = { node_id = 2; node_name = "dec"; node_kind = Nassert "" }
let inv = { node_id = 3; node_name = "inv"; node_kind = Ninvariant "INV" }
let loop = { node_id = 4; node_name = "loop"; node_kind = Nassert "" }
let post = { node_id = 5; node_name = "post"; node_kind = Nassert "POST" }
let g n = match n.node_id with
  | 0 -> [changem, "s1"]
  | 1 -> [dec, "s2"]
  | 2 -> [inv, "s3"]
  | 3 -> [post, "assume r3<=0"; loop, "assume r3>0; s4"]
  | 4 -> [dec, "assume A>=X[r3]"; changem, "assume A<X[r3]"]
  | 5 -> []
  | _ -> assert false

let t = transform g init
