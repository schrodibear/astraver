
#load "mix_cfg.ml";;

module X = struct
  type label = string
    
  let new_label = let r = ref 0 in fun () -> incr r; "L" ^ string_of_int !r

  type predicate = string
    
  let ptrue = "true"

  type statement = string
    
  let append s1 s2 = s1 ^ "; " ^ s2

end

include Make(X)

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
