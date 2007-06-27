
(* checking ocamlgraph version *)

open Graph.Pack.Graph
let g = create ()
let a = Components.scc_array g

