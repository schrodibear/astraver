type t = int

let fresh = let c = ref 0 in fun () -> incr c; !c

let find v a b =
  List.assoc v (List.map2 (fun a b -> a, b) a b)

let uid x = x
