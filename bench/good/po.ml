
(* Tests for proof obligations. *)

external x : int ref

let p1 = { q(x+1) } begin x := !x + 1 end { q(x) }

let p2 = { q(7) } begin x := 3 + 4 end { q(x) }

let p3 = begin x := !x + 1; x := !x + 2 end { x = x@ + 3 }

let p4 = begin x := 7; x := 2 * !x end { x = 14 }

let p5 = (3 + 4) { result = 7 }

let p6 = (let a = 3 in a + 4) { result = 7 }

let p7 = (3 + (let a = 4 in a + a)) { result = 11 }

let p8 = { q(x+4) } (3 + begin x := !x + 1; !x end) { q(x) }
