
(* Tests for proof obligations. *)

parameter x : int ref

(* basic stuff: assignment, sequence and local variables *)

let p1 = { q(x+1) } begin x := !x + 1 end { q(x) }

let p2 = { q(7) } begin x := 3 + 4 end { q(x) }

let p3 = begin x := !x + 1; x := !x + 2 end { x = x@ + 3 }

let p4 = begin x := 7; x := 2 * !x end { x = 14 }

let p5 = (3 + 4) { result = 7 }

let p6 = (let a = 3 in a + 4) { result = 7 }

let p7 = (3 + (let a = 4 in a + a)) { result = 11 }

(* side effects in function arguments *)

let p8 = 
  { q(x+1) } (3 + begin x := !x + 1; !x end) { q(x) and result = x@ + 4 }

(* evaluation order (argument first) *)

let p9 = (begin x := 1; 1 end + begin x := 2; 1 end) { result = 2 and x = 1 }

(* function with a post-condition *)

parameter fsucc : x:int -> { } int { result = x + 1 }

let p10 = (fsucc 0) { result = 1 }

let p11 = ((fsucc 0) + (fsucc 3)) { result = 5 }

let p11a = (let a = (fsucc 1) in a + a) { result = 4 }

(* function with a post-condition and side-effects *)

parameter incrx : unit -> { } unit writes x { x = x@ + 1 }

let p12 = { x = 0 } (incrx void) { x = 1 }

let p13 = begin (incrx void); (incrx void) end { x = x@init + 2 }

let p13a = (incrx (incrx void)) { x = x@init + 2 }

(* function with side-effects, result and post-condition *)

parameter incrx2 : unit -> { } int writes x { x = x@ + 1 and result = x }

let p14 = { x = 0 } (incrx2 void) { result = 1 }

(* arrays *)

parameter t : array 10 of int

let p15 = t[0]

let p16 = t[9] := 1

let p17 = { 0 <= t[0] < 10 } t[t[0]] := 1

let p18 = (t[begin x := 0; !x end] := !x) { t[0] = x@ }

