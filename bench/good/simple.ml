
(* Simple examples with only assigments and conditionals. *)

external x : int ref
external y : int ref

let p1 = (x := 0) { x = 0 }

let p2 = begin x := 0 end { x = 0 }

let p3 = begin x := 0; x := !x + 1 end { x = 1 }

let p4 = (if !x = 0 then x := 1) { x /= 0 }


