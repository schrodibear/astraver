
(* exception without argument *)

exception E

let p1 = (raise E) { false | E => true }

(* exception with an argument *)

exception F of int

let p2 = raise (F 1) { false | F => result = 1 }

(* composition of exceptions with other constructs *)

(***
let p3 = 
  (if true then raise (F 1) else raise (F 2)) { false | F => result = 1 }
***)

