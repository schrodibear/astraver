
(* exception without argument *)

exception E

let p1 = (raise E) { false | E => true }

(* exception with an argument *)

exception F of int

let p = raise (F 1) { false | F => result = 1 }
