
(* exception without argument *)

exception E

let p1 = (raise E) { false | E => true }

(* exception with an argument *)

exception F of int

let p2 = raise (F 1) { false | F => result = 1 }

let p2a = raise (F (raise E : int)) { false | E => true | F => false }

(* composition of exceptions with other constructs *)

let p3 = begin raise (F 1); raise (F 2) end { false | F => result = 1 }

let p4 = 
  (if true then raise (F 1) else raise (F 2)) { false | F => result = 1 }

let p5 = 
  begin
    if true then raise (F 1);
    raise E
  end
  { false | E => false | F => result = 1 }

let p6 = 
  begin
    if false then raise (F 1);
    raise E
  end
  { false | E => true | F => false }

(* composition of exceptions with side-effect on a reference *)

parameter x : int ref

let p7 = 
  begin x := 1; raise E; x := 2 end { false | E => x = 1 }

let p8 = 
  begin x := 1; raise (F !x); x := 2 end { false | F => x = 1 and result = 1 }

let p9 = (raise (F begin x := 1; !x end)) { false | F => x = 1 and result = 1 }

(* try / with *)

let p10 = (try raise E : int with E -> 0 end) { result = 0 }

let p11 = (try raise (F 1) : int with F x -> x end) { result = 1 }
