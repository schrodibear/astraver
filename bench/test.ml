
(* Types syntax *)

external b: bool ref

external f: int -> bool -> int

external g : int -> int ref -> bool

external h : x:int ref -> y:int ref -> 
             { p } returns r:int reads x,y writes z { q }

(* Test program *)

let test = 
  fun (v:bool) -> v
