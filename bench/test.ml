
(* Types syntax *)

external x: int ref

external f: int -> bool -> int

external g : int -> int ref -> bool

external h : x:int ref -> y:int ref -> 
             { p } returns r:int reads x,y writes z { q }

let test = 
  begin
    x := 1 + 2
  end

