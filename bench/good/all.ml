
(* Types syntax *)

external v : foo

(* values *)
external v1 : bool ref
external v2 : int
external v3 : (int)
external v4 : (int) ref
external v5 : foo
external v6 : array 10 of int
external v7 : array 10 of (int)
external v8 : array 3+4 of (int -> int)

(* functions *)
external f1 : int -> bool -> int

external f2 : int -> int ref -> bool

external f3 : x:int ref -> y:int ref -> 
             { p(x,y) } returns r:int reads x,y writes y { q(r,x,y,z) }

external f4 : unit -> {} unit {}

external f5 : foo -> foo
external f6 : x:foo -> foo
external f7 : x:foo -> {} foo {}

external f8 : t:array 10 of int -> {} unit { access(t,1) = 2 }

