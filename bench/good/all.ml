
(* Unitary tests *)

(* Types syntax *)

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

(* variables *)
let acc1 = v2
let acc2 = acc1
let acc3 = f8

(* deref *)
let d1 = !v1
let d2 = !v4

(* arithmetic *)
let ar1 = 1
let ar2 = -1
let ar3 = 1+1
let ar4 = 1-1
let ar5 = 1*1
(*TODO let ar6 = 1/1 *)

(* assignement *)
let a1 = v4 := 1
let a2 = v1 := true
let a3 = v4 := 2+2
let a4 = v4 := !v4

(* sequences *)
let s1 = begin v4 := 1; v4 := 2 end
let s2 = begin v1 := true; v4 := 2 end
let s3 = begin v4 := 1; v4 := !v4; v4 := 3 end
let s4 = begin v4 := 1; 2 end

(* conditionals *)
let c1 = if true then 1 else 2
let c2 = if !v1 then 1 else 2
(* let c3 = if !v4 = 1 then v4 := 2 else v4 := 3 *)

(* arrays *)

(* local variables *)

