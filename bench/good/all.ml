
(* Unitary tests *)

(* types syntax: values *)
parameter v1 : bool ref
external  v2 : int
external  v3 : (int)
parameter v4 : (int) ref
external  v5 : foo
parameter v6 : array 10 of int
parameter v7 : array 10 of (int)
parameter v8 : array 3+4 of (int -> int)

(* types syntax: functions *)
external f1 : int -> bool -> int

external f2 : int -> int ref -> bool

external f3 : x:int ref -> y:int ref -> 
             { x >= 0 } returns r:int reads x,y writes y { y = y@ + x + r }

external f4 : unit -> {} unit {}

external f5 : foo -> foo
external f6 : x:foo -> foo
external f7 : x:foo -> {} foo {}

external f8 : t:array 10 of int -> {} unit { access(t,1) = 2 }

(* predicates *)
let p1 = 0 { true }
let p2 = 0 { not false }
let p3 = 0 { true and true }
let p4 = 0 { true or false }
let p5 = 0 { false or not false }
let p6 = 0 { true -> not false }
let p7 = 0 { forall x:int. x=x }
let p8 = 0 { true and forall x:int. x=x }
let p9 = 0 { forall x:int. forall y:int. x=y -> x=y }

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
let ar6 = 1/1

(* assignements *)
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
let c3 = if !v4 = 1 then v4 := 2 else v4 := 3

(* local variables *)
let l1 = let x = 1 in x
let l2 = let x = 1 in v4 := x
let l3 = let x = 1 in let y = 2 in x + y
let l4 = v4 := (let x = 1 in 1)
let l5 = let x = 1 in begin v1 := true; v4 := x end

(* local references *)
let lr1 = let x = ref 1 in x := 2
let lr2 = let x = ref 1 in begin x := !x + 1; !x end
let lr3 = let x = ref 1 in let y = ref !x in x := !y

(* relations *)
let r1 = 1 = 1
let r2 = 2 > 1
let r3 = 2 >= 1
let r4 = 1 < 2
let r5 = 1 <= 2
let r6 = 1 <> 2
let r7 = 1 = 2 || 2 = 3
let r8 = 1 = 2 && 2 = 3

(* arrays *)
let arr1 = v6[0]
let arr2 = v6[1+2]
let arr3 = { v4 = 0 } v6[!v4]
let arr4 = { v6[0] = 9 } v6[v6[0]]

(* function calls *)
let fc1 = (f5 v5)
let fc2 = (f4 void)
let fc3 = let a = ref 0 in let b = ref 0 in (f3 a b)

(* while loops *)


(* recursive functions *)


(* annotations *)
let an1 = 0 { result = 0 }
let an2 = { v4 >= 0 } begin v4 := !v4 + 1 end { v4 > v4@ }
let an3 = { v4 >= 0 } begin v4 := !v4 + 1 end { v4 > v4@init }
