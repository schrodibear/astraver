
(* Swapping the contents of two variables *)


(* 1. with global variables *)

external x,y : int ref

let swap1 = 
  (let t = !x in begin x := !y; y := t end)
  { x = y@ and y = x@ }

(* different syntax, with begin...end instead of parentheses *)
let swap2 = 
  begin
    let t = !x in
    begin
      x := !y; 
      y := t
    end
  end
  { x = y@ and y = x@ } 


(* 2. with a function *)

let swap3 = fun (x,y : int ref) ->
  (let t = !x in begin x := !y; y := t end)
  { x = y@ and y = x@ }

let test_swap3 =
  let a = ref 1 in
  let b = ref 2 in
  (swap3 a b) { b = 1 }

(* called on the globals x,y *)
let call_swap3 = (swap3 x y)


(* 3. with a function using a global variable *)

external tmp : int ref

let swap4 = fun (x,y : int ref) ->
  begin tmp := !x; x := !y; y := !tmp end
  { x = y@ and y = x@ }

