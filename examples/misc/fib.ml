
(** Various implementations of the Fibonacci function. 
    All the following programs have the same specification

       n:int -> { n >= 0 } int { result = F(n) }

    where F is the Fibonacci function defined on the logical side
    (with F(0) = F(1) = 1 and F(n+2) = F(n+1) + F(n)) *)

logic F : int -> int

(** Naive and purely functional *)

let rec fib1 (n:int) : int { variant n } = 
  { n >= 0 }
  (if n <= 1 then
     1
   else 
     (fib1 (n - 1)) + (fib1 (n - 2)))
  { result = F(n) }

(** Still purely functional, but efficient *)

let rec fib2_aux (n:int) (x:int) (fx:int) (fx_1:int) : int { variant n-x } =
  { 1 <= x <= n and fx = F(x) and fx_1 = F(x-1) }
  (if x = n then
     fx 
   else 
     (fib2_aux n (x+1) (fx+fx_1) fx))
  { result = F(n) }

let fib2 = fun (n:int) ->
  { n >= 0 }
  (if n <= 1 then 1 else (fib2_aux n 1 1 1))
  { result = F(n) }

(** Imperative *)

let fib3 (n:int) =
 { n >= 0 }
 (let k = ref 1 in
  let x = ref 1 in
  let y = ref 1 in
  begin
    if n > 0 then
    while !k < n do
      { invariant 1 <= k <= n and x = F(k) and y = F(k-1)  variant n - k }
      let t = !y in
      begin
        y := !x;
        x := !x + t;
	k := !k + 1
      end
    done;
    !x
  end)
 { result = F(n) }

(** Imperative, in an array *)

parameter N : int

parameter t : array N of int

let fib4 (n:int) =
  { 0 <= n < N }
  (if n <= 1 then
     1
   else begin
     t[0] := 1;
     t[1] := 1;
     let k = ref 2 in
     while !k <= n do
       { invariant 2 <= k <= n+1 and forall i:int. 0 <= i < k -> t[i] = F(i)  
         variant n+1 - k }
       t[!k] := t[!k - 1] + t[!k - 2];
       k := !k + 1
     done;
     t[n]
   end)
  { result = F(n) }
