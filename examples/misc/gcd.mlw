
(** Various implementations of the gcd. *)

logic gcd : int,int -> int
logic max : int,int -> int

(** Simple algorithm with difference *)

let gcd1 (a:int) (b:int) =
  { a > 0 and b > 0 }
  (let x = ref a in
   let y = ref b in
   begin
     while !x <> !y do
       { invariant 0 < x and 0 < y and gcd(x,y) = gcd(a,b)  variant max(x,y) }
       if !x > !y then
         x := !x - !y
       else 
	 y := !y - !x
     done;
     !x
   end)
  { result = gcd(a,b) }


(** Euclid's algorithm *)

let gcd2 (a:int) (b:int) =
  { a >= 0 and b >= 0 }
  (let x = ref a in
   let y = ref b in
   begin
     while !y <> 0 do
       { invariant 0 <= x and 0 <= y and gcd(x,y) = gcd(a,b)  variant y }
       let r = !x % !y in
       begin
	 x := !y;
	 y := r
       end
     done;
     !x
   end)
  { result = gcd(a,b) }

