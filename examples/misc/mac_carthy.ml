
(**** McCarthy's ``91'' function. *)

logic max : int,int -> int

let rec f91 (n:int) : int { variant max(0,101-n) } =
  (if n <= 100 then
     (f91 (f91 (n + 11)))
   else
     n - 10)
  { (n <= 100 and result = 91) or (n >= 101 and result = n - 10) }
