
(** Dijkstra's "Dutch national flag" *)

external blue : color
external white : color
external red : color

external eq_blue  : c:color -> {} bool { if result then c=blue else c<>blue }
external eq_white : c:color -> {} bool { if result then c=white else c<>white }

parameter N : int
parameter t : array N of color

logic monochrome : array color, int, int, color -> prop

let dutch_flag = 
  let b = ref 0 in
  let i = ref 0 in
  let r = ref N in
  while !i < !r do
     { invariant 0 <= b <= i and i <= r <= N and
	         monochrome(t,0,b,blue) and 
	         monochrome(t,b,i,white) and 
	         monochrome(t,r,N,red)
       variant r - i }
     if (eq_blue t[!i]) then begin
       let u = t[!b] in begin t[!b] := t[!i]; t[!i] := u end;
       b := !b + 1;
       i := !i + 1
     end else if (eq_white t[!i]) then
       i := !i + 1
     else begin
       r := !r - 1;
       let u = t[!r] in begin t[!r] := t[!i]; t[!i] := u end
     end
  done
  { monochrome(t,0,b,blue) and 
    monochrome(t,b,r,white) and 
    monochrome(t,r,N,red) }
