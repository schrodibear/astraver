
(* Test program *)


let rec f (x:int) (y:int) : bool { variant phi(x) } = (f x y)

(***
	let res = ref false in
	let test = ref (compareTo (access_contenu this) c) in
	begin
	if !test = 0 then res := true
	else 
	   if !test > 0 then
		res := (has (access_gauche this) c)
	    else 
		res := (has (access_droit this) c);
	!res
	end    
***)
   
