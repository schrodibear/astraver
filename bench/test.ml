
(* Test program *)

parameter x : int ref

let p = x = x

(****
external build_Noeud_value : value -> value -> value -> value

external access_contenu : value -> value

external compareTo : value -> value -> int

let has = fun (this:value) (c : value) ->
	
	let res = ref false in
	let test = ref (compareTo (access_contenu this) c) in
	begin
	if test = 0 then res := true
	else 
	   if test > 0 then
		res := (has (access_gauche this) c)
	    else 
		res := (has (access_droit this) c);
	!res
	end    
    

***)
