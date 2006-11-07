


let map f = function None -> None | Some x -> Some (f x)

let iter f = function None -> () | Some x -> f x

let fold f x c = match x with None -> c | Some x -> f x c 
