
module type Tree = sig

  type t (* type of trees *)

  exception NoMove
  val down : t -> t
  val up : t -> t
  val left : t -> t
  val right : t -> t

  type info
  val info : t -> info
  val show_info : info -> unit

end

module Make (T : Tree) = struct

  open T

  let tree = ref None

  let option_iter f = function
    | None -> ()
    | Some t -> f t

  let update () = option_iter (fun t -> show_info (info t)) !tree

  let set t = tree := Some t; update ()

  let move f () = 
    option_iter (fun t -> try set (f t) with NoMove -> ()) !tree

  let down = move T.down
  let up = move T.up
  let left = move T.left
  let right = move T.right

  let next () = 
    let rec really_right t =
      try set (T.right t) with NoMove -> really_right (T.up t)
    in
    option_iter 
      (fun t -> 
	 try set (T.down t) with NoMove -> 
         try set (T.right t) with NoMove ->
	 try really_right (T.up t) with NoMove -> ()) 
      !tree

end
