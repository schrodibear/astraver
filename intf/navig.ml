
module type Tree = sig

  type t (* type of trees *)

  val down : t -> t
  val up : t -> t
  val left : t -> t
  val right : t -> t

  type info
  val info : t -> info
  val show_info : info -> unit

end

module Make (T : Tree) = struct

  let tree = ref None

  let option_iter f = function
    | None -> ()
    | Some t -> f t

  let update () = option_iter (fun t -> T.show_info (T.info t)) !tree

  let set t = tree := Some t; update ()

  let down () = option_iter (fun t -> set (T.down t)) !tree
  let up () = option_iter (fun t -> set (T.up t)) !tree
  let left () = option_iter (fun t -> set (T.left t)) !tree
  let right () = option_iter (fun t -> set (T.right t)) !tree

end
