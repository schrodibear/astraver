
module type Tree = sig

  type t (* type of trees *)

  (* functions to navigate in the tree; must raise [NoMove] when the move
     is not possible *)
  exception NoMove
  val down : t -> t
  val up : t -> t
  val left : t -> t
  val right : t -> t

  type info
  val info : t -> info
  val show_info : info -> unit

end

module Make (T : Tree) : sig

  val set : T.t -> unit

  val down : unit -> unit
  val up : unit -> unit
  val left : unit -> unit
  val right : unit -> unit

  (* depth-first traversal *)
  val next : unit -> unit

end
