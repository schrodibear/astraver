
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

module Make (T : Tree) : sig

  val set : T.t -> unit

  val down : unit -> unit
  val up : unit -> unit
  val left : unit -> unit
  val right : unit -> unit

  (* val current_info : unit -> T.info (* raises [Not_found] is not set *) *)

  (* val top : unit -> unit *)

end
