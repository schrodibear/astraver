
(*s trees *)

module type Tree = sig

  type t
  val children : t -> t list

  type info
  val info : t -> info
  val show_info : info -> unit

end

(*s trees equipped with navigation functions *)

module type NavTree = sig

  type tree (* type of trees *)
  type t    (* type of navigable trees *)

  val create : tree -> t

  (* functions to navigate in the tree; 
     must raise [NoMove] when the move is not possible *)
  exception NoMove
  val down : t -> t
  val up : t -> t
  val left : t -> t
  val right : t -> t

  type info
  val info : t -> info
  val show_info : info -> unit

end

(*s functor to add navigation fuctions to a tree *)

module MakeNavTree (T : Tree) : 
  NavTree with type tree = T.t and type info = T.info 

(*s functor to build a navigator *)

module MakeNavigator (T : NavTree) : sig

  val set : T.t -> unit

  val down : unit -> unit
  val up : unit -> unit
  val left : unit -> unit
  val right : unit -> unit

  (* depth-first traversal *)
  val next : unit -> unit

end
