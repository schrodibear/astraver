open Cc

val reset : unit -> unit

val push : Logic_decl.t -> unit
val iter : (Logic_decl.t -> unit) -> unit
