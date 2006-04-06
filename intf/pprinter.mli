
val desactivate : unit -> unit
val activate : unit -> unit
val swap_active : unit -> unit
val is_active : unit -> bool

val set_tvsource : GText.view -> unit

val reset_last_file : unit -> unit

val read_file : Tags.loc option -> unit
val move_to_source : Tags.loc option -> unit

val text_of_obligation :
  GText.view -> 'a * string * (Cc.context_element list * Logic.predicate) Env.scheme -> unit
