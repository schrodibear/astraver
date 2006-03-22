
val desactivate : unit -> unit
val activate : unit -> unit
val swap_active : unit -> unit
val is_active : unit -> bool

val reset_last_file : unit -> unit

val text_of_obligation :
  GText.view -> GText.view ->
  'a * string * (Cc.context_element list * Logic.predicate) -> unit
