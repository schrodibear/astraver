(* explanations *)

val raw_loc : ?pref:string -> Format.formatter -> Loc.floc -> unit
val print: Format.formatter -> Logic_decl.vc_expl -> unit

