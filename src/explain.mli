(* explanations *)

val raw_loc : ?quote:bool -> ?pref:string -> Format.formatter -> Loc.floc -> unit
val print:  ?quote:bool -> Format.formatter ->  Logic_decl.vc_expl -> unit

