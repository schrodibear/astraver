
(* realing-point intervals *)

(* [split ol] extracts realing-point obligations (predicate `fpi') from a 
   list of obligations and return the remaining ones *)
val split : Vcg.obligation list -> Vcg.obligation list

(* [output f] outputs the current realing-point obligations in file [f] *)
val output : string -> unit 

(* clear the current set of obligations *)
val reset : unit -> unit
