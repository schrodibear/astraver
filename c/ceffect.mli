
val interp_type : Cast.tctype -> string

open Info

type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

(* all heap vars and their associated types *)
val heap_vars : (string, Output.base_type) Hashtbl.t

val heap_var_type : string -> Output.base_type

val location : Cast.tterm Clogic.location -> HeapVarSet.t

val locations : Cast.tterm Clogic.location list -> HeapVarSet.t

val predicate : Cast.predicate -> HeapVarSet.t

val file : Cast.tfile -> unit

