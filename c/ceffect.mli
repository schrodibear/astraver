
val interp_type : Cast.tctype -> string

open Info

type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

(* all heap vars and their associated types *)
val heap_vars : (string, Output.base_type) Hashtbl.t
val print_heap_vars : Format.formatter -> unit -> unit

val heap_var_type : string -> Output.base_type

val location : Cast.tterm Clogic.location -> HeapVarSet.t

val locations : Cast.tterm Clogic.location list -> HeapVarSet.t

val predicate : Cast.predicate -> HeapVarSet.t

(* computes effects for logical symbols only *)
val file : Cast.tfile -> unit

(* computes functions effects; 
   return [true] when fixpoint is reached (no more modification) *)
val functions : Cast.tfile -> bool
