

val interp_type : Cast.tctype -> string

module HeapVarSet : Set.S with type elt = string * Output.base_type

type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

val location : Cast.tterm Clogic.location -> HeapVarSet.t

val locations : Cast.tterm Clogic.location list -> HeapVarSet.t

val file : Cast.tfile -> unit

