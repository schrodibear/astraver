

val interp_type : Cast.tctype -> string

open Info

type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

val location : Cast.tterm Clogic.location -> HeapVarSet.t

val locations : Cast.tterm Clogic.location list -> HeapVarSet.t

val predicate : Cast.predicate -> HeapVarSet.t

val file : Cast.tfile -> unit

