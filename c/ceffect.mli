
module StringSet : Set.S with type elt = string

type effect =
    {
      reads : StringSet.t;
      assigns : StringSet.t;
    }

val location : Cast.tterm Clogic.location -> StringSet.t

val locations : Cast.tterm Clogic.location list -> StringSet.t

val file : Cast.tfile -> unit

