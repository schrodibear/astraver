
open Format

exception Error of (Loc.t option) * Cerror.t

val report : formatter -> Cerror.t -> unit

val raise_located : Loc.t -> Cerror.t -> 'a 
val raise_unlocated : Cerror.t -> 'a
val raise_locop : Loc.t option -> Cerror.t -> 'a

