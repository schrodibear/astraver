val (>=): int -> int -> bool
val (>): int -> int -> bool
val (<=): int -> int -> bool
val (<): int -> int -> bool

val (=): 'a -> 'a -> bool
val (<>): 'a -> 'a -> bool

val (&&): bool -> bool -> bool

val ( * ): int -> int -> int
val (/): int -> int -> int
val (+): int -> int -> int
val (-): int -> int -> int

module Array: sig
  val make: int -> 'a -> 'a array
  val get: 'a array -> int -> 'a
  val set: 'a array -> int -> 'a -> unit
end
