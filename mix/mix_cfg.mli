
(* From assembly to a set of purely sequential programs *)

module type INPUT = sig
  
  module Label : sig
    type t
    val create : unit -> t
    val equal : t -> t -> bool
    val hash : t -> int
    val to_string : t -> string
  end

  type predicate
    
  val ptrue : predicate

  val string_of_predicate : predicate -> string

  type statement
    
  val void_stmt : statement

  val append_stmt : statement -> statement -> statement

  val assert_stmt : predicate -> statement

  val string_of_stmt : statement -> string
    
end


module Make(X : INPUT) : sig

  type asm =
    | Ainvariant of X.predicate
    | Ajump of X.Label.t
    | Acond of X.Label.t * X.statement * X.statement
    | Ahalt
    | Aother of X.statement

  type asm_code = (X.Label.t option * asm) list
  
  type seq =
    | Sassert of X.predicate
    | Sstmt of X.statement

  type seq_code = {
    seq_pre : X.predicate option;
    seq_code : seq list;
  }

  val transform : asm_code -> X.Label.t -> seq_code list

end


