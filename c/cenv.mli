
open Cast
open Info

(* Typing environments. They are common to both code and annotations. *)

val eq_type : tctype -> tctype -> bool
val eq_type_node : 'a ctype_node -> 'b ctype_node -> bool
val sub_type : 'a ctype -> 'b ctype -> bool
val arith_type : 'a ctype -> bool
val array_type : 'a ctype -> bool
val pointer_type : 'a ctype -> bool
val pointer_or_array_type : 'a ctype -> bool
val is_null : texpr -> bool

(* Global environment *)
val add_sym : Loc.t -> string -> tctype -> unit
val find_sym : string -> tctype * var_info

val add_typedef : Loc.t -> string -> tctype -> unit
val find_typedef : string -> tctype

val add_tag_type : Loc.t -> string -> tctype -> unit
val find_tag_type : string -> tctype

(* Logic environment *)
val add_fun : string -> tctype list * tctype -> unit
val find_fun : string -> tctype list * tctype

val add_pred : string -> tctype list -> unit
val find_pred : string -> tctype list

(* Local environment *)
module Env : sig

  type t

  val empty : t
  val add : string -> tctype -> var_info -> t -> t
  val find : string -> t -> tctype * var_info

  val add_tag_type : Loc.t -> string -> tctype -> t -> t
  val find_tag_type : string -> t -> tctype

end

val type_of_struct_field : Loc.t -> string -> texpr field list -> tctype
val type_of_union_field : Loc.t -> string -> texpr field list -> tctype

