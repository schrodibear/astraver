
open Cast
open Info

(* Typing environments. They are common to both code and annotations. *)

val eq_type : tctype -> tctype -> bool
val eq_type_node : 'a ctype_node -> 'b ctype_node -> bool
val sub_type : 'a ctype -> 'b ctype -> bool
val compatible_type : 'a ctype -> 'b ctype -> bool
val arith_type : 'a ctype -> bool
val array_type : 'a ctype -> bool
val pointer_type : 'a ctype -> bool
val pointer_or_array_type : 'a ctype -> bool
val is_null : texpr -> bool

(* Global environment *)
val add_sym : Loc.t -> string -> tctype -> var_info -> var_info
val find_sym : string -> tctype * var_info

val add_typedef : Loc.t -> string -> tctype -> unit
val find_typedef : string -> tctype

(* Logic environment *)
val add_fun : string -> tctype list * tctype * Info.logic_info -> unit
val find_fun : string -> tctype list * tctype * Info.logic_info

val add_pred : string -> tctype list * Info.logic_info -> unit
val find_pred : string -> tctype list * Info.logic_info 

(* tag types *)
type tag_type_definition = Incomplete | Defined of texpr ctype_node
val tag_type_definition : string -> tag_type_definition

(* Local environment *)
module Env : sig

  type t

  val empty : unit -> t

  val new_block : t -> t

  val add : string -> tctype -> var_info -> t -> t
  val find : string -> t -> tctype * var_info
  val mem : string -> t -> bool

  val find_tag_type : Loc.t -> t -> texpr ctype_node -> texpr ctype_node

end

val type_of_field : Loc.t -> string -> tctype -> field_info * tctype
val find_field : tag:string -> field:string -> field_info
val declare_fields : texpr ctype_node -> ('a * string * 'b) list -> unit

(* make heap var names unique *)
(*
val uniquize_names : unit -> unit
*)
