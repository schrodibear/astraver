
open Ctypes
open Info

(* Typing environments. They are common to both code and annotations. *)

val eq_type : ctype -> ctype -> bool
val eq_type_node : ctype_node -> ctype_node -> bool
val sub_type : ctype -> ctype -> bool
val compatible_type : ctype -> ctype -> bool
val arith_type : ctype -> bool
val array_type : ctype -> bool
val pointer_type : ctype -> bool
val pointer_or_array_type : ctype -> bool



(* Global environment *)

val add_sym : Loc.t -> string -> ctype -> env_info -> env_info
val find_sym : string -> env_info

val add_typedef : Loc.t -> string -> ctype -> unit
val find_typedef : string -> ctype

(* Logic environment *)
val add_fun : string -> ctype list * ctype * Info.logic_info -> unit
val find_fun : string -> ctype list * ctype * Info.logic_info

val add_pred : string -> ctype list * Info.logic_info -> unit
val find_pred : string -> ctype list * Info.logic_info 

(* tag types *)
type tag_type_definition = 
  | TTIncomplete 
  | TTStructUnion of ctype_node * (ctype * string) list
  | TTEnum of ctype_node * (string * int64) list
val tag_type_definition : string -> tag_type_definition

(* Local environment *)
module Env : sig

  type t

  val empty : unit -> t

  val new_block : t -> t

  val add : string -> ctype -> env_info -> t -> t
  val find : string -> t -> env_info
  val mem : string -> t -> bool

  val find_tag_type : Loc.t -> t -> ctype_node -> ctype_node
  val set_struct_union_type : Loc.t -> t -> ctype_node -> 
    (ctype * string) list -> ctype_node
  val set_enum_type : Loc.t -> t -> ctype_node -> 
    (string * int64) list -> ctype_node
end

val type_of_field : Loc.t -> string -> ctype -> var_info 
val find_field : tag:string -> field:string -> var_info
val declare_fields : ctype_node -> (ctype * string ) list -> unit

