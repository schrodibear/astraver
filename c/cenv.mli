
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


(* for type why*)
val type_type_why : ?name:string -> Ctypes.ctype -> bool -> why_type 
val set_var_type : env_info -> Ctypes.ctype -> bool -> unit
val zone_table : (string,Info.zone) Hashtbl.t
val make_zone :  ?name:string -> bool -> zone

(* Global environment *)

val add_sym : Loc.position -> string -> ctype -> env_info -> env_info
val find_sym : string -> env_info
val iter_sym : (Lib.Sset.elt -> Info.env_info -> unit) -> unit
val add_typedef : Loc.position -> string -> ctype -> unit
val find_typedef : string -> ctype

(* Logic environment *)
val add_type : string -> unit
val mem_type : string -> bool
val iter_types : (string -> unit) -> unit

val add_fun : string -> ctype list * ctype * Info.logic_info -> unit
val find_fun : string -> ctype list * ctype * Info.logic_info

val add_pred : string -> ctype list * Info.logic_info -> unit
val mem_pred : string -> bool 
val find_pred : string -> ctype list * Info.logic_info 

val add_ghost : Loc.position -> string -> ctype -> var_info -> var_info
val find_ghost : string -> var_info

(* tag types *)
type tag_type_definition = 
  | TTIncomplete 
  | TTStructUnion of ctype_node * var_info list
  | TTEnum of ctype_node * (var_info * int64) list
val tag_type_definition : string -> tag_type_definition

(* iterates over all declared structures *)
val iter_all_struct : (string -> ctype_node * var_info list -> unit) -> unit
val fold_all_struct : 
  (string -> ctype_node * var_info list -> 'a -> 'a) -> 'a -> 'a

(* iterates over all pairs of structures (the pairs (a,b) and (b,a) are
   identified) *)
val fold_all_struct_pairs :
  (string -> ctype_node * var_info list ->
   string -> ctype_node * var_info list -> 'a -> 'a) -> 'a -> 'a

(* Local environment *)
module Env : sig

  type t

  val empty : unit -> t

  val new_block : t -> t

  val add : string -> ctype -> env_info -> t -> t
  val find : string -> t -> env_info
  val mem : string -> t -> bool

  val find_tag_type : Loc.position -> t -> ctype_node -> ctype_node
  val set_struct_union_type : Loc.position -> t -> ctype_node -> 
    (var_info) list -> ctype_node
  val set_enum_type : Loc.position -> t -> ctype_node -> 
    (var_info * int64) list -> ctype_node
end

val type_of_field : Loc.position -> string -> ctype -> var_info 
val find_field : tag:string -> field:string -> var_info
val declare_fields : ctype_node -> (ctype * var_info) list -> unit

(* for normalization of fields types *)
val update_fields_type : unit -> unit

