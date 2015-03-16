
open Format
open Jc_output_ast
open Jc_envset

val constant : formatter -> 'a constant -> unit

val id : formatter -> string -> unit
val uid : formatter -> string -> unit
val int_ty :
  how:[< `Module of bool * bool | `Name | `Theory of bool ] ->
  formatter ->
  ('a range, 'b bit) integer ->
  unit

val enum_ty :
  how:[< `Module of bool | `Name | `Theory ] ->
  formatter ->
  ('a enum, 'b bit) integer -> unit

val modulo : formatter -> bool -> unit

val op :
  formatter ->
  [< `Add
   | `And
   | `Asr
   | `Compl
   | `Div
   | `Eq
   | `Ge
   | `Gt
   | `Le
   | `Lsl
   | `Lsr
   | `Lt
   | `Mod
   | `Mul
   | `Ne
   | `Neg
   | `Neq
   | `Or
   | `Sub
   | `Xor ] ->
  unit

type any_integer =
    Int :
      ('r range, 'b bit) integer ->
      any_integer

module S : Set.S with type elt = any_integer

val func :
  where:[< `Behavior of bool | `Logic ] ->
  bw_ints:S.t -> formatter -> ('a, 'b) func -> unit

val vc_kind : formatter -> vc_kind -> unit

val jc_position : formatter -> Jc_position.t -> unit

val why_label : formatter -> why_label -> unit

val tconstr : formatter -> ('a, 'b) tconstr -> unit

val ltype_hlist : formatter -> 'a ltype_hlist -> unit

val logic_type : formatter -> 'a logic_type -> unit

val term_hlist :
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a term_hlist -> unit

val term :
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a term -> unit

val list :
  (formatter -> 'a -> unit) ->
  sep:('b, 'c, 'd, 'e, 'e, 'b) format6 -> formatter -> 'a list -> unit

val pred :
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> pred -> unit

val triggers :
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> trigger list list -> unit

val why_type :
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a why_type -> unit

val variant :
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> ('a term * string option) option -> unit

val option : ('a -> 'b -> unit) -> 'a -> 'b option -> unit

val any_type :
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> any_why_type -> unit

val expr_hlist :
  safe:bool ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a expr_hlist -> unit

val expr_node :
  safe:bool ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a expr_node -> unit

val expr :
  safe:bool ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a expr -> unit

val any_logic_type : formatter -> any_logic_type -> unit

val logic_arg :
  formatter -> string * any_logic_type -> unit

val goal_kind : formatter -> goal_kind -> unit

val why_id : ?constr:bool -> formatter -> why_id -> unit

type 'kind kind =
  | Theory : [ `Theory ] kind
  | Module : bool -> [ `Module of bool ] kind

val why_decl :
  kind:'a kind ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a why_decl -> unit

val dependency : formatter -> 'a dependency -> unit

val module_dependency :
  formatter -> module_dependency -> unit

val why3_builtin_locals : StringSet.t

val entry :
  consts:StringSet.t -> formatter -> 'a entry -> unit

val file : filename:string -> any_entry list -> unit
