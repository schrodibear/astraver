
open Format
open Output_ast
open Envset

val constant : formatter -> 'a constant -> unit

val id : formatter -> string -> unit
val uid : formatter -> string -> unit
val int_ty :
  how:[< `Module of [< `Abstract | `Bitvector ] * [< `Safe | `Unsafe ]
      | `Name
      | `Theory of [< `Abstract | `Bitvector ] ] ->
  formatter ->
  ('a repr, 'b bit) xintx bounded integer ->
  unit

val enum_ty :
  how:[< `Module of [< `Safe | `Unsafe ] | `Name | `Theory ] ->
  formatter -> 'a enum bounded integer -> unit

val modulo : formatter -> [< `Check | `Modulo ] -> unit

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
      ('r repr, 'b bit) xintx bounded integer ->
      any_integer

module S : Set.S with type elt = any_integer

val func :
  entry:string ->
  where:[< `Behavior of [< `Safe | `Unsafe] | `Logic ] ->
  bw_ints:S.t -> formatter -> ('a, 'b) func -> unit

val vc_kind : formatter -> vc_kind -> unit

val jc_position : formatter -> Position.t -> unit

val why_label : formatter -> why_label -> unit

val tconstr : entry:string -> formatter -> ('a, 'b) tconstr -> unit

val ltype_hlist : entry:string -> formatter -> 'a ltype_hlist -> unit

val logic_type : entry:string -> formatter -> 'a logic_type -> unit

val term_hlist :
  entry:string ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a term_hlist -> unit

val term :
  entry:string ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a term -> unit

val list :
  ?pre:('a, 'b, 'c, 'd, 'd, 'a) format6 ->
  sep:('e, 'f, 'g, 'h, 'h, 'e) format6 ->
  ?post:('i, 'j, 'k, 'l, 'l, 'i) format6 ->
  (Format.formatter -> 'm -> unit) ->
  Format.formatter -> 'm list -> unit

val pred :
  entry:string ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> pred -> unit

val triggers :
  entry:string ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> trigger list list -> unit

val why_type :
  entry:string ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a why_type -> unit

val variant :
  entry:string ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> ('a term * string option) option -> unit

val option : ('a -> 'b -> unit) -> 'a -> 'b option -> unit

val any_type :
  entry:string ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> some_why_type -> unit

val expr_hlist :
  entry:string ->
  safe:[< `Safe | `Unsafe] ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a expr_hlist -> unit

val expr_node :
  entry:string ->
  safe:[< `Safe | `Unsafe] ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a expr_node -> unit

val expr :
  entry:string ->
  safe:[< `Safe | `Unsafe] ->
  bw_ints:S.t ->
  consts:StringSet.t ->
  formatter -> 'a expr -> unit

val any_logic_type : entry:string -> formatter -> some_logic_type -> unit

val logic_arg :
  entry:string -> formatter -> string * some_logic_type -> unit

val goal_kind : formatter -> goal_kind -> unit

val why_id : ?constr:bool -> formatter -> why_id -> unit

type 'kind kind =
  | Theory : [ `Let | `With ] -> [ `Theory of [< `Rec | `Nonrec ] ] kind
  | Module : [ `Safe | `Unsafe ] -> [ `Module of [ `Safe | `Unsafe ] ] kind

val why_decl :
  entry:string ->
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

val file : filename:string -> some_entry list -> unit
