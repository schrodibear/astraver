
open Env
open Output_ast

val struc : struct_info -> why_decl list -> why_decl list

val root : root_info -> why_decl list -> why_decl list

val alloc :
  arg:(expr, check_size:bool -> expr -> expr, _, [ `Range_0_n | `Singleton ], _, 'a) arg ->
  alloc_class * Region.RegionTable.key -> pointer_class -> 'a

val valid_pre : in_param:bool -> Fenv.effect -> var_info -> assertion

val instanceof_pre : in_param:bool -> Fenv.effect -> var_info -> assertion
