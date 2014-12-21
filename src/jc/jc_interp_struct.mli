
open Env
open Fenv
open Output_ast

val struc : struct_info -> why_decl list -> why_decl list

val root : root_info -> why_decl list -> why_decl list

val alloc :
  arg:(expr, check_size:bool -> expr -> expr, _, [ `Range_0_n | `Singleton ], _, 'a) arg ->
  alloc_class * region -> pointer_class -> 'a

val free : safe:bool -> alloc_class * region -> pointer_class -> expr -> expr

val valid_pre : in_param:bool -> effect -> var_info -> assertion

val instanceof_pre : in_param:bool -> effect -> var_info -> assertion
