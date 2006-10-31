
open Cast

val pop_initializer : Loc.position -> Cast.tctype ->
    Cast.texpr Cast.c_initializer list ->
    tterm * Cast.texpr Cast.c_initializer list

val invariants_initially_established_info : Info.fun_info

val add_init : tdecl located list -> tdecl located list

val user_invariants : bool ref
