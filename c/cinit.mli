
open Cast

val pop_initializer : Loc.t -> Cast.tctype ->
    Cast.texpr Cast.c_initializer list ->
    Cast.texpr * Cast.texpr Cast.c_initializer list

val invariants_initially_established_info : Info.fun_info

val add_init : tdecl located list -> tdecl located list

