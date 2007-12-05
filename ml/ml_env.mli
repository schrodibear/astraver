type t

val empty: t

val add_var: string -> Jc_env.jc_type -> t -> t
val add_fun: string -> Jc_env.var_info list -> Jc_env.jc_type -> t -> t

val find_var: string -> t -> Jc_env.var_info
val find_fun: string -> t -> Jc_fenv.fun_info
