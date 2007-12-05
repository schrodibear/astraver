open Ml_misc
open Jc_env
open Jc_fenv

type t = {
  vars: Jc_env.var_info StringMap.t;
  funs: Jc_fenv.fun_info StringMap.t;
}

let empty = {
  vars = StringMap.empty;
  funs = StringMap.empty;
}

let add_var name ty env =
  let vi = {
    jc_var_info_tag = fresh_int ();
    jc_var_info_name = name;
    jc_var_info_final_name = name; (* ? *)
    jc_var_info_type = ty;
    jc_var_info_formal = false; (* ? *)
    jc_var_info_assigned = false; (* ? *)
    jc_var_info_static = false; (* ? *)
  } in
  { env with vars = StringMap.add name vi env.vars }

let add_fun name params return_type env =
  let fi = {
    jc_fun_info_tag = fresh_int ();
    jc_fun_info_name = name;
    jc_fun_info_final_name = name; (* ? *)
    jc_fun_info_return_type = return_type;
    jc_fun_info_parameters = params;
    jc_fun_info_calls = []; (* ? *)
    jc_fun_info_logic_apps = []; (* ? *)
    jc_fun_info_effects = Jc_pervasives.empty_fun_effect; (* ! *)
  } in
  { env with funs = StringMap.add name fi env.funs }

let find_var name env = StringMap.find name env.vars
let find_fun name env = StringMap.find name env.funs

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)

