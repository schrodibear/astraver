open Ml_misc
open Jc_env
open Jc_fenv

exception Not_found_str of string

module IdentMap = Map.Make(
  struct
    type t = Ml_ocaml.Ident.t
    let compare x y = String.compare (Ml_ocaml.Ident.unique_name x)
      (Ml_ocaml.Ident.unique_name y)
  end)

type t = {
  vars: Jc_env.var_info StringMap.t;
  funs: Jc_fenv.fun_info StringMap.t;
  fields: Jc_env.field_info StringMap.t;
  structs: Jc_env.struct_info StringMap.t;
  fun_specs: Ml_ocaml.Typedtree.function_spec IdentMap.t;
  type_specs: Ml_ocaml.Typedtree.type_spec IdentMap.t;
}

let empty = {
  vars = StringMap.empty;
  funs = StringMap.empty;
  fields = StringMap.empty;
  structs = StringMap.empty;
  fun_specs = IdentMap.empty;
  type_specs = IdentMap.empty;
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
  { env with vars = StringMap.add name vi env.vars }, vi

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

let add_field name ty si env =
  let fi = {
    jc_field_info_tag = fresh_int ();
    jc_field_info_name = name;
    jc_field_info_final_name = name;
    jc_field_info_type = ty;
    jc_field_info_struct = si;
    jc_field_info_root = si.jc_struct_info_root;
    jc_field_info_rep = false;
  } in
  { env with fields = StringMap.add name fi env.fields }, fi

let add_struct si env =
  { env with structs = StringMap.add si.jc_struct_info_name si env.structs }

let add_fun_spec id spec env =
  { env with fun_specs = IdentMap.add id spec env.fun_specs }

let add_type_spec id spec env =
  { env with type_specs = IdentMap.add id spec env.type_specs }

let nf s f k m =
  try
    f k m
  with Not_found ->
    raise (Not_found_str s)

let find_var name env = nf name StringMap.find name env.vars
let find_fun name env = nf name StringMap.find name env.funs
let find_field name env = nf name StringMap.find name env.fields
let find_struct name env = nf name StringMap.find name env.structs
let find_fun_spec id env =
  nf (Ml_ocaml.Ident.name id) IdentMap.find id env.fun_specs
let find_type_spec id env =
  nf (Ml_ocaml.Ident.name id) IdentMap.find id env.type_specs

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/jessica.byte"
End: 
*)
