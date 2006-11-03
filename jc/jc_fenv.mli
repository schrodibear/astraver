
(* $Id: jc_fenv.mli,v 1.1 2006-11-03 16:27:07 marche Exp $ *)

open Jc_env
open Jc_envset

type effects =
    {
      jc_writes_fields : FieldSet.t;
    }

type fun_info =
    {
      jc_fun_info_tag : int;
      jc_fun_info_name : string;
      jc_fun_info_return_type : jc_type;
      mutable jc_fun_info_parameters : var_info list;
      mutable jc_fun_info_calls : fun_info list;
      mutable jc_fun_info_logic_apps : logic_info list;
      mutable jc_fun_info_effects : effects;
    }
