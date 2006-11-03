

type native_type =
  [ `Tunit | `Tboolean | `Tinteger | `Treal ]

type jc_type =
  | JCTnative of native_type
  | JCTlogic of string
  | JCTpointer of string
  | JCTvalidpointer of string * int * int

type logic_info =
    {
      jc_logic_info_name : string;
      jc_logic_info_result_type : jc_type option (*r None for predicates *)
    }

type var_info =
    {
      jc_var_info_name : string;
      jc_var_info_final_name : string;
      jc_var_info_type : jc_type;
      mutable jc_var_info_assigned : bool;
    }

type fun_info =
    {
      jc_fun_info_name : string;
      jc_fun_info_return_type : jc_type;
      jc_fun_info_parameters : var_info list;
    }

type field_info =
    {
      jc_field_info_name : string;
      jc_field_info_type : jc_type;
    }

type exception_info =
    {
      jc_exception_info_name : string;
      jc_exception_info_type : jc_type;
    }
