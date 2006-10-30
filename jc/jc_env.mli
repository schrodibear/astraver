

type jc_type =
  | JCTlogic of string
  | JCTpointer of jc_type
  | JCTvalidpointer of jc_type * int * int

type logic_info =
    {
      jc_logic_info_name : string;
      jc_logic_info_result_type : jc_type option (*r None for predicates *)
    }

type var_info =
    {
      jc_var_info_name : string;
      jc_var_info_type : jc_type;
    }

type fun_info =
    {
      jc_function_info_name : string;
      jc_function_info_return_type : jc_type;
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
