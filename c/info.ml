




type var_info =
    {
      var_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_static : bool;
    }

let default_var_info x =
  { var_name = x; 
    var_is_assigned = false;
    var_is_static = false;
  }

type logic_info =
    {
      logic_name : string;
      mutable logic_args : string list;
    }

let default_logic_info x =
  { logic_name = x;
    logic_args = [] }

