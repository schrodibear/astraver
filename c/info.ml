




type var_info =
    {
      var_name : string;
      mutable var_is_assigned : bool;
    }

let default_var_info x =
  { var_name = x; 
    var_is_assigned = false }

