




type var_info =
    {
      var_name : string;
      mutable var_is_assigned : bool;
    }

val default_var_info : string -> var_info
