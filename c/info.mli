
module HeapVarSet : Set.S with type elt = string

type var_info =
    {
      var_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_static : bool;
      mutable function_reads : HeapVarSet.t;
      mutable function_writes : HeapVarSet.t;
    }

val default_var_info : string -> var_info

type logic_info =
    {
      logic_name : string;
      mutable logic_args : HeapVarSet.t;
    }

val default_logic_info : string -> logic_info

